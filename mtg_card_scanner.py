"""
MTG Card Scanner - desktop app
==============================
Point your webcam at a Magic: The Gathering card, press SPACE, confirm the
name, and the app looks up its price on Scryfall and adds it to your list.
You can sort and filter your cards (type, color, foil) and export them to a
text file. Everything is saved on your own computer in:

    Documents/MTG Card Scanner/
        cards.json    <- your card list (saved automatically)
        settings.json <- your settings
        Scans/        <- a photo of every card you scanned
        Exports/      <- default place for exported text files

Normal users: just run the installer (MTG-Card-Scanner-Setup.exe). Nothing
else needs to be installed - the app includes its own card-name reader.

Developers can run it from source:
    pip install -r requirements.txt
    python mtg_card_scanner.py
"""

import os
import sys
import json
import time
import datetime
import subprocess
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

import cv2
import numpy as np
import requests
from PIL import Image, ImageTk

# Card-name reader. RapidOCR ships its own models inside the app, so there is
# nothing extra to install. If it can't load, you just type the name instead.
try:
    from rapidocr_onnxruntime import RapidOCR
    HAVE_OCR = True
except Exception:
    HAVE_OCR = False

_OCR_ENGINE = None


def _get_ocr_engine():
    global _OCR_ENGINE
    if _OCR_ENGINE is None:  # load once, on first use (takes a second or two)
        _OCR_ENGINE = RapidOCR()
    return _OCR_ENGINE

# ----------------------------------------------------------------- settings
APP_NAME = "MTG Card Scanner"
DATA_DIR = Path.home() / "Documents" / "MTG Card Scanner"
SCANS_DIR = DATA_DIR / "Scans"
EXPORT_DIR = DATA_DIR / "Exports"
CARDS_FILE = DATA_DIR / "cards.json"
SETTINGS_FILE = DATA_DIR / "settings.json"

PREVIEW_W, PREVIEW_H = 640, 360
RESOLUTIONS = [("1280 x 720", 1280, 720),
               ("1920 x 1080 (sharper)", 1920, 1080),
               ("640 x 480", 640, 480)]
CARD_RATIO = 63 / 88
BOX_HEIGHT_FRACTION = 0.88
HEADERS = {"User-Agent": "MTGCardScannerApp/1.0", "Accept": "application/json"}

SORT_MODES = [
    ("Value: high to low", lambda c: -c["price"]),
    ("Value: low to high", lambda c: c["price"]),
    ("Name: A to Z",       lambda c: c["name"].lower()),
    ("Set: A to Z",        lambda c: (c["set"].lower(), c["name"].lower())),
    ("Scan order",         lambda c: c["scanned_at"]),
]
SORT_FUNCS = dict(SORT_MODES)

TYPE_FILTERS = ["All", "Land", "Creature", "Instant", "Sorcery",
                "Artifact", "Enchantment", "Planeswalker", "Battle"]
COLOR_LETTERS = {"White": "W", "Blue": "U", "Black": "B", "Red": "R", "Green": "G"}
LETTER_NAMES = {v: k for k, v in COLOR_LETTERS.items()}
COLOR_FILTERS = ["All", "White", "Blue", "Black", "Red", "Green",
                 "Multicolor", "Colorless"]


# ------------------------------------------------------------ local storage
def ensure_dirs():
    for d in (DATA_DIR, SCANS_DIR, EXPORT_DIR):
        d.mkdir(parents=True, exist_ok=True)


def load_json(path, default):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return default


def save_json(path, data):
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(data, indent=2), encoding="utf-8")
    os.replace(tmp, path)  # safe write: never leaves a half-written file


def load_cards():
    cards = load_json(CARDS_FILE, [])
    if not isinstance(cards, list):
        cards = []
    for i, c in enumerate(cards):
        c.setdefault("id", f"c{time.time_ns()}{i}")
        c.setdefault("name", "?")
        c.setdefault("set", "?")
        c.setdefault("number", "")
        c.setdefault("rarity", "")
        c.setdefault("type_line", "")
        c.setdefault("colors", [])
        c.setdefault("price_nonfoil", c.get("price", 0.0))
        c.setdefault("price_foil", 0.0)
        c.setdefault("finish", "nonfoil")
        c.setdefault("price", c["price_nonfoil"])
        c.setdefault("scanned_at", 0)
    return cards


def open_folder(path):
    try:
        if sys.platform.startswith("win"):
            os.startfile(str(path))  # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path)])
    except Exception:
        messagebox.showinfo(APP_NAME, f"Your files are in:\n{path}")


# ------------------------------------------------------------ price lookups
def _money(v):
    try:
        return float(v) if v else 0.0
    except (TypeError, ValueError):
        return 0.0


def _card_colors(c):
    cols = c.get("colors")
    if cols is None and c.get("card_faces"):       # double-faced cards
        cols = sorted({x for f in c["card_faces"] for x in (f.get("colors") or [])})
    cols = list(cols or [])
    if not cols and "Land" in c.get("type_line", ""):
        cols = list(c.get("color_identity", []))   # Forest -> G, etc.
    return cols


def _art_url(c):
    uris = c.get("image_uris") or {}
    if not uris and c.get("card_faces"):
        uris = (c["card_faces"][0] or {}).get("image_uris") or {}
    return uris.get("art_crop", "")


def _parse_scryfall(c):
    p = c.get("prices", {})
    return {
        "name": c["name"],
        "set": c.get("set_name", "?"),
        "number": c.get("collector_number", ""),
        "rarity": c.get("rarity", ""),
        "type_line": c.get("type_line", ""),
        "colors": _card_colors(c),
        "art_url": _art_url(c),
        "price_nonfoil": _money(p.get("usd")),
        "price_foil": _money(p.get("usd_foil") or p.get("usd_etched")),
    }


def search_mtg(name):
    """Return a list of candidate printings from Scryfall."""
    r = requests.get(
        "https://api.scryfall.com/cards/search",
        params={"q": f'!"{name}"', "unique": "prints", "order": "released"},
        headers=HEADERS, timeout=10,
    )
    if r.status_code == 404:  # no exact match -> try fuzzy (forgives typos)
        r = requests.get(
            "https://api.scryfall.com/cards/named",
            params={"fuzzy": name}, headers=HEADERS, timeout=10,
        )
        if r.status_code == 200:
            # re-search using the corrected name so we get every printing
            fixed = r.json().get("name", name)
            r2 = requests.get(
                "https://api.scryfall.com/cards/search",
                params={"q": f'!"{fixed}"', "unique": "prints", "order": "released"},
                headers=HEADERS, timeout=10,
            )
            data = r2.json().get("data", []) if r2.status_code == 200 else [r.json()]
        else:
            # last resort: any card whose name contains the words we read
            r3 = requests.get(
                "https://api.scryfall.com/cards/search",
                params={"q": name, "unique": "prints", "order": "released"},
                headers=HEADERS, timeout=10,
            )
            if r3.status_code != 200:
                return []
            data = r3.json().get("data", [])
    else:
        r.raise_for_status()
        data = r.json().get("data", [])
    return [_parse_scryfall(c) for c in data[:15]]


def apply_finish(card, finish):
    card["finish"] = finish
    nf, fo = card["price_nonfoil"], card["price_foil"]
    card["price"] = (fo or nf) if finish == "foil" else (nf or fo)
    return card


# --------------------------------------------------------------------- OCR
def ocr_title(card_img):
    """Returns (guess, note). note explains a failure to the user."""
    if not HAVE_OCR:
        return "", "Automatic name reading isn't available - please type the card name."
    h, w = card_img.shape[:2]
    strip = card_img[int(h * 0.02):int(h * 0.14), int(w * 0.03):int(w * 0.82)]
    strip = cv2.resize(strip, None, fx=2, fy=2, interpolation=cv2.INTER_CUBIC)
    gray = cv2.cvtColor(strip, cv2.COLOR_BGR2GRAY)
    boosted = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(4, 4)).apply(gray)
    sharp = cv2.addWeighted(boosted, 1.6, cv2.GaussianBlur(boosted, (0, 0), 3), -0.6, 0)
    variants = (strip,
                cv2.cvtColor(boosted, cv2.COLOR_GRAY2BGR),
                cv2.cvtColor(sharp, cv2.COLOR_GRAY2BGR))

    # try a few versions of the title strip and keep the most confident read
    best_text, best_score = "", 0.0
    for variant in variants:
        try:
            result, _ = _get_ocr_engine()(variant)
        except Exception:
            continue
        if not result:
            continue
        try:
            score = sum(float(r[2]) for r in result) / len(result)
        except (TypeError, ValueError):
            score = 0.5
        if score > best_score:
            best_text = " ".join(str(r[1]) for r in result)
            best_score = score
    guess = "".join(ch for ch in best_text if ch.isalnum() or ch in " ',-:").strip()
    if not guess:
        return "", "Couldn't read the title - type the card name and press Search."
    return guess, "Check the name below, fix it if needed, then pick the right printing."


# ------------------------------------------------- image quality / artwork
def sharpness_score(img):
    """Bigger = sharper. Drives the live focus check and picks the best frame."""
    g = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    g = cv2.resize(g, (320, max(1, int(g.shape[0] * 320 / g.shape[1]))))
    return float(cv2.Laplacian(g, cv2.CV_64F).var())


def sharpness_label(score):
    if score < 40:
        return "Blurry"
    if score < 120:
        return "OK"
    return "Sharp"


def art_region(card_img):
    h, w = card_img.shape[:2]
    return card_img[int(h * 0.12):int(h * 0.55), int(w * 0.08):int(w * 0.92)]


def _prep_gray(img, width=400):
    g = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY) if img.ndim == 3 else img
    g = cv2.resize(g, (width, max(1, int(g.shape[0] * width / g.shape[1]))))
    return cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8)).apply(g)


def pick_printing_by_art(card_img, matches):
    """Compare the photographed artwork with each printing's artwork on Scryfall.
    Returns (index, score) for a clear winner, or None when it isn't sure."""
    candidates = [(i, m["art_url"]) for i, m in enumerate(matches) if m.get("art_url")]
    if len(candidates) < 2:
        return None
    orb = cv2.ORB_create(nfeatures=1000)
    kq, dq = orb.detectAndCompute(_prep_gray(art_region(card_img)), None)
    if dq is None or len(kq) < 20:
        return None

    def fetch(url):
        try:
            r = requests.get(url, headers=HEADERS, timeout=10)
            r.raise_for_status()
            return r.content
        except requests.RequestException:
            return None

    with ThreadPoolExecutor(max_workers=6) as ex:
        blobs = list(ex.map(fetch, [u for _, u in candidates]))

    bf = cv2.BFMatcher(cv2.NORM_HAMMING)
    scores = []
    for (i, _), blob in zip(candidates, blobs):
        good = 0
        if blob:
            try:
                im = cv2.imdecode(np.frombuffer(blob, np.uint8), cv2.IMREAD_COLOR)
                kt, dt = orb.detectAndCompute(_prep_gray(im), None)
                if dt is not None and len(kt) >= 20:
                    pairs = bf.knnMatch(dq, dt, k=2)
                    good = sum(1 for p in pairs
                               if len(p) == 2 and p[0].distance < 0.75 * p[1].distance)
            except Exception:
                good = 0
        scores.append((good, i))
    scores.sort(reverse=True)
    best, second = scores[0], scores[1]
    if best[0] >= 15 and best[0] >= 1.5 * max(second[0], 1):
        return best[1], best[0]
    return None


# ------------------------------------------------------- filtering/sorting
def matches_type(card, type_filter):
    if type_filter == "All":
        return True
    return type_filter.lower() in card.get("type_line", "").lower()


def matches_color(card, color_filter):
    cols = card.get("colors", [])
    if color_filter == "All":
        return True
    if color_filter == "Multicolor":
        return len(cols) >= 2
    if color_filter == "Colorless":
        return len(cols) == 0
    return COLOR_LETTERS[color_filter] in cols


def get_view(cards, sort_name, type_filter, color_filter):
    rows = [c for c in cards
            if matches_type(c, type_filter) and matches_color(c, color_filter)]
    return sorted(rows, key=SORT_FUNCS[sort_name])


def color_text(card):
    cols = card.get("colors", [])
    if not cols:
        return "Colorless"
    return "/".join(LETTER_NAMES[x] for x in cols if x in LETTER_NAMES)


def main_type(card):
    left = card.get("type_line", "").split("//")[0].split("\u2014")[0]
    for t in TYPE_FILTERS[1:]:
        if t.lower() in left.lower():
            return t
    return left.strip() or "?"


def finish_text(card):
    return "Foil" if card["finish"] == "foil" else "Non-foil"


def write_export(path, rows, header_lines):
    total = sum(c["price"] for c in rows)
    name_w = max([len(c["name"]) for c in rows] + [4])
    set_w = max([len(c["set"]) for c in rows] + [3])
    type_w = max([len(main_type(c)) for c in rows] + [4])
    col_w = max([len(color_text(c)) for c in rows] + [5])
    line_w = name_w + set_w + type_w + col_w + 38

    with open(path, "w", encoding="utf-8") as f:
        f.write("MTG card collection export\n")
        for h in header_lines:
            f.write(h + "\n")
        f.write("=" * line_w + "\n")
        f.write(f"{'#':>3}  {'Name':<{name_w}}  {'Type':<{type_w}}  "
                f"{'Color':<{col_w}}  {'Set':<{set_w}}  {'Finish':<8} {'Value':>9}\n")
        f.write("-" * line_w + "\n")
        for i, c in enumerate(rows, 1):
            val = f"${c['price']:,.2f}" if c["price"] else "n/a"
            f.write(f"{i:>3}  {c['name']:<{name_w}}  {main_type(c):<{type_w}}  "
                    f"{color_text(c):<{col_w}}  {c['set']:<{set_w}}  "
                    f"{finish_text(c):<8} {val:>9}\n")
        f.write("-" * line_w + "\n")
        f.write(f"{len(rows)} cards, total value ${total:,.2f}\n")


# ------------------------------------------------------------ camera guide
def card_box(frame):
    h, w = frame.shape[:2]
    bh = int(h * BOX_HEIGHT_FRACTION)
    bw = int(bh * CARD_RATIO)
    x1, y1 = (w - bw) // 2, (h - bh) // 2
    return x1, y1, x1 + bw, y1 + bh


def draw_guide(img):
    """Dim outside the box, draw the box, corner brackets and scan line."""
    h, w = img.shape[:2]
    x1, y1, x2, y2 = card_box(img)
    img[:y1, :] = (img[:y1, :] * 0.4).astype("uint8")
    img[y2:, :] = (img[y2:, :] * 0.4).astype("uint8")
    img[y1:y2, :x1] = (img[y1:y2, :x1] * 0.4).astype("uint8")
    img[y1:y2, x2:] = (img[y1:y2, x2:] * 0.4).astype("uint8")

    cv2.rectangle(img, (x1, y1), (x2, y2), (0, 255, 0), 2)
    L = 26
    for (cx, cy, dx, dy) in [(x1, y1, 1, 1), (x2, y1, -1, 1),
                             (x1, y2, 1, -1), (x2, y2, -1, -1)]:
        cv2.line(img, (cx, cy), (cx + dx * L, cy), (0, 255, 255), 4)
        cv2.line(img, (cx, cy), (cx, cy + dy * L), (0, 255, 255), 4)

    t = (time.time() * 0.8) % 2
    frac = t if t <= 1 else 2 - t
    ly = int(y1 + frac * (y2 - y1))
    cv2.line(img, (x1 + 4, ly), (x2 - 4, ly), (0, 0, 255), 2)
    return img


# ------------------------------------------------------------ add-card popup
class AddCardDialog(tk.Toplevel):
    """Shown after a snap: confirm the name, pick the printing, set finish."""

    def __init__(self, parent, card_img, guess, note, finish):
        super().__init__(parent)
        self.title("Add card")
        self.transient(parent)
        self.resizable(False, False)
        self.result = None
        self.matches = []
        self.name_var = tk.StringVar(value=guess)
        self.finish_var = tk.StringVar(value=finish)
        self.value_var = tk.StringVar()
        self.msg_var = tk.StringVar(value=note)
        self.card_img = card_img
        pad = {"padx": 8, "pady": 4}

        pil = Image.fromarray(cv2.cvtColor(card_img, cv2.COLOR_BGR2RGB))
        pil.thumbnail((190, 270))
        self._thumb = ImageTk.PhotoImage(pil)
        ttk.Label(self, image=self._thumb).grid(
            row=0, column=0, rowspan=6, sticky="n", padx=10, pady=10)

        ttk.Label(self, text="Card name:").grid(row=0, column=1, sticky="w", **pad)
        self.entry = ttk.Entry(self, textvariable=self.name_var, width=34)
        self.entry.grid(row=0, column=2, sticky="ew", **pad)
        ttk.Button(self, text="Search", command=self.search).grid(row=0, column=3, **pad)
        ttk.Label(self, textvariable=self.msg_var, foreground="#555555",
                  wraplength=470, justify="left").grid(
            row=1, column=1, columnspan=3, sticky="w", **pad)

        cols = [("set", "Set", 190), ("num", "No.", 50), ("rarity", "Rarity", 70),
                ("nonfoil", "Non-foil", 75), ("foil", "Foil", 75)]
        self.tree = ttk.Treeview(self, columns=[c[0] for c in cols],
                                 show="headings", height=8, selectmode="browse")
        for key, text, width in cols:
            self.tree.heading(key, text=text)
            self.tree.column(key, width=width, anchor="w" if key == "set" else "e")
        self.tree.grid(row=2, column=1, columnspan=3, sticky="nsew", **pad)

        fin = ttk.Frame(self)
        fin.grid(row=3, column=1, columnspan=3, sticky="w", **pad)
        ttk.Label(fin, text="This card is:").pack(side="left")
        ttk.Radiobutton(fin, text="Non-foil", value="nonfoil",
                        variable=self.finish_var).pack(side="left", padx=8)
        ttk.Radiobutton(fin, text="Foil", value="foil",
                        variable=self.finish_var).pack(side="left")

        val = ttk.Frame(self)
        val.grid(row=4, column=1, columnspan=3, sticky="w", **pad)
        ttk.Label(val, text="Custom value in $ (optional):").pack(side="left")
        ttk.Entry(val, textvariable=self.value_var, width=10).pack(side="left", padx=8)

        btns = ttk.Frame(self)
        btns.grid(row=5, column=1, columnspan=3, sticky="e", **pad)
        ttk.Button(btns, text="Cancel", command=self.destroy).pack(side="right", padx=4)
        ttk.Button(btns, text="Add card", command=self.add).pack(side="right", padx=4)

        self.entry.bind("<Return>", lambda e: self.search())
        self.tree.bind("<Double-1>", lambda e: self.add())
        self.bind("<Escape>", lambda e: self.destroy())

        self.update_idletasks()
        try:  # center over the main window
            x = parent.winfo_rootx() + (parent.winfo_width() - self.winfo_width()) // 2
            y = parent.winfo_rooty() + (parent.winfo_height() - self.winfo_height()) // 2
            self.geometry(f"+{max(x, 0)}+{max(y, 0)}")
            self.wait_visibility()
            self.grab_set()
        except tk.TclError:
            pass
        self.entry.focus_set()
        self.entry.icursor("end")
        if guess:
            self.after(150, self.search)

    def search(self):
        name = self.name_var.get().strip()
        if not name:
            return
        self.msg_var.set("Searching...")
        self.update_idletasks()
        try:
            self.matches = search_mtg(name)
        except (requests.RequestException, ValueError):
            self.matches = []
            self.msg_var.set("Couldn't reach Scryfall - check your internet connection. "
                             "You can still add the card with a custom value below.")
            self._fill([])
            return
        self._fill(self.matches)
        if self.matches:
            msg = f"Found {len(self.matches)} printing(s). Pick the one you have."
            if len(self.matches) > 1:
                self.msg_var.set(f"Found {len(self.matches)} printings - comparing artwork...")
                self.update_idletasks()
                try:
                    hit = pick_printing_by_art(self.card_img, self.matches)
                except Exception:
                    hit = None
                if hit:
                    idx = hit[0]
                    self.tree.selection_set(str(idx))
                    self.tree.focus(str(idx))
                    self.tree.see(str(idx))
                    m = self.matches[idx]
                    msg = (f"Found {len(self.matches)} printings. The artwork looks most like "
                           f"{m['set']} #{m['number']} - check that it matches your card.")
            self.msg_var.set(msg)
        else:
            self.msg_var.set("No match - check the spelling and search again, "
                             "or add it with a custom value below.")

    def _fill(self, matches):
        self.tree.delete(*self.tree.get_children())
        for i, m in enumerate(matches):
            nf = f"${m['price_nonfoil']:,.2f}" if m["price_nonfoil"] else "n/a"
            fo = f"${m['price_foil']:,.2f}" if m["price_foil"] else "n/a"
            self.tree.insert("", "end", iid=str(i),
                             values=(m["set"], m["number"], m["rarity"], nf, fo))
        if matches:
            self.tree.selection_set("0")
            self.tree.focus("0")

    def add(self):
        sel = self.tree.selection()
        custom = self.value_var.get().strip().replace("$", "")
        if sel:
            card = dict(self.matches[int(sel[0])])
        else:
            name = self.name_var.get().strip()
            if not name or not custom:
                messagebox.showinfo(APP_NAME, "Search for the card and pick a printing, "
                                    "or type a name and a custom value.", parent=self)
                return
            card = {"name": name, "set": "?", "number": "", "rarity": "",
                    "type_line": "", "colors": [],
                    "price_nonfoil": 0.0, "price_foil": 0.0}
        if custom:
            try:
                v = float(custom)
            except ValueError:
                messagebox.showerror(APP_NAME, "The custom value must be a number, "
                                     "like 2.50", parent=self)
                return
            card["price_nonfoil"] = v
            card["price_foil"] = v
        apply_finish(card, self.finish_var.get())
        self.result = card
        self.destroy()


# ---------------------------------------------------------------- main app
class ScannerApp:
    def __init__(self, root):
        self.root = root
        root.title(APP_NAME)
        ensure_dirs()
        self.settings = load_json(SETTINGS_FILE, {})
        self.cards = load_cards()

        self.finish = tk.StringVar(value=self.settings.get("finish", "nonfoil"))
        self.camera_var = tk.StringVar(value=str(self.settings.get("camera_index", 0)))
        self.type_var = tk.StringVar(value="All")
        self.color_var = tk.StringVar(value="All")
        self.sort_var = tk.StringVar(value=SORT_MODES[0][0])
        self.status_var = tk.StringVar(value=f"Your cards are saved in: {DATA_DIR}")
        self.autofocus = tk.BooleanVar(value=bool(self.settings.get("autofocus", True)))
        self.focus_value = tk.DoubleVar(value=float(self.settings.get("focus", 128)))
        self.res_var = tk.StringVar(value=self.settings.get("resolution", RESOLUTIONS[0][0]))
        self.sharp_var = tk.StringVar(value="Focus check: waiting for camera...")
        self.frame_buffer = deque(maxlen=6)   # recent (sharpness, frame) pairs
        self.frame_count = 0

        self.cap = None
        self.last_frame = None
        self.photo = None
        self.busy = False

        self.build_ui()
        self.open_camera()
        self.refresh_table()
        self.update_preview()
        root.bind("<space>", self.on_space)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.canvas.focus_set()

    # ---------------------------------------------------------------- UI
    def build_ui(self):
        root = self.root
        root.columnconfigure(1, weight=1)
        root.rowconfigure(0, weight=1)
        ttk.Style().configure("Treeview", rowheight=24)

        # ---- left: camera
        left = ttk.Frame(root, padding=10)
        left.grid(row=0, column=0, sticky="n")
        self.canvas = tk.Canvas(left, width=PREVIEW_W, height=PREVIEW_H,
                                bg="black", highlightthickness=0)
        self.canvas.pack()
        self.img_item = self.canvas.create_image(PREVIEW_W // 2, PREVIEW_H // 2)
        self.msg_item = self.canvas.create_text(
            PREVIEW_W // 2, PREVIEW_H // 2, text="Starting camera...",
            fill="white", width=PREVIEW_W - 60, justify="center", font=("TkDefaultFont", 12))

        ttk.Button(left, text="Snap card  (Space bar)", command=self.snap,
                   takefocus=0).pack(fill="x", pady=(10, 6), ipady=6)

        fbox = ttk.LabelFrame(left, text="New scans are")
        fbox.pack(fill="x", pady=4)
        ttk.Radiobutton(fbox, text="Non-foil", value="nonfoil", variable=self.finish,
                        command=self.on_finish_change, takefocus=0).pack(side="left", padx=10, pady=4)
        ttk.Radiobutton(fbox, text="Foil", value="foil", variable=self.finish,
                        command=self.on_finish_change, takefocus=0).pack(side="left", padx=10, pady=4)

        cam_box = ttk.LabelFrame(left, text="Camera")
        cam_box.pack(fill="x", pady=4)

        row1 = ttk.Frame(cam_box)
        row1.pack(fill="x", padx=8, pady=(4, 2))
        ttk.Label(row1, text="Camera #").pack(side="left")
        cam = ttk.Combobox(row1, textvariable=self.camera_var, values=["0", "1", "2", "3"],
                           width=3, state="readonly")
        cam.pack(side="left", padx=(4, 12))
        cam.bind("<<ComboboxSelected>>", self.on_camera_change)
        ttk.Label(row1, text="Quality").pack(side="left")
        res = ttk.Combobox(row1, textvariable=self.res_var,
                           values=[r[0] for r in RESOLUTIONS], width=20, state="readonly")
        res.pack(side="left", padx=4)
        res.bind("<<ComboboxSelected>>", self.on_camera_change)

        row2 = ttk.Frame(cam_box)
        row2.pack(fill="x", padx=8, pady=2)
        ttk.Checkbutton(row2, text="Auto-focus", variable=self.autofocus,
                        command=self.on_focus_change, takefocus=0).pack(side="left")
        ttk.Label(row2, text="   Manual focus:").pack(side="left")
        self.focus_scale = ttk.Scale(row2, from_=0, to=255, variable=self.focus_value,
                                     orient="horizontal", length=170)
        self.focus_scale.pack(side="left", padx=4)
        self.focus_scale.bind("<ButtonRelease-1>", lambda e: self.on_focus_change())

        row3 = ttk.Frame(cam_box)
        row3.pack(fill="x", padx=8, pady=(2, 6))
        ttk.Button(row3, text="Camera settings window", command=self.open_driver_settings,
                   takefocus=0).pack(side="left")
        ttk.Label(row3, textvariable=self.sharp_var,
                  font=("TkDefaultFont", 10, "bold")).pack(side="left", padx=10)

        ttk.Label(left, justify="left", foreground="#555555", text=(
            "Tip: hold the card flat, about a hand-span from the camera, with\n"
            "light on it but no glare. Wait for the Focus check to say Sharp,\n"
            "then press Space. The sharpest of the last few frames is used.")
                  ).pack(anchor="w", pady=(6, 0))

        # ---- right: filters, table, buttons
        right = ttk.Frame(root, padding=10)
        right.grid(row=0, column=1, sticky="nsew")
        right.columnconfigure(0, weight=1)
        right.rowconfigure(1, weight=1)

        bar = ttk.Frame(right)
        bar.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        for label, var, values, width in (
                ("Type", self.type_var, TYPE_FILTERS, 12),
                ("Color", self.color_var, COLOR_FILTERS, 11),
                ("Sort by", self.sort_var, [n for n, _ in SORT_MODES], 18)):
            ttk.Label(bar, text=label + ":").pack(side="left", padx=(0, 4))
            cb = ttk.Combobox(bar, textvariable=var, values=values,
                              width=width, state="readonly")
            cb.pack(side="left", padx=(0, 14))
            cb.bind("<<ComboboxSelected>>", self.on_filter_change)

        cols = [("name", "Name", 190, "w"), ("type", "Type", 90, "w"),
                ("color", "Color", 90, "w"), ("set", "Set", 150, "w"),
                ("finish", "Finish", 70, "w"), ("value", "Value", 75, "e")]
        tframe = ttk.Frame(right)
        tframe.grid(row=1, column=0, sticky="nsew")
        tframe.columnconfigure(0, weight=1)
        tframe.rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(tframe, columns=[c[0] for c in cols],
                                 show="headings", selectmode="extended", height=16)
        for key, text, width, anchor in cols:
            self.tree.heading(key, text=text)
            self.tree.column(key, width=width, anchor=anchor)
        sb = ttk.Scrollbar(tframe, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.bind("<<TreeviewSelect>>", lambda e: self.canvas.focus_set())

        self.stats_var = tk.StringVar()
        ttk.Label(right, textvariable=self.stats_var,
                  font=("TkDefaultFont", 10, "bold")).grid(row=2, column=0, sticky="w", pady=6)

        btns = ttk.Frame(right)
        btns.grid(row=3, column=0, sticky="ew")
        for text, cmd in (("Switch foil / non-foil", self.flip_selected),
                          ("Remove selected", self.remove_selected),
                          ("Export this view", self.export_view),
                          ("Export all cards", self.export_all),
                          ("Open my files", lambda: open_folder(DATA_DIR))):
            ttk.Button(btns, text=text, command=cmd, takefocus=0).pack(side="left", padx=(0, 6))

        ttk.Label(root, textvariable=self.status_var, relief="sunken",
                  anchor="w", padding=(6, 2)).grid(row=1, column=0, columnspan=2, sticky="ew")

    # ------------------------------------------------------------ camera
    def open_camera(self):
        if self.cap is not None:
            self.cap.release()
            self.cap = None
        self.last_frame = None
        idx = int(self.camera_var.get())
        cap = cv2.VideoCapture(idx, cv2.CAP_DSHOW) if os.name == "nt" else cv2.VideoCapture(idx)
        if cap is not None and cap.isOpened():
            _, rw, rh = next((r for r in RESOLUTIONS if r[0] == self.res_var.get()),
                             RESOLUTIONS[0])
            cap.set(cv2.CAP_PROP_FOURCC, cv2.VideoWriter_fourcc(*"MJPG"))
            cap.set(cv2.CAP_PROP_FRAME_WIDTH, rw)
            cap.set(cv2.CAP_PROP_FRAME_HEIGHT, rh)
            self.cap = cap
            self.apply_focus()
        else:
            self.cap = None
        self.frame_buffer.clear()

    def update_preview(self):
        try:
            self._update_preview_once()
        except Exception as e:  # keep the preview loop alive
            print("preview error:", e, file=sys.stderr)
        self.root.after(33, self.update_preview)

    def _update_preview_once(self):
        frame = None
        if self.cap is not None:
            ok, f = self.cap.read()
            if ok:
                frame = f
        if frame is None:
            self.last_frame = None
            self.canvas.itemconfig(self.img_item, image="")
            self.canvas.itemconfig(
                self.msg_item, state="normal",
                text="No camera found.\nMake sure it's plugged in and not being used by "
                     "another app, or try a different camera number below.")
            return
        self.last_frame = frame
        self.track_sharpness(frame)
        h, w = frame.shape[:2]
        scale = min(PREVIEW_W / w, PREVIEW_H / h)
        small = cv2.resize(frame, (int(w * scale), int(h * scale)))
        small = draw_guide(small)
        rgb = cv2.cvtColor(small, cv2.COLOR_BGR2RGB)
        self.photo = ImageTk.PhotoImage(Image.fromarray(rgb))
        self.canvas.itemconfig(self.img_item, image=self.photo)
        self.canvas.itemconfig(self.msg_item, state="hidden")

    # ---------------------------------------------------------- handlers
    def on_space(self, event):
        try:
            w = self.root.focus_get()
        except (KeyError, tk.TclError):
            return
        if isinstance(w, (tk.Entry, ttk.Entry, ttk.Combobox, ttk.Spinbox)):
            return
        self.snap()
        return "break"

    def on_finish_change(self):
        self.settings["finish"] = self.finish.get()
        save_json(SETTINGS_FILE, self.settings)
        self.set_status("New scans will be "
                        + ("FOIL" if self.finish.get() == "foil" else "NON-FOIL"))
        self.canvas.focus_set()

    def on_camera_change(self, event=None):
        self.settings["camera_index"] = int(self.camera_var.get())
        self.settings["resolution"] = self.res_var.get()
        save_json(SETTINGS_FILE, self.settings)
        self.open_camera()
        self.canvas.focus_set()

    def apply_focus(self):
        auto = self.autofocus.get()
        self.focus_scale.state(["disabled"] if auto else ["!disabled"])
        if self.cap is None:
            return
        try:  # not every camera supports these; failures are harmless
            self.cap.set(cv2.CAP_PROP_AUTOFOCUS, 1 if auto else 0)
            if not auto:
                self.cap.set(cv2.CAP_PROP_FOCUS, float(self.focus_value.get()))
        except Exception:
            pass

    def on_focus_change(self):
        self.settings["autofocus"] = bool(self.autofocus.get())
        self.settings["focus"] = float(self.focus_value.get())
        save_json(SETTINGS_FILE, self.settings)
        self.apply_focus()
        self.canvas.focus_set()

    def open_driver_settings(self):
        """Opens the camera maker's own settings window (focus, brightness...)."""
        if self.cap is None:
            messagebox.showinfo(APP_NAME, "The camera isn't working yet.")
            return
        try:
            self.cap.set(cv2.CAP_PROP_SETTINGS, 1)
            self.set_status("Opened the camera's own settings window "
                            "(it may appear behind this window).")
        except Exception:
            messagebox.showinfo(APP_NAME, "This camera doesn't offer a settings window.")

    def track_sharpness(self, frame):
        """Score the card area of every frame; show the average every few frames."""
        x1, y1, x2, y2 = card_box(frame)
        score = sharpness_score(frame[y1:y2, x1:x2])
        self.frame_buffer.append((score, frame))
        self.frame_count += 1
        if self.frame_count % 5 == 0:
            avg = sum(s for s, _ in self.frame_buffer) / len(self.frame_buffer)
            self.sharp_var.set(f"Focus check: {sharpness_label(avg)} ({avg:.0f})")

    def on_filter_change(self, event=None):
        self.refresh_table()
        self.canvas.focus_set()

    def set_status(self, msg):
        self.status_var.set(msg)

    # ------------------------------------------------------------- table
    def current_view(self):
        return get_view(self.cards, self.sort_var.get(),
                        self.type_var.get(), self.color_var.get())

    def refresh_table(self, keep_selection=()):
        view = self.current_view()
        self.tree.delete(*self.tree.get_children())
        for c in view:
            self.tree.insert("", "end", iid=c["id"], values=(
                c["name"], main_type(c), color_text(c), c["set"],
                finish_text(c), f"${c['price']:,.2f}"))
        keep = [i for i in keep_selection if self.tree.exists(i)]
        if keep:
            self.tree.selection_set(keep)
        self.stats_var.set(
            f"Showing {len(view)} of {len(self.cards)} cards   |   "
            f"This view: ${sum(c['price'] for c in view):,.2f}   |   "
            f"Whole collection: ${sum(c['price'] for c in self.cards):,.2f}")

    def selected_cards(self):
        ids = set(self.tree.selection())
        return [c for c in self.cards if c["id"] in ids]

    def save_cards(self):
        save_json(CARDS_FILE, self.cards)

    # ---------------------------------------------------------- snapping
    def snap(self):
        if self.busy:
            return
        if self.last_frame is None:
            messagebox.showinfo(APP_NAME, "The camera isn't working yet, so there's "
                                "nothing to snap. Check the camera number.")
            return
        if self.frame_buffer:  # use the sharpest of the last few frames
            frame = max(self.frame_buffer, key=lambda t: t[0])[1].copy()
        else:
            frame = self.last_frame.copy()
        x1, y1, x2, y2 = card_box(frame)
        crop = frame[y1:y2, x1:x2].copy()

        self.busy = True
        try:
            self.set_status("Reading card...")
            self.root.update_idletasks()
            guess, note = ocr_title(crop)
            dlg = AddCardDialog(self.root, crop, guess, note, self.finish.get())
            self.root.wait_window(dlg)
            card = dlg.result
        finally:
            self.busy = False

        if not card:
            self.set_status("Cancelled - nothing added.")
            return

        card["id"] = f"c{time.time_ns()}"
        card["scanned_at"] = time.time()
        try:  # keep a photo of the scan
            safe = "".join(ch for ch in card["name"] if ch.isalnum())[:30] or "card"
            fname = f"{datetime.datetime.now():%Y%m%d_%H%M%S}_{safe}.jpg"
            Image.fromarray(cv2.cvtColor(crop, cv2.COLOR_BGR2RGB)).save(
                SCANS_DIR / fname, quality=90)
            card["image"] = fname
        except OSError:
            card["image"] = ""
        self.cards.append(card)
        self.save_cards()
        self.refresh_table()
        self.set_status(f"Added {card['name']} ({finish_text(card)}) - ${card['price']:,.2f}")

    # ------------------------------------------------------- list actions
    def flip_selected(self):
        sel = self.selected_cards()
        if not sel:
            messagebox.showinfo(APP_NAME, "Click a card in the list first "
                                "(hold Ctrl to pick several).")
            return
        ids = [c["id"] for c in sel]
        for c in sel:
            apply_finish(c, "nonfoil" if c["finish"] == "foil" else "foil")
        self.save_cards()
        self.refresh_table(keep_selection=ids)
        self.set_status(f"Switched {len(sel)} card(s).")

    def remove_selected(self):
        sel = self.selected_cards()
        if not sel:
            messagebox.showinfo(APP_NAME, "Click a card in the list first "
                                "(hold Ctrl to pick several).")
            return
        if not messagebox.askyesno(APP_NAME, f"Remove {len(sel)} card(s) from your list?"):
            return
        ids = {c["id"] for c in sel}
        for c in sel:
            if c.get("image"):
                try:
                    (SCANS_DIR / c["image"]).unlink()
                except OSError:
                    pass
        self.cards = [c for c in self.cards if c["id"] not in ids]
        self.save_cards()
        self.refresh_table()
        self.set_status(f"Removed {len(sel)} card(s).")

    # ------------------------------------------------------------ export
    def _export(self, rows, header_lines, label):
        if not rows:
            messagebox.showinfo(APP_NAME, "There are no cards to export.")
            return
        default = f"mtg_cards_{label}_{datetime.datetime.now():%Y-%m-%d_%H-%M}.txt"
        path = filedialog.asksaveasfilename(
            parent=self.root, title="Save text file", initialdir=str(EXPORT_DIR),
            initialfile=default, defaultextension=".txt",
            filetypes=[("Text file", "*.txt")])
        if not path:
            return
        try:
            write_export(path, rows, header_lines)
        except OSError as e:
            messagebox.showerror(APP_NAME, f"Couldn't save the file:\n{e}")
            return
        self.set_status(f"Saved {len(rows)} cards to {path}")

    def export_view(self):
        self._export(self.current_view(), [
            f"Exported: {datetime.datetime.now():%Y-%m-%d %H:%M}",
            f"Filters: type = {self.type_var.get()}, color = {self.color_var.get()}",
            f"Sorted by: {self.sort_var.get()}"], "view")

    def export_all(self):
        rows = sorted(self.cards, key=SORT_FUNCS[self.sort_var.get()])
        self._export(rows, [
            f"Exported: {datetime.datetime.now():%Y-%m-%d %H:%M}",
            "Filters: none (all cards)",
            f"Sorted by: {self.sort_var.get()}"], "all")

    # -------------------------------------------------------------- close
    def on_close(self):
        if self.cap is not None:
            self.cap.release()
        self.root.destroy()


def main():
    root = tk.Tk()
    ScannerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
