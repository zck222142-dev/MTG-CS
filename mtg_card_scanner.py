"""
MTG Card Scanner - desktop app
==============================
Hold a Magic: The Gathering card up to your webcam (or load a photo of it),
and the app finds the card, straightens it, reads the name, and suggests the
most likely cards with their artwork. Pick the right one, choose the printing,
and it is added to your list with its price from Scryfall.

Everything is saved on your own computer in:

    Documents/MTG Card Scanner/
        cards.json      <- your card list (saved automatically)
        settings.json   <- your settings
        card_names.json <- a cached list of all card names (for suggestions)
        Scans/          <- a photo of every card you scanned
        Exports/        <- default place for exported text files

Normal users: just run the installer (MTG-Card-Scanner-Setup.exe). Nothing
else needs to be installed - the app includes its own card-name reader.

Developers can run it from source:
    pip install -r requirements.txt
    python mtg_card_scanner.py
"""

import datetime
import difflib
import heapq
import io
import json
import os
import queue
import re
import subprocess
import sys
import threading
import time
import unicodedata
from collections import Counter, deque
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
DEBUG_DIR = DATA_DIR / "Debug"
CARDS_FILE = DATA_DIR / "cards.json"
SETTINGS_FILE = DATA_DIR / "settings.json"
NAMES_FILE = DATA_DIR / "card_names.json"

PREVIEW_W, PREVIEW_H = 640, 360
RESOLUTIONS = [("1280 x 720", 1280, 720),
               ("1920 x 1080 (sharper)", 1920, 1080),
               ("640 x 480", 640, 480)]
CARD_W, CARD_H = 630, 880            # size of a straightened card image
CARD_RATIO = 63 / 88                 # width / height of a real card
BOX_HEIGHT_FRACTION = 0.92           # size of the guide frame
HEADERS = {"User-Agent": "MTGCardScannerApp/1.1", "Accept": "application/json"}
API = "https://api.scryfall.com"

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


def write_image(path, img):
    """cv2.imwrite fails on non-English folder names on Windows; this doesn't."""
    ok, buf = cv2.imencode(".jpg", img, [cv2.IMWRITE_JPEG_QUALITY, 92])
    if ok:
        buf.tofile(str(path))


# -------------------------------------------------------------------- theme
C = dict(bg="#13151b", panel="#1b1e27", panel2="#252938", hover="#2f3548",
         line="#313648", text="#e9ebf2", muted="#8f96a8", accent="#6d8bff",
         accent_hi="#8aa2ff", accent_lo="#5671d6", good="#38d996",
         warn="#ffb547", bad="#ff6b6b", gold="#ffd479", stripe="#1f232d")
UI_FONT = "Segoe UI" if os.name == "nt" else "TkDefaultFont"


def F(size=10, weight="normal"):
    return (UI_FONT, size, weight)


def apply_theme(root):
    s = ttk.Style(root)
    try:
        s.theme_use("clam")
    except tk.TclError:
        pass
    root.configure(bg=C["bg"])
    s.configure(".", background=C["bg"], foreground=C["text"], fieldbackground=C["panel2"],
                bordercolor=C["line"], lightcolor=C["bg"], darkcolor=C["bg"],
                troughcolor=C["panel"], focuscolor=C["bg"], font=F(10))

    s.configure("TFrame", background=C["bg"])
    s.configure("Panel.TFrame", background=C["panel"])
    s.configure("TLabel", background=C["bg"], foreground=C["text"])
    s.configure("Panel.TLabel", background=C["panel"], foreground=C["text"])
    s.configure("Muted.TLabel", background=C["bg"], foreground=C["muted"])
    s.configure("PanelMuted.TLabel", background=C["panel"], foreground=C["muted"], font=F(9))
    s.configure("Title.TLabel", font=F(19, "bold"))
    s.configure("Section.TLabel", font=F(10, "bold"))
    s.configure("StatNum.TLabel", background=C["panel"], font=F(17, "bold"))
    s.configure("StatCap.TLabel", background=C["panel"], foreground=C["muted"], font=F(9))

    s.configure("TButton", background=C["panel2"], foreground=C["text"], borderwidth=0,
                focusthickness=0, padding=(14, 9), relief="flat")
    s.map("TButton",
          background=[("disabled", C["panel"]), ("pressed", C["line"]), ("active", C["hover"])],
          foreground=[("disabled", C["muted"])])
    s.configure("Accent.TButton", background=C["accent"], foreground="#ffffff",
                font=F(11, "bold"), padding=(14, 12))
    s.map("Accent.TButton",
          background=[("disabled", C["line"]), ("pressed", C["accent_lo"]),
                      ("active", C["accent_hi"])])
    s.configure("Danger.TButton", foreground=C["bad"])
    s.configure("Link.TButton", background=C["panel"], foreground=C["muted"], padding=(2, 4))
    s.map("Link.TButton", foreground=[("active", C["text"])],
          background=[("active", C["panel"])])

    # segmented toggle (used for Non-foil / Foil)
    s.configure("Seg.Toolbutton", background=C["panel2"], foreground=C["muted"],
                padding=(20, 8), borderwidth=0, relief="flat", anchor="center")
    s.map("Seg.Toolbutton",
          background=[("selected", C["accent"]), ("active", C["hover"])],
          foreground=[("selected", "#ffffff"), ("active", C["text"])])

    for w in ("TCheckbutton", "TRadiobutton"):
        s.configure(w, background=C["panel"], foreground=C["text"],
                    indicatorbackground=C["panel2"], indicatorcolor=C["panel2"])
        s.map(w, background=[("active", C["panel"])],
              indicatorcolor=[("selected", C["accent"]), ("pressed", C["accent"])],
              indicatorbackground=[("selected", C["accent"])])

    s.configure("TCombobox", fieldbackground=C["panel2"], background=C["panel2"],
                foreground=C["text"], arrowcolor=C["muted"], bordercolor=C["line"],
                lightcolor=C["panel2"], darkcolor=C["panel2"], padding=6,
                selectbackground=C["panel2"], selectforeground=C["text"])
    s.map("TCombobox",
          fieldbackground=[("readonly", C["panel2"]), ("focus", C["panel2"])],
          foreground=[("readonly", C["text"])],
          selectbackground=[("readonly", C["panel2"])],
          selectforeground=[("readonly", C["text"])],
          arrowcolor=[("active", C["text"])],
          bordercolor=[("focus", C["accent"])])
    root.option_add("*TCombobox*Listbox.background", C["panel2"])
    root.option_add("*TCombobox*Listbox.foreground", C["text"])
    root.option_add("*TCombobox*Listbox.selectBackground", C["accent"])
    root.option_add("*TCombobox*Listbox.selectForeground", "#ffffff")
    root.option_add("*TCombobox*Listbox.font", F(10))

    s.configure("TEntry", fieldbackground=C["panel2"], foreground=C["text"],
                insertcolor=C["text"], bordercolor=C["line"], lightcolor=C["panel2"],
                darkcolor=C["panel2"], padding=7)
    s.map("TEntry", bordercolor=[("focus", C["accent"])],
          lightcolor=[("focus", C["accent"])], darkcolor=[("focus", C["accent"])])

    s.configure("Treeview", background=C["panel"], fieldbackground=C["panel"],
                foreground=C["text"], rowheight=30, borderwidth=0, relief="flat", font=F(10))
    s.map("Treeview", background=[("selected", C["accent"])],
          foreground=[("selected", "#ffffff")])
    s.configure("Treeview.Heading", background=C["panel2"], foreground=C["muted"],
                relief="flat", borderwidth=0, padding=(8, 8), font=F(9, "bold"))
    s.map("Treeview.Heading", background=[("active", C["hover"])])
    s.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
    s.configure("Cand.Treeview", rowheight=58)

    s.configure("Vertical.TScrollbar", background=C["panel2"], troughcolor=C["panel"],
                bordercolor=C["panel"], arrowcolor=C["muted"], lightcolor=C["panel2"],
                darkcolor=C["panel2"], gripcount=0, relief="flat")
    s.map("Vertical.TScrollbar", background=[("active", C["line"])])
    s.configure("Horizontal.TScale", background=C["panel"], troughcolor=C["panel2"],
                lightcolor=C["panel2"], darkcolor=C["panel2"])


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
        f"{API}/cards/search",
        params={"q": f'!"{name}"', "unique": "prints", "order": "released"},
        headers=HEADERS, timeout=12,
    )
    if r.status_code == 404:  # no exact match -> try fuzzy (forgives typos)
        r = requests.get(f"{API}/cards/named", params={"fuzzy": name},
                         headers=HEADERS, timeout=12)
        if r.status_code == 200:
            # re-search using the corrected name so we get every printing
            fixed = r.json().get("name", name)
            r2 = requests.get(
                f"{API}/cards/search",
                params={"q": f'!"{fixed}"', "unique": "prints", "order": "released"},
                headers=HEADERS, timeout=12,
            )
            data = r2.json().get("data", []) if r2.status_code == 200 else [r.json()]
        else:
            # last resort: any card whose name contains the words we read
            r3 = requests.get(
                f"{API}/cards/search",
                params={"q": name, "unique": "prints", "order": "released"},
                headers=HEADERS, timeout=12,
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


def card_by_name(name, exact=True):
    """One Scryfall card record for a name (or None)."""
    r = requests.get(f"{API}/cards/named",
                     params={"exact" if exact else "fuzzy": name},
                     headers=HEADERS, timeout=12)
    return r.json() if r.status_code == 200 else None


def scryfall_autocomplete(text):
    r = requests.get(f"{API}/cards/autocomplete", params={"q": text},
                     headers=HEADERS, timeout=12)
    return r.json().get("data", []) if r.status_code == 200 else []


def fetch_bytes(url):
    try:
        r = requests.get(url, headers=HEADERS, timeout=15)
        r.raise_for_status()
        return r.content
    except requests.RequestException:
        return None


def decode_image(blob):
    if not blob:
        return None
    try:
        return cv2.imdecode(np.frombuffer(blob, np.uint8), cv2.IMREAD_COLOR)
    except Exception:
        return None


# --------------------------------------------------------------- card names
def norm(s):
    """Lowercase letters/digits/spaces only, accents removed."""
    s = s.lower().replace("æ", "ae")
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii")
    s = re.sub(r"[^a-z0-9 ]+", "", s)
    return re.sub(r"\s+", " ", s).strip()


def grams(s):
    s = f" {s} "
    return {s[i:i + 3] for i in range(len(s) - 2)}


def similarity(a, b):
    """0..1 - how alike two normalised names are (also credits partial reads)."""
    if a == b:
        return 1.0
    best = difflib.SequenceMatcher(None, a, b, autojunk=False).ratio()
    if len(a) + 2 < len(b):  # the reader may have caught only the start of a long name
        part = difflib.SequenceMatcher(None, a, b[:len(a) + 2], autojunk=False).ratio()
        best = max(best, part * 0.93)
    return best


_DIGIT_FIX = str.maketrans("0158", "olsb")


def read_variants(text):
    n = norm(text)
    fixed = norm(text.translate(_DIGIT_FIX))
    return [n] if fixed == n else [n, fixed]


class NameCatalog:
    """Every Magic card name (from Scryfall), cached on disk, for fuzzy matching."""
    URL = f"{API}/catalog/card-names"

    def __init__(self, path):
        self.path = Path(path)
        self.entries = []      # (normalised name, display name)
        self.postings = {}     # trigram -> entry indexes
        self.gcount = []       # number of trigrams in each entry
        self.ready = False

    def start(self):
        threading.Thread(target=self._run, daemon=True).start()

    def _run(self):
        names, age = None, None
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
            names = data.get("names")
            age = time.time() - float(data.get("fetched", 0))
        except Exception:
            pass
        if not names or (age is not None and age > 14 * 86400):
            try:
                r = requests.get(self.URL, headers=HEADERS, timeout=30)
                r.raise_for_status()
                fresh = r.json().get("data", [])
                if fresh:
                    names = fresh
                    save_json(self.path, {"fetched": time.time(), "names": fresh})
            except Exception:
                pass
        if names:
            self.build(names)

    def build(self, names):
        entries, seen = [], set()
        for full in names:
            if not full or full.startswith("A-"):     # skip Alchemy rebalanced copies
                continue
            faces = [full] + (full.split(" // ") if " // " in full else [])
            for face in faces:
                n = norm(face)
                if n and (n, full) not in seen:
                    seen.add((n, full))
                    entries.append((n, full))
        postings, gcount = {}, []
        for i, (n, _) in enumerate(entries):
            gs = grams(n)
            gcount.append(len(gs))
            for g in gs:
                postings.setdefault(g, []).append(i)
        self.postings = postings
        self.gcount = gcount
        self.entries = entries
        self.ready = True

    def _shortlist(self, q, limit=300):
        """Entries sharing the most letter-triples with q (Dice score, so short
        exact names aren't crowded out by long names that merely contain them)."""
        qg = grams(q)
        counts = Counter()
        for g in qg:
            for i in self.postings.get(g, ()):
                counts[i] += 1
        nq = len(qg)
        best = heapq.nlargest(limit, ((2.0 * c / (nq + self.gcount[i]), i)
                                      for i, c in counts.items()))
        return [i for _, i in best]

    def rank(self, reads, limit=8):
        """reads: [(text, confidence)] -> [(card name, score 0..1)] best first."""
        if not self.ready:
            return []
        scores, agree = {}, {}
        for text, conf in reads:
            weight = 0.75 + 0.25 * max(0.0, min(1.0, conf))
            for q in read_variants(text):
                if len(q) < 3:
                    continue
                for i in self._shortlist(q):
                    nm, disp = self.entries[i]
                    s = similarity(q, nm)
                    if s * weight > scores.get(disp, 0.0):
                        scores[disp] = s * weight
                    if s >= 0.8:
                        agree[disp] = agree.get(disp, 0) + 1
        for disp in scores:
            scores[disp] = min(1.0, scores[disp] + min(0.06, 0.02 * (agree.get(disp, 1) - 1)))
        return sorted(scores.items(), key=lambda kv: -kv[1])[:limit]

    def suggest(self, text, limit=7):
        """Type-ahead: names starting with / containing what was typed, then close matches."""
        q = norm(text)
        if len(q) < 2 or not self.ready:
            return []
        out, seen = [], set()

        def add(disp):
            if disp not in seen and len(out) < limit:
                seen.add(disp)
                out.append(disp)

        starts = sorted((e for e in self.entries if e[0].startswith(q)), key=lambda e: len(e[0]))
        for _, disp in starts:
            add(disp)
        if len(out) < limit:
            words = sorted((e for e in self.entries if f" {q}" in e[0]), key=lambda e: len(e[0]))
            for _, disp in words:
                add(disp)
        if len(out) < limit:
            for _, disp in self.rank([(text, 0.6)], limit=limit):
                add(disp)
        return out


# ------------------------------------------------- finding and fixing a card
def order_quad(pts):
    """Order 4 points as top-left, top-right, bottom-right, bottom-left."""
    pts = np.asarray(pts, dtype="float32").reshape(4, 2)
    s = pts.sum(axis=1)
    d = pts[:, 0] - pts[:, 1]
    return np.array([pts[np.argmin(s)], pts[np.argmax(d)],
                     pts[np.argmax(s)], pts[np.argmin(d)]], dtype="float32")


def portrait_quad(q):
    wd = (np.linalg.norm(q[1] - q[0]) + np.linalg.norm(q[2] - q[3])) / 2
    ht = (np.linalg.norm(q[3] - q[0]) + np.linalg.norm(q[2] - q[1])) / 2
    return np.roll(q, -1, axis=0) if wd > ht else q


def detect_card(frame):
    """Find a card-shaped outline in the picture. Returns 4 corner points (in the
    picture's own pixels) or None."""
    h, w = frame.shape[:2]
    scale = 480.0 / max(h, w) if max(h, w) > 480 else 1.0
    small = cv2.resize(frame, None, fx=scale, fy=scale, interpolation=cv2.INTER_AREA) if scale != 1.0 else frame
    g = cv2.cvtColor(small, cv2.COLOR_BGR2GRAY)
    g = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(8, 8)).apply(g)   # helps in dim rooms
    g = cv2.GaussianBlur(g, (5, 5), 0)
    sh, sw = g.shape
    best, best_area = None, 0.0
    for lo, hi in ((30, 90), (10, 45)):
        edges = cv2.Canny(g, lo, hi)
        edges = cv2.dilate(edges, np.ones((3, 3), np.uint8), iterations=1)
        cnts, _ = cv2.findContours(edges, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
        for c in sorted(cnts, key=cv2.contourArea, reverse=True)[:10]:
            area = cv2.contourArea(c)
            if area < 0.06 * sw * sh or area > 0.95 * sw * sh:
                continue
            approx = cv2.approxPolyDP(c, 0.02 * cv2.arcLength(c, True), True)
            if len(approx) == 4 and cv2.isContourConvex(approx):
                pts = approx.reshape(4, 2)
            else:   # fingers / rounded corners: use the tightest rotated box instead
                box = cv2.boxPoints(cv2.minAreaRect(c))
                box_area = cv2.contourArea(box.astype("float32"))
                if box_area <= 0 or area / box_area < 0.80:
                    continue
                pts = box
            q = order_quad(pts)
            wd = (np.linalg.norm(q[1] - q[0]) + np.linalg.norm(q[2] - q[3])) / 2
            ht = (np.linalg.norm(q[3] - q[0]) + np.linalg.norm(q[2] - q[1])) / 2
            if wd <= 0 or ht <= 0:
                continue
            if abs(min(wd, ht) / max(wd, ht) - CARD_RATIO) > 0.14:
                continue
            if area > best_area:
                best, best_area = q, area
        if best is not None:
            break
    if best is None:
        return None
    return portrait_quad(best / scale)


def warp_card(frame, quad):
    """Straighten the card inside quad into a flat CARD_W x CARD_H picture."""
    dst = np.array([[0, 0], [CARD_W - 1, 0], [CARD_W - 1, CARD_H - 1], [0, CARD_H - 1]],
                   dtype="float32")
    m = cv2.getPerspectiveTransform(np.asarray(quad, dtype="float32"), dst)
    return cv2.warpPerspective(frame, m, (CARD_W, CARD_H), flags=cv2.INTER_CUBIC)


def card_box(frame, frac=BOX_HEIGHT_FRACTION):
    h, w = frame.shape[:2]
    bh = int(h * frac)
    bw = int(bh * CARD_RATIO)
    if bw > w:
        bw = w
        bh = int(bw / CARD_RATIO)
    x1, y1 = (w - bw) // 2, (h - bh) // 2
    return x1, y1, x1 + bw, y1 + bh


def extract_card(frame, quad=None, frac=BOX_HEIGHT_FRACTION):
    """Best-effort flat picture of the card: outline if found, else the guide frame."""
    if quad is None:
        quad = detect_card(frame)
    if quad is not None:
        return warp_card(frame, quad)
    x1, y1, x2, y2 = card_box(frame, frac)
    return cv2.resize(frame[y1:y2, x1:x2], (CARD_W, CARD_H), interpolation=cv2.INTER_CUBIC)


def region_for(frame, quad):
    """The part of the picture to judge focus / brightness on."""
    h, w = frame.shape[:2]
    if quad is not None:
        x, y, bw, bh = cv2.boundingRect(np.asarray(quad, dtype="int32"))
        mx, my = int(bw * 0.1), int(bh * 0.1)
        x1, y1 = max(0, x + mx), max(0, y + my)
        x2, y2 = min(w, x + bw - mx), min(h, y + bh - my)
        if x2 - x1 > 20 and y2 - y1 > 20:
            return frame[y1:y2, x1:x2]
    x1, y1, x2, y2 = card_box(frame)
    return frame[y1:y2, x1:x2]


def sharpness_score(img):
    """Bigger = sharper. Drives the live focus check and picks the best frame."""
    g = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    g = cv2.resize(g, (320, max(1, int(g.shape[0] * 320 / g.shape[1]))))
    return float(cv2.Laplacian(g, cv2.CV_64F).var())


def brightness(img):
    return float(cv2.cvtColor(img, cv2.COLOR_BGR2GRAY).mean())


def enhance(card):
    """Brighten dark pictures and boost contrast so small text is readable."""
    lab = cv2.cvtColor(card, cv2.COLOR_BGR2LAB)
    l, a, b = cv2.split(lab)
    mean = float(l.mean())
    if mean < 105:
        gamma = np.log(125 / 255.0) / np.log(max(mean, 8.0) / 255.0)
        gamma = float(np.clip(gamma, 0.35, 1.0))
        lut = np.array([((i / 255.0) ** gamma) * 255 for i in range(256)], dtype="uint8")
        l = cv2.LUT(l, lut)
    l = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8)).apply(l)
    return cv2.cvtColor(cv2.merge((l, a, b)), cv2.COLOR_LAB2BGR)


def art_region(card):
    h, w = card.shape[:2]
    return card[int(h * 0.115):int(h * 0.55), int(w * 0.08):int(w * 0.92)]


def art_similarity(photo, ref):
    """0..1 - how much two pictures of artwork look alike (layout and colour),
    tolerant of blur, brightness and colour casts."""
    def prep(img):
        img = cv2.resize(img, (48, 36), interpolation=cv2.INTER_AREA)
        img = cv2.GaussianBlur(img, (3, 3), 0)
        return cv2.cvtColor(img, cv2.COLOR_BGR2LAB).astype(np.float32)

    a, b = prep(photo), prep(ref)
    total, wsum = 0.0, 0.0
    for ch, wt in ((0, 0.5), (1, 0.25), (2, 0.25)):
        x = a[:, :, ch].ravel()
        y = b[:, :, ch].ravel()
        x = x - x.mean()
        y = y - y.mean()
        d = float(np.linalg.norm(x) * np.linalg.norm(y))
        if d < 1e-6:
            continue
        total += wt * float((x * y).sum() / d)
        wsum += wt
    return max(0.0, total / wsum) if wsum else 0.0


# ----------------------------------------------------------- reading a card
def clean_read(text):
    text = "".join(ch for ch in text if ch.isalnum() or ch in " ',-:")
    return re.sub(r"\s+", " ", text).strip()


def _ocr_once(img):
    try:
        result, _ = _get_ocr_engine()(img)
    except Exception:
        return "", 0.0
    if not result:
        return "", 0.0
    items = sorted(result, key=lambda r: r[0][0][0])        # left to right
    text = " ".join(str(r[1]) for r in items)
    confs = []
    for r in items:
        try:
            confs.append(float(r[2]))
        except (TypeError, ValueError, IndexError):
            pass
    return clean_read(text), (sum(confs) / len(confs) if confs else 0.5)


def ocr_read_iter(card, treatments=4):
    """Yield (text, confidence) reads of the title, trying several image treatments.
    A generator so the caller can stop as soon as a read is good enough."""
    if not HAVE_OCR:
        return
    h, w = card.shape[:2]
    strip = card[int(h * 0.02):int(h * 0.12), int(w * 0.05):int(w * 0.80)]
    strip = cv2.resize(strip, None, fx=2.5, fy=2.5, interpolation=cv2.INTER_CUBIC)
    try:
        strip = cv2.fastNlMeansDenoisingColored(strip, None, 4, 4, 7, 21)
    except cv2.error:
        pass
    gray = cv2.cvtColor(strip, cv2.COLOR_BGR2GRAY)
    clahe = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(4, 4)).apply(gray)
    soft = cv2.GaussianBlur(clahe, (0, 0), 2.5)
    sharp = cv2.addWeighted(clahe, 1.8, soft, -0.8, 0)
    tries = (strip,
             cv2.cvtColor(clahe, cv2.COLOR_GRAY2BGR),
             cv2.cvtColor(sharp, cv2.COLOR_GRAY2BGR),
             cv2.cvtColor(255 - clahe, cv2.COLOR_GRAY2BGR))      # light-on-dark titles
    for img in tries[:treatments]:
        text, conf = _ocr_once(img)
        if text:
            yield text, conf


def recognize(cards, catalog, debug_dir=None, online=True):
    """Work out which card this is. cards: straightened pictures, sharpest first.
    Returns {"reads": [...], "cands": [{name, final, name_score, art_score, art_bytes}]}"""
    prepared = [enhance(c) for c in cards]
    reads, done = [], False
    deadline = time.time() + 14          # never make the user wait much longer than this

    for n, card in enumerate(prepared):
        for text, conf in ocr_read_iter(card, treatments=4 if n == 0 else 2):
            reads.append((text, conf))
            if catalog.ready:
                top = catalog.rank([(text, conf)], limit=1)
                if top and top[0][1] >= 0.95:
                    done = True
                    break
            if time.time() > deadline:
                done = True
                break
        if done:
            break
    if prepared and not done and (not reads or max(c for _, c in reads) < 0.5):
        for text, conf in ocr_read_iter(cv2.rotate(prepared[0], cv2.ROTATE_180)):  # upside down?
            reads.append((text, conf))

    scores = dict(catalog.rank(reads, limit=10)) if catalog.ready else {}
    if reads and online:
        best_text = max(reads, key=lambda r: r[1])[0]
        try:
            hit = card_by_name(best_text, exact=False)
            if hit:
                scores[hit["name"]] = max(scores.get(hit["name"], 0.0), 0.8)
        except Exception:
            pass
        if not catalog.ready:
            try:
                for i, nm in enumerate(scryfall_autocomplete(best_text)[:6]):
                    scores.setdefault(nm, 0.6 - 0.02 * i)
            except Exception:
                pass

    ranked = sorted(scores.items(), key=lambda kv: -kv[1])[:6]
    cands = [{"name": n, "name_score": s, "art_score": None, "final": s, "art_bytes": None}
             for n, s in ranked]

    if cands and online and prepared:      # compare artwork like a visual search would
        photo_art = art_region(prepared[0])

        def look(c):
            try:
                rec = card_by_name(c["name"], exact=True)
                if not rec:
                    return
                blob = fetch_bytes(_art_url(rec))
                img = decode_image(blob)
                if img is None:
                    return
                c["art_bytes"] = blob
                c["art_score"] = art_similarity(photo_art, img)
            except Exception:
                return

        with ThreadPoolExecutor(max_workers=5) as ex:
            list(ex.map(look, cands[:5]))
        for c in cands:
            if c["art_score"] is not None:
                c["final"] = min(1.0, 0.65 * c["name_score"] + 0.35 * c["art_score"])
        cands.sort(key=lambda c: -c["final"])

    if debug_dir:
        try:
            save_debug(debug_dir, cards, reads, cands)
        except Exception:
            pass
    return {"reads": reads, "cands": cands}


def save_debug(debug_dir, cards, reads, cands):
    d = Path(debug_dir) / datetime.datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    d.mkdir(parents=True, exist_ok=True)
    for i, c in enumerate(cards):
        write_image(d / f"card{i}.jpg", c)
    lines = ["Reads (text, confidence):"] + [f"  {t!r}  {c:.2f}" for t, c in reads]
    lines += ["", "Guesses:"] + [
        f"  {c['name']}  name={c['name_score']:.2f}  art={c['art_score']}  final={c['final']:.2f}"
        for c in cands]
    (d / "result.txt").write_text("\n".join(lines), encoding="utf-8")


def rank_printings_by_art(photo_art, matches):
    """Compare the photographed artwork with each printing's artwork.
    Returns {index: score} for the printings that could be compared."""
    todo = [(i, m["art_url"]) for i, m in enumerate(matches[:12]) if m.get("art_url")]
    if not todo:
        return {}

    def score(item):
        i, url = item
        img = decode_image(fetch_bytes(url))
        return i, (art_similarity(photo_art, img) if img is not None else None)

    with ThreadPoolExecutor(max_workers=6) as ex:
        return {i: s for i, s in ex.map(score, todo) if s is not None}


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
    left = card.get("type_line", "").split("//")[0].split("—")[0]
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


# ------------------------------------------------------------ small widgets
def stat_tile(parent, caption):
    f = ttk.Frame(parent, style="Panel.TFrame", padding=(18, 10))
    var = tk.StringVar(value="0")
    ttk.Label(f, textvariable=var, style="StatNum.TLabel").pack(anchor="w")
    ttk.Label(f, text=caption, style="StatCap.TLabel").pack(anchor="w")
    return f, var


def hex_to_bgr(h):
    h = h.lstrip("#")
    return (int(h[4:6], 16), int(h[2:4], 16), int(h[0:2], 16))


# ------------------------------------------------------------ add-card popup
class AddCardDialog(tk.Toplevel):
    """Shown after a snap: reads the card, lists the best guesses with artwork,
    lets you pick the printing and finish."""

    def __init__(self, parent, cards, catalog, finish, debug_dir=None):
        super().__init__(parent)
        self.configure(bg=C["bg"])
        self.title("Add a card")
        self.transient(parent)
        self.resizable(False, False)
        self.result = None
        self.cards = cards
        self.catalog = catalog
        self.debug_dir = debug_dir
        self.matches = []
        self.cands = []
        self.loaded_name = ""
        self._thumbs = []
        self._job = 0
        self._suggest_after = None
        self.name_var = tk.StringVar()
        self.finish_var = tk.StringVar(value=finish)
        self.value_var = tk.StringVar()
        self.msg_var = tk.StringVar()
        self.photo_art = art_region(enhance(cards[0])) if cards else None

        body = ttk.Frame(self, padding=18)
        body.pack(fill="both", expand=True)

        # ---- left: what the camera saw
        left = ttk.Frame(body, style="Panel.TFrame", padding=12)
        left.grid(row=0, column=0, sticky="n", padx=(0, 18))
        if cards:
            pil = Image.fromarray(cv2.cvtColor(cards[0], cv2.COLOR_BGR2RGB))
            pil.thumbnail((250, 350))
            self._photo = ImageTk.PhotoImage(pil)
            ttk.Label(left, image=self._photo, style="Panel.TLabel").pack()
            ttk.Label(left, text="Your photo, straightened",
                      style="PanelMuted.TLabel").pack(pady=(8, 0))
        else:
            ttk.Label(left, text="Type a card name\nto add it by hand",
                      style="PanelMuted.TLabel", justify="center").pack(padx=50, pady=130)

        # ---- right: name, guesses, printings
        right = ttk.Frame(body)
        right.grid(row=0, column=1, sticky="nsew")

        ttk.Label(right, text="Card name", style="Section.TLabel").pack(anchor="w")
        row = ttk.Frame(right)
        row.pack(fill="x", pady=(4, 0))
        self.entry = ttk.Entry(row, textvariable=self.name_var, width=44, font=F(12))
        self.entry.pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Search", command=self.search).pack(side="left", padx=(8, 0))
        ttk.Label(right, textvariable=self.msg_var, style="Muted.TLabel",
                  wraplength=560, justify="left").pack(anchor="w", pady=(8, 8))

        ttk.Label(right, text="Best guesses", style="Section.TLabel").pack(anchor="w")
        cf = ttk.Frame(right, style="Panel.TFrame")
        cf.pack(fill="x", pady=(4, 10))
        self.cand_tree = ttk.Treeview(cf, columns=("pct",), show="tree", height=3,
                                      style="Cand.Treeview", selectmode="browse")
        self.cand_tree.column("#0", width=440, stretch=True)
        self.cand_tree.column("pct", width=70, anchor="e", stretch=False)
        csb = ttk.Scrollbar(cf, orient="vertical", command=self.cand_tree.yview)
        self.cand_tree.configure(yscrollcommand=csb.set)
        self.cand_tree.pack(side="left", fill="x", expand=True)
        csb.pack(side="right", fill="y")

        ttk.Label(right, text="Printings", style="Section.TLabel").pack(anchor="w")
        pf = ttk.Frame(right, style="Panel.TFrame")
        pf.pack(fill="x", pady=(4, 10))
        cols = [("set", "Set", 230), ("num", "No.", 55), ("rarity", "Rarity", 75),
                ("nonfoil", "Non-foil", 75), ("foil", "Foil", 75)]
        self.tree = ttk.Treeview(pf, columns=[c[0] for c in cols], show="headings",
                                 height=5, selectmode="browse")
        for key, text, width in cols:
            self.tree.heading(key, text=text)
            self.tree.column(key, width=width, anchor="w" if key == "set" else "e")
        psb = ttk.Scrollbar(pf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=psb.set)
        self.tree.pack(side="left", fill="x", expand=True)
        psb.pack(side="right", fill="y")

        opts = ttk.Frame(right)
        opts.pack(fill="x", pady=(0, 12))
        ttk.Radiobutton(opts, text="Non-foil", value="nonfoil", variable=self.finish_var,
                        style="Seg.Toolbutton", takefocus=0).pack(side="left")
        ttk.Radiobutton(opts, text="Foil", value="foil", variable=self.finish_var,
                        style="Seg.Toolbutton", takefocus=0).pack(side="left", padx=(2, 0))
        ttk.Label(opts, text="Custom value $", style="Muted.TLabel").pack(side="left", padx=(24, 6))
        ttk.Entry(opts, textvariable=self.value_var, width=8).pack(side="left")

        btns = ttk.Frame(right)
        btns.pack(fill="x")
        ttk.Button(btns, text="Add card", style="Accent.TButton",
                   command=self.add).pack(side="right")
        ttk.Button(btns, text="Cancel", command=self.destroy).pack(side="right", padx=(0, 8))

        self.entry.bind("<KeyRelease>", self._on_key)
        self.entry.bind("<Return>", lambda e: self.search())
        self.entry.bind("<Down>", self._focus_guesses)
        self.cand_tree.bind("<<TreeviewSelect>>", self._on_cand_select)
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

        if cards:
            self.msg_var.set("Reading the card... (the first scan can take a few seconds)")
            self._bg(lambda: recognize(self.cards, self.catalog, self.debug_dir),
                     self._on_recognized)
        else:
            self.msg_var.set("Type a few letters of the card name - suggestions appear as you type.")

    # ---------------------------------------------------------- background work
    def _bg(self, fn, done):
        """Run fn in a thread; call done(ok, value) back on the screen thread."""
        q = queue.Queue()

        def run():
            try:
                q.put((True, fn()))
            except Exception as e:  # noqa: BLE001 - shown to the user, not hidden
                q.put((False, e))

        threading.Thread(target=run, daemon=True).start()

        def poll():
            try:
                if not self.winfo_exists():
                    return
            except tk.TclError:
                return
            try:
                ok, val = q.get_nowait()
            except queue.Empty:
                self.after(80, poll)
                return
            done(ok, val)

        self.after(80, poll)

    def _on_recognized(self, ok, val):
        if not ok:
            self.msg_var.set("Couldn't read the card automatically. Type a few letters "
                             "of the name and pick from the suggestions.")
            return
        self.cands = val["cands"]
        self._show_candidates(self.cands)
        if val["reads"] and not self.name_var.get().strip():
            self.name_var.set(max(val["reads"], key=lambda r: r[1])[0])
        if self.cands and self.cands[0]["final"] >= 0.5:
            self.msg_var.set(f"Best guess: {self.cands[0]['name']}. Not right? "
                             "Pick another below, or type the name.")
            self.cand_tree.selection_set("0")
        elif self.cands:
            self.msg_var.set("Not sure about this one - check the guesses, or type the name.")
        else:
            self.msg_var.set("Couldn't read this card clearly. Type a few letters of the "
                             "name - suggestions appear as you type.")

    # ------------------------------------------------------------ guesses list
    def _show_candidates(self, cands):
        self.cand_tree.delete(*self.cand_tree.get_children())
        self._thumbs = []
        for i, c in enumerate(cands):
            img = ""
            if c.get("art_bytes"):
                try:
                    im = Image.open(io.BytesIO(c["art_bytes"])).convert("RGB")
                    im.thumbnail((78, 56))
                    ph = ImageTk.PhotoImage(im)
                    self._thumbs.append(ph)
                    img = ph
                except Exception:
                    img = ""
            pct = f"{int(round(c['final'] * 100))}%" if c.get("final") is not None else ""
            self.cand_tree.insert("", "end", iid=str(i), text="  " + c["name"],
                                  image=img, values=(pct,))

    def _on_cand_select(self, event=None):
        sel = self.cand_tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        if idx >= len(self.cands):
            return
        name = self.cands[idx]["name"]
        if name == self.loaded_name:
            return
        self.name_var.set(name)
        self.load_printings(name)

    def _focus_guesses(self, event=None):
        kids = self.cand_tree.get_children()
        if kids:
            self.cand_tree.focus_set()
            self.cand_tree.selection_set(kids[0])
        return "break"

    # --------------------------------------------------------------- type-ahead
    def _on_key(self, event):
        if event.keysym in ("Return", "Escape", "Down", "Up", "Tab", "Shift_L", "Shift_R"):
            return
        if self._suggest_after is not None:
            self.after_cancel(self._suggest_after)
        self._suggest_after = self.after(220, self._suggest)

    def _suggest(self):
        self._suggest_after = None
        text = self.name_var.get().strip()
        if len(text) < 2:
            return
        if self.catalog.ready:
            names = self.catalog.suggest(text)
            self._set_suggestions(names)
        else:
            self._job += 1
            token = self._job
            self._bg(lambda: scryfall_autocomplete(text)[:7],
                     lambda ok, val: token == self._job and ok and self._set_suggestions(val))

    def _set_suggestions(self, names):
        self.cands = [{"name": n, "final": None, "art_bytes": None} for n in names]
        self._show_candidates(self.cands)
        if names:
            self.msg_var.set("Pick a suggestion below, or press Search.")

    # --------------------------------------------------------------- printings
    def search(self):
        name = self.name_var.get().strip()
        if name:
            self.load_printings(name)

    def load_printings(self, name):
        self.loaded_name = name
        self._job += 1
        token = self._job
        self.msg_var.set(f"Looking up {name}...")
        self._fill_printings([])
        self._bg(lambda: search_mtg(name),
                 lambda ok, val: self._on_printings(token, ok, val))

    def _on_printings(self, token, ok, val):
        if token != self._job:
            return
        if not ok:
            self.matches = []
            self.msg_var.set("Couldn't reach Scryfall - check your internet connection. "
                             "You can still add the card with a custom value.")
            return
        self.matches = val
        self._fill_printings(val)
        if not val:
            self.msg_var.set("No card found with that name - check the spelling, "
                             "or add it with a custom value.")
            return
        self.msg_var.set(f"{len(val)} printing(s) found. Pick the one you have.")
        self.tree.selection_set("0")
        if self.photo_art is not None and len(val) > 1:
            self.msg_var.set(f"{len(val)} printings found - comparing artwork...")
            self._bg(lambda: rank_printings_by_art(self.photo_art, val),
                     lambda ok2, scores: self._on_art(token, ok2, scores))

    def _on_art(self, token, ok, scores):
        if token != self._job or not ok:
            return
        self.msg_var.set(f"{len(self.matches)} printing(s) found. Pick the one you have.")
        if len(scores) < 2:
            return
        ordered = sorted(scores.items(), key=lambda kv: -kv[1])
        (best_i, best), (_, second) = ordered[0], ordered[1]
        if best >= 0.35 and best - second >= 0.07:
            self.tree.selection_set(str(best_i))
            self.tree.see(str(best_i))
            m = self.matches[best_i]
            self.msg_var.set(f"The artwork looks most like {m['set']} #{m['number']} - "
                             "check that it matches your card.")

    def _fill_printings(self, matches):
        self.tree.delete(*self.tree.get_children())
        for i, m in enumerate(matches):
            nf = f"${m['price_nonfoil']:,.2f}" if m["price_nonfoil"] else "n/a"
            fo = f"${m['price_foil']:,.2f}" if m["price_foil"] else "n/a"
            self.tree.insert("", "end", iid=str(i),
                             values=(m["set"], m["number"], m["rarity"], nf, fo))

    # --------------------------------------------------------------------- add
    def add(self):
        sel = self.tree.selection()
        custom = self.value_var.get().strip().replace("$", "")
        if sel and self.matches:
            card = dict(self.matches[int(sel[0])])
        else:
            name = self.name_var.get().strip()
            if not name or not custom:
                messagebox.showinfo(APP_NAME, "Pick a printing from the list, or type a "
                                    "name and a custom value.", parent=self)
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
        root.geometry("1380x800")
        root.minsize(1240, 720)
        ensure_dirs()
        apply_theme(root)
        self.settings = load_json(SETTINGS_FILE, {})
        self.cards = load_cards()
        self.catalog = NameCatalog(NAMES_FILE)
        self.catalog.start()

        self.finish = tk.StringVar(value=self.settings.get("finish", "nonfoil"))
        self.camera_var = tk.StringVar(value=str(self.settings.get("camera_index", 0)))
        self.res_var = tk.StringVar(value=self.settings.get("resolution", RESOLUTIONS[0][0]))
        self.autofocus = tk.BooleanVar(value=bool(self.settings.get("autofocus", True)))
        self.focus_value = tk.DoubleVar(value=float(self.settings.get("focus", 128)))
        self.debug_var = tk.BooleanVar(value=bool(self.settings.get("debug", False)))
        self.type_var = tk.StringVar(value="All")
        self.color_var = tk.StringVar(value="All")
        self.sort_var = tk.StringVar(value=SORT_MODES[0][0])
        self.status_var = tk.StringVar(value=f"Your cards are saved in: {DATA_DIR}")
        self.detail_var = tk.StringVar()

        self.cap = None
        self.last_frame = None
        self.photo = None
        self.busy = False
        self.quad = None
        self.quad_miss = 0
        self.frame_count = 0
        self.sharp_avg = 0.0
        self.frame_buffer = deque(maxlen=6)   # recent (sharpness, frame, quad)
        self._pill_state = None

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
        root.columnconfigure(0, weight=0)
        root.columnconfigure(1, weight=1)
        root.rowconfigure(1, weight=1)

        # ---- header
        head = ttk.Frame(root, padding=(22, 16, 22, 6))
        head.grid(row=0, column=0, columnspan=2, sticky="ew")
        head.columnconfigure(0, weight=1)
        titles = ttk.Frame(head)
        titles.grid(row=0, column=0, sticky="w")
        ttk.Label(titles, text="MTG Card Scanner", style="Title.TLabel").pack(anchor="w")
        ttk.Label(titles, text="Scan, price and sort your Magic cards",
                  style="Muted.TLabel").pack(anchor="w")
        tiles = ttk.Frame(head)
        tiles.grid(row=0, column=1, sticky="e")
        t1, self.tile_count = stat_tile(tiles, "Cards shown")
        t2, self.tile_view = stat_tile(tiles, "Value of this view")
        t3, self.tile_all = stat_tile(tiles, "Whole collection")
        for t in (t1, t2, t3):
            t.pack(side="left", padx=(8, 0))

        # ---- left: camera
        left = ttk.Frame(root, padding=(22, 8, 10, 16))
        left.grid(row=1, column=0, sticky="nsw")
        cam = ttk.Frame(left, style="Panel.TFrame", padding=14)
        cam.pack(fill="x")
        self.canvas = tk.Canvas(cam, width=PREVIEW_W, height=PREVIEW_H, bg="#0b0c10",
                                highlightthickness=0)
        self.canvas.pack()
        self.img_item = self.canvas.create_image(PREVIEW_W // 2, PREVIEW_H // 2)
        self.msg_item = self.canvas.create_text(
            PREVIEW_W // 2, PREVIEW_H // 2, text="Starting camera...", fill="#cfd3de",
            width=PREVIEW_W - 80, justify="center", font=F(12))

        pill_row = ttk.Frame(cam, style="Panel.TFrame")
        pill_row.pack(fill="x", pady=(10, 0))
        self.pill = tk.Label(pill_row, text="Starting camera...", font=F(10, "bold"),
                             bg=C["panel2"], fg=C["muted"], padx=14, pady=6)
        self.pill.pack(side="left")
        ttk.Label(pill_row, textvariable=self.detail_var,
                  style="PanelMuted.TLabel").pack(side="right")

        row = ttk.Frame(cam, style="Panel.TFrame")
        row.pack(fill="x", pady=(12, 0))
        ttk.Button(row, text="Snap card   (Space)", style="Accent.TButton",
                   command=self.snap, takefocus=0).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Photo file...", command=self.scan_file,
                   takefocus=0).pack(side="left", padx=(8, 0), ipady=3)
        ttk.Button(row, text="Add by name...", command=self.add_by_name,
                   takefocus=0).pack(side="left", padx=(8, 0), ipady=3)

        fin = ttk.Frame(cam, style="Panel.TFrame")
        fin.pack(fill="x", pady=(12, 0))
        ttk.Label(fin, text="New scans are", style="PanelMuted.TLabel").pack(side="left", padx=(0, 12))
        ttk.Radiobutton(fin, text="Non-foil", value="nonfoil", variable=self.finish,
                        style="Seg.Toolbutton", command=self.on_finish_change,
                        takefocus=0).pack(side="left")
        ttk.Radiobutton(fin, text="Foil", value="foil", variable=self.finish,
                        style="Seg.Toolbutton", command=self.on_finish_change,
                        takefocus=0).pack(side="left", padx=(2, 0))
        self.cam_toggle = ttk.Button(fin, text="Camera settings  v", style="Link.TButton",
                                     command=self.toggle_camera_settings, takefocus=0)
        self.cam_toggle.pack(side="right")

        self.cam_frame = ttk.Frame(cam, style="Panel.TFrame")
        r1 = ttk.Frame(self.cam_frame, style="Panel.TFrame")
        r1.pack(fill="x", pady=(12, 0))
        ttk.Label(r1, text="Camera #", style="PanelMuted.TLabel").pack(side="left")
        cb = ttk.Combobox(r1, textvariable=self.camera_var, values=["0", "1", "2", "3"],
                          width=3, state="readonly")
        cb.pack(side="left", padx=(6, 16))
        cb.bind("<<ComboboxSelected>>", self.on_camera_change)
        ttk.Label(r1, text="Quality", style="PanelMuted.TLabel").pack(side="left")
        res = ttk.Combobox(r1, textvariable=self.res_var, values=[r[0] for r in RESOLUTIONS],
                           width=20, state="readonly")
        res.pack(side="left", padx=6)
        res.bind("<<ComboboxSelected>>", self.on_camera_change)
        r2 = ttk.Frame(self.cam_frame, style="Panel.TFrame")
        r2.pack(fill="x", pady=(10, 0))
        ttk.Checkbutton(r2, text="Auto-focus", variable=self.autofocus,
                        command=self.on_focus_change, takefocus=0).pack(side="left")
        ttk.Label(r2, text="   Manual focus", style="PanelMuted.TLabel").pack(side="left")
        self.focus_scale = ttk.Scale(r2, from_=0, to=255, variable=self.focus_value,
                                     orient="horizontal", length=170)
        self.focus_scale.pack(side="left", padx=8)
        self.focus_scale.bind("<ButtonRelease-1>", lambda e: self.on_focus_change())
        r3 = ttk.Frame(self.cam_frame, style="Panel.TFrame")
        r3.pack(fill="x", pady=(10, 0))
        ttk.Button(r3, text="Camera's own settings window", command=self.open_driver_settings,
                   takefocus=0).pack(side="left")
        ttk.Checkbutton(r3, text="Save diagnostic pictures", variable=self.debug_var,
                        command=self.on_debug_change, takefocus=0).pack(side="left", padx=14)

        ttk.Label(left, justify="left", style="Muted.TLabel", wraplength=PREVIEW_W, text=(
            "Tips: fill the frame with the card, hold it flat and steady, and keep light "
            "on it without glare. A brighter room helps more than anything else. "
            "Still struggling? Take a photo with your phone and use Photo file...")
                  ).pack(anchor="w", pady=(12, 0))

        # ---- right: collection
        right = ttk.Frame(root, padding=(10, 8, 22, 16))
        right.grid(row=1, column=1, sticky="nsew")
        panel = ttk.Frame(right, style="Panel.TFrame", padding=14)
        panel.pack(fill="both", expand=True)
        panel.columnconfigure(0, weight=1)
        panel.rowconfigure(1, weight=1)

        bar = ttk.Frame(panel, style="Panel.TFrame")
        bar.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        for label, var, values, width in (
                ("Type", self.type_var, TYPE_FILTERS, 12),
                ("Color", self.color_var, COLOR_FILTERS, 11),
                ("Sort", self.sort_var, [n for n, _ in SORT_MODES], 18)):
            ttk.Label(bar, text=label, style="PanelMuted.TLabel").pack(side="left", padx=(0, 6))
            c = ttk.Combobox(bar, textvariable=var, values=values, width=width,
                             state="readonly")
            c.pack(side="left", padx=(0, 16))
            c.bind("<<ComboboxSelected>>", self.on_filter_change)

        cols = [("name", "Name", 210, "w"), ("type", "Type", 90, "w"),
                ("color", "Color", 90, "w"), ("set", "Set", 170, "w"),
                ("finish", "Finish", 75, "w"), ("value", "Value", 80, "e")]
        tframe = ttk.Frame(panel, style="Panel.TFrame")
        tframe.grid(row=1, column=0, sticky="nsew")
        tframe.columnconfigure(0, weight=1)
        tframe.rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(tframe, columns=[c[0] for c in cols], show="headings",
                                 selectmode="extended")
        for key, text, width, anchor in cols:
            self.tree.heading(key, text=text, anchor=anchor)
            self.tree.column(key, width=width, anchor=anchor)
        self.tree.tag_configure("odd", background=C["stripe"])
        self.tree.tag_configure("foil", foreground=C["gold"])
        sb = ttk.Scrollbar(tframe, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.bind("<<TreeviewSelect>>", lambda e: self.canvas.focus_set())

        btns = ttk.Frame(panel, style="Panel.TFrame")
        btns.grid(row=2, column=0, sticky="ew", pady=(12, 0))
        for text, cmd, style in (("Switch foil / non-foil", self.flip_selected, "TButton"),
                                 ("Remove selected", self.remove_selected, "Danger.TButton"),
                                 ("Export this view", self.export_view, "TButton"),
                                 ("Export all", self.export_all, "TButton"),
                                 ("Open my files", lambda: open_folder(DATA_DIR), "TButton")):
            ttk.Button(btns, text=text, command=cmd, style=style,
                       takefocus=0).pack(side="left", padx=(0, 8))

        tk.Label(root, textvariable=self.status_var, anchor="w", bg=C["panel"],
                 fg=C["muted"], font=F(9), padx=22, pady=6).grid(
            row=2, column=0, columnspan=2, sticky="ew")

    def toggle_camera_settings(self):
        if self.cam_frame.winfo_ismapped():
            self.cam_frame.pack_forget()
            self.cam_toggle.configure(text="Camera settings  v")
        else:
            self.cam_frame.pack(fill="x")
            self.cam_toggle.configure(text="Camera settings  ^")

    # ------------------------------------------------------------ camera
    def _try_open(self, idx):
        cap = cv2.VideoCapture(idx, cv2.CAP_DSHOW) if os.name == "nt" else cv2.VideoCapture(idx)
        if cap is not None and cap.isOpened():
            return cap
        if cap is not None:
            cap.release()
        return None

    def open_camera(self):
        if self.cap is not None:
            self.cap.release()
            self.cap = None
        self.last_frame = None
        self.quad = None
        self.frame_buffer.clear()
        wanted = int(self.camera_var.get())
        cap = self._try_open(wanted)
        if cap is None:                       # try the other camera numbers too
            for idx in range(4):
                if idx != wanted:
                    cap = self._try_open(idx)
                    if cap is not None:
                        self.camera_var.set(str(idx))
                        break
        if cap is None:
            self.cap = None
            return
        _, rw, rh = next((r for r in RESOLUTIONS if r[0] == self.res_var.get()), RESOLUTIONS[0])
        cap.set(cv2.CAP_PROP_FOURCC, cv2.VideoWriter_fourcc(*"MJPG"))
        cap.set(cv2.CAP_PROP_FRAME_WIDTH, rw)
        cap.set(cv2.CAP_PROP_FRAME_HEIGHT, rh)
        self.cap = cap
        self.apply_focus()

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
                     "another app, then open Camera settings and try another camera number. "
                     "You can still use Photo file... or Add by name...")
            self.set_pill("warn", "No camera found")
            self.detail_var.set("")
            return

        self.last_frame = frame
        self.frame_count += 1
        if self.frame_count % 3 == 0:                     # look for the card outline
            q = detect_card(frame)
            if q is not None:
                if self.quad is not None and np.abs(self.quad - q).max() < 40:
                    q = 0.5 * self.quad + 0.5 * q          # smooth the jitter
                self.quad, self.quad_miss = q.astype("float32"), 0
            else:
                self.quad_miss += 1
                if self.quad_miss > 6:
                    self.quad = None

        region = region_for(frame, self.quad)
        sharp = sharpness_score(region)
        bright = brightness(region)
        self.sharp_avg = sharp if self.sharp_avg == 0 else 0.85 * self.sharp_avg + 0.15 * sharp
        self.frame_buffer.append((sharp, frame, self.quad))

        state, text = self.assess(frame, bright)
        self.set_pill(state, text)
        if self.frame_count % 5 == 0:
            self.detail_var.set(f"focus {self.sharp_avg:.0f}   light {bright:.0f}")

        h, w = frame.shape[:2]
        scale = min(PREVIEW_W / w, PREVIEW_H / h)
        small = cv2.resize(frame, (int(w * scale), int(h * scale)), interpolation=cv2.INTER_AREA)
        self.draw_guide(small, state, scale)
        rgb = cv2.cvtColor(small, cv2.COLOR_BGR2RGB)
        self.photo = ImageTk.PhotoImage(Image.fromarray(rgb))
        self.canvas.itemconfig(self.img_item, image=self.photo)
        self.canvas.itemconfig(self.msg_item, state="hidden")

    def assess(self, frame, bright):
        """Decide what to tell the user about the live picture."""
        if self.quad is None:
            return "idle", "Place the card inside the frame"
        h, w = frame.shape[:2]
        area = cv2.contourArea(self.quad.astype("float32")) / float(w * h)
        if area < 0.10:
            return "warn", "Move the card closer"
        if bright < 55:
            return "warn", "Too dark - add more light"
        if self.sharp_avg < 45:
            return "warn", "Blurry - hold steady or adjust focus"
        return "good", "Ready - press Space"

    def set_pill(self, state, text):
        if (state, text) == self._pill_state:
            return
        self._pill_state = (state, text)
        bg = {"good": C["good"], "warn": C["warn"]}.get(state, C["panel2"])
        fg = "#0d1117" if state in ("good", "warn") else C["muted"]
        self.pill.configure(text=text, bg=bg, fg=fg)

    def draw_guide(self, img, state, scale):
        """Draw the card outline (when found) or the empty guide frame."""
        color = {"good": hex_to_bgr(C["good"]), "warn": hex_to_bgr(C["warn"])}.get(
            state, (225, 225, 225))
        if self.quad is not None:
            pts = (self.quad * scale).astype("int32")
            cv2.polylines(img, [pts], True, color, 3, cv2.LINE_AA)
            for p in pts:
                cv2.circle(img, tuple(int(v) for v in p), 6, color, -1, cv2.LINE_AA)
            return
        x1, y1, x2, y2 = card_box(img)
        n = 30
        for (cx, cy, dx, dy) in ((x1, y1, 1, 1), (x2, y1, -1, 1), (x1, y2, 1, -1), (x2, y2, -1, -1)):
            cv2.line(img, (cx, cy), (cx + dx * n, cy), color, 3, cv2.LINE_AA)
            cv2.line(img, (cx, cy), (cx, cy + dy * n), color, 3, cv2.LINE_AA)

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

    def on_debug_change(self):
        self.settings["debug"] = bool(self.debug_var.get())
        save_json(SETTINGS_FILE, self.settings)
        if self.debug_var.get():
            self.set_status(f"Diagnostic pictures will be saved in: {DEBUG_DIR}")

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
        for n, c in enumerate(view):
            tags = []
            if n % 2:
                tags.append("odd")
            if c["finish"] == "foil":
                tags.append("foil")
            self.tree.insert("", "end", iid=c["id"], tags=tags, values=(
                c["name"], main_type(c), color_text(c), c["set"],
                finish_text(c), f"${c['price']:,.2f}"))
        keep = [i for i in keep_selection if self.tree.exists(i)]
        if keep:
            self.tree.selection_set(keep)
        total = len(self.cards)
        self.tile_count.set(f"{len(view)}" if len(view) == total else f"{len(view)} of {total}")
        self.tile_view.set(f"${sum(c['price'] for c in view):,.2f}")
        self.tile_all.set(f"${sum(c['price'] for c in self.cards):,.2f}")

    def selected_cards(self):
        ids = set(self.tree.selection())
        return [c for c in self.cards if c["id"] in ids]

    def save_cards(self):
        save_json(CARDS_FILE, self.cards)

    # ---------------------------------------------------------- snapping
    def snap(self):
        if self.busy:
            return
        if self.last_frame is None or not self.frame_buffer:
            messagebox.showinfo(APP_NAME, "The camera isn't working yet, so there's nothing "
                                "to snap. You can use Photo file... or Add by name... instead.")
            return
        best = sorted(self.frame_buffer, key=lambda t: -t[0])[:3]   # sharpest frames first
        cards = [extract_card(frame, quad) for _, frame, quad in best]
        self.run_add_dialog(cards)

    def scan_file(self):
        if self.busy:
            return
        path = filedialog.askopenfilename(
            parent=self.root, title="Choose a photo of a card",
            filetypes=[("Pictures", "*.jpg *.jpeg *.png *.bmp *.webp"), ("All files", "*.*")])
        if not path:
            return
        try:
            img = cv2.imdecode(np.fromfile(path, dtype=np.uint8), cv2.IMREAD_COLOR)
        except Exception:
            img = None
        if img is None:
            messagebox.showerror(APP_NAME, "Couldn't open that picture.")
            return
        self.run_add_dialog([extract_card(img, None, frac=1.0)])

    def add_by_name(self):
        if not self.busy:
            self.run_add_dialog([])

    def run_add_dialog(self, cards):
        self.busy = True
        try:
            dlg = AddCardDialog(self.root, cards, self.catalog, self.finish.get(),
                                DEBUG_DIR if self.debug_var.get() else None)
            self.root.wait_window(dlg)
            card = dlg.result
        finally:
            self.busy = False
        if not card:
            self.set_status("Cancelled - nothing added.")
            return

        card["id"] = f"c{time.time_ns()}"
        card["scanned_at"] = time.time()
        card["image"] = ""
        if cards:
            try:  # keep a photo of the scan
                safe = "".join(ch for ch in card["name"] if ch.isalnum())[:30] or "card"
                fname = f"{datetime.datetime.now():%Y%m%d_%H%M%S}_{safe}.jpg"
                write_image(SCANS_DIR / fname, cards[0])
                card["image"] = fname
            except OSError:
                pass
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
