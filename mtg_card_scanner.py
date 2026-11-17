"""
MTG Card Scanner - desktop app
==============================
Hold a Magic: The Gathering card up to your webcam (or send a photo from your
phone), and the app finds the card, straightens it, reads the name, and
suggests the most likely cards with their artwork. You confirm the right one,
pick the printing, and it is added to your list with its price from Scryfall.

Ways to add a card:
  * Webcam - press Space, or switch to Auto and just hold the card still
  * Phone  - scan a QR code, take a photo, it appears on the PC
  * Photo file, or type a name, or a set code + collector number (TLA 58)

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
import hashlib
import heapq
import io
import json
import os
import queue
import re
import secrets
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unicodedata
from collections import Counter, deque
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, urlparse

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

import cv2
import numpy as np
import requests
from PIL import Image, ImageTk

# ------------------------------------------------------- card-name reader (OCR)
# RapidOCR ships its own models inside the app, so there is nothing extra to
# install. It is loaded in the background at start-up so the window opens
# instantly; if it can't load, you just type the name instead.
_OCR = {"engine": None, "error": None}
OCR_READY = threading.Event()


def _load_ocr():
    try:
        from rapidocr_onnxruntime import RapidOCR
        engine = RapidOCR()
        engine(np.full((48, 240, 3), 255, np.uint8))     # warm-up run
        _OCR["engine"] = engine
    except Exception as e:  # noqa: BLE001
        _OCR["error"] = e
    finally:
        OCR_READY.set()


def start_ocr_warmup():
    threading.Thread(target=_load_ocr, daemon=True).start()


def _get_ocr_engine():
    OCR_READY.wait(timeout=120)
    if _OCR["engine"] is None:
        raise RuntimeError("the card-name reader isn't available")
    return _OCR["engine"]


def ocr_available():
    return not (OCR_READY.is_set() and _OCR["engine"] is None)


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

# Version. The installer build (GitHub Actions) writes build_info.txt next to the app with
# the full version (for example 1.3.27) and the name of your GitHub repository, so the
# app knows what it is and where to look for updates. Running from source: version x.y.0.
APP_BASE_VERSION = "1.3"


def app_dir():
    return Path(getattr(sys, "_MEIPASS", Path(__file__).resolve().parent))


def read_build_info():
    info = {}
    try:
        for line in (app_dir() / "build_info.txt").read_text(encoding="utf-8").splitlines():
            if "=" in line:
                k, v = line.split("=", 1)
                info[k.strip()] = v.strip()
    except OSError:
        pass
    return info


BUILD_INFO = read_build_info()
APP_VERSION = BUILD_INFO.get("version") or f"{APP_BASE_VERSION}.0"
IS_BUILT = bool(getattr(sys, "frozen", False))
HEADERS = {"User-Agent": f"MTGCardScannerApp/{APP_VERSION}", "Accept": "application/json"}
API = "https://api.scryfall.com"


def line_total(c):
    return c["price"] * c.get("qty", 1)


SORT_MODES = [
    ("Value: high to low", lambda c: -line_total(c)),
    ("Value: low to high", lambda c: line_total(c)),
    ("Name: A to Z",       lambda c: c["name"].lower()),
    ("Set: A to Z",        lambda c: (c["set"].lower(), c["name"].lower())),
    ("Quantity: most first", lambda c: (-c["qty"], c["name"].lower())),
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
        try:
            c["qty"] = max(1, int(c.get("qty") or 1))
        except (TypeError, ValueError):
            c["qty"] = 1
    return cards


def same_card(a, b):
    """Same printing and finish -> scanning it again just adds to the quantity."""
    return (a["set"] != "?" and
            (a["name"], a["set"], a["number"], a["finish"]) ==
            (b["name"], b["set"], b["number"], b["finish"]))


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
    s.configure("Small.TButton", padding=(10, 6))
    s.configure("Link.TButton", background=C["panel"], foreground=C["muted"], padding=(2, 4))
    s.map("Link.TButton", foreground=[("active", C["text"])],
          background=[("active", C["panel"])])

    # segmented toggle (used for Non-foil / Foil and Manual / Auto)
    s.configure("Seg.Toolbutton", background=C["panel2"], foreground=C["muted"],
                padding=(18, 8), borderwidth=0, relief="flat", anchor="center")
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

    for w in ("TEntry", "TSpinbox"):
        s.configure(w, fieldbackground=C["panel2"], foreground=C["text"],
                    insertcolor=C["text"], bordercolor=C["line"], lightcolor=C["panel2"],
                    darkcolor=C["panel2"], arrowcolor=C["muted"], background=C["panel2"],
                    padding=7)
        s.map(w, bordercolor=[("focus", C["accent"])],
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
    s.configure("TNotebook", background=C["bg"], borderwidth=0, tabmargins=(0, 0, 0, 0))
    s.configure("TNotebook.Tab", background=C["panel2"], foreground=C["muted"],
                padding=(18, 9), borderwidth=0)
    s.map("TNotebook.Tab", background=[("selected", C["accent"]), ("active", C["hover"])],
          foreground=[("selected", "#ffffff"), ("active", C["text"])])
    s.configure("Horizontal.TProgressbar", troughcolor=C["panel2"], background=C["accent"],
                bordercolor=C["panel"], lightcolor=C["accent"], darkcolor=C["accent"])


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


class ScryfallBusy(Exception):
    """Scryfall asked us to slow down (or we are about to exceed its limits)."""

    def __init__(self, seconds=30):
        self.seconds = max(1, int(seconds))
        super().__init__(f"Scryfall is busy - try again in about {self.seconds} seconds")


# Scryfall allows 2 requests/second on search, named, random and collection and
# 10/second on everything else. Going over gets you locked out for 30 seconds
# (and repeat offenders get blocked), so EVERY call to api.scryfall.com goes
# through this one polite gatekeeper, from every thread.
SLOW_ENDPOINTS = ("/cards/search", "/cards/named", "/cards/random", "/cards/collection")
SLOW_GAP, FAST_GAP = 0.6, 0.12       # seconds between calls (limits are 0.5 / 0.1)
MAX_QUEUE_WAIT = 6.0                 # don't let a long line of calls pile up
_gate = threading.Lock()
_next_slot = {"slow": 0.0, "fast": 0.0}
_blocked_until = 0.0


def scryfall(method, path, **kwargs):
    global _blocked_until
    kind = "slow" if path.startswith(SLOW_ENDPOINTS) else "fast"
    gap = SLOW_GAP if kind == "slow" else FAST_GAP
    timeout = kwargs.pop("timeout", 15)
    with _gate:
        now = time.time()
        if now < _blocked_until:
            raise ScryfallBusy(_blocked_until - now + 1)
        start = max(now, _next_slot[kind])
        if start - now > MAX_QUEUE_WAIT:
            raise ScryfallBusy(start - now)
        _next_slot[kind] = start + gap
    wait = start - time.time()
    if wait > 0:
        time.sleep(wait)
    r = requests.request(method, API + path, headers=HEADERS, timeout=timeout, **kwargs)
    if r.status_code == 429:              # we were told to back off: do so for a while
        with _gate:
            _blocked_until = time.time() + 35
        raise ScryfallBusy(35)
    return r


_PRINT_CACHE = {}
_SEARCH_LOCKS = {}
_SEARCH_LOCKS_GUARD = threading.Lock()


def search_mtg(name):
    """Return a list of candidate printings from Scryfall."""
    key = name.strip().lower()
    if key in _PRINT_CACHE:                # asked before: no need to bother Scryfall again
        return [dict(m) for m in _PRINT_CACHE[key]]
    with _SEARCH_LOCKS_GUARD:              # two threads asking for the same card share one call
        lock = _SEARCH_LOCKS.setdefault(key, threading.Lock())
    with lock:
        if key in _PRINT_CACHE:
            return [dict(m) for m in _PRINT_CACHE[key]]
        sort = {"unique": "prints", "order": "released"}
        r = scryfall("GET", "/cards/search", params={"q": f'!"{name}"', **sort})
        if r.status_code == 404:  # no exact match -> try fuzzy (forgives typos)
            r = scryfall("GET", "/cards/named", params={"fuzzy": name})
            if r.status_code == 200:
                # re-search using the corrected name so we get every printing
                fixed = r.json().get("name", name)
                r2 = scryfall("GET", "/cards/search", params={"q": f'!"{fixed}"', **sort})
                data = r2.json().get("data", []) if r2.status_code == 200 else [r.json()]
            else:
                # last resort: any card whose name contains the words we read
                r3 = scryfall("GET", "/cards/search", params={"q": name, **sort})
                if r3.status_code != 200:
                    return []
                data = r3.json().get("data", [])
        else:
            r.raise_for_status()
            data = r.json().get("data", [])
        out = [_parse_scryfall(c) for c in data[:15]]
        if out:
            if len(_PRINT_CACHE) > 60:
                _PRINT_CACHE.clear()
            _PRINT_CACHE[key] = [dict(m) for m in out]
        return out


def apply_finish(card, finish):
    card["finish"] = finish
    nf, fo = card["price_nonfoil"], card["price_foil"]
    card["price"] = (fo or nf) if finish == "foil" else (nf or fo)
    return card


def card_by_name(name, exact=True):
    """One Scryfall card record for a name (or None)."""
    r = scryfall("GET", "/cards/named", params={"exact" if exact else "fuzzy": name})
    return r.json() if r.status_code == 200 else None


def cards_by_names(names):
    """Many cards in ONE request -> {card name: record}."""
    names = list(dict.fromkeys(n for n in names if n))[:75]
    if not names:
        return {}
    r = scryfall("POST", "/cards/collection", json={"identifiers": [{"name": n} for n in names]})
    if r.status_code != 200:
        return {}
    return {c["name"]: c for c in r.json().get("data", [])}


def card_by_set_number(set_code, number):
    """The exact printing from a set code and collector number, e.g. tla / 58."""
    r = scryfall("GET", f"/cards/{quote(set_code.lower(), safe='')}/{quote(number.lower(), safe='')}")
    return _parse_scryfall(r.json()) if r.status_code == 200 else None


SET_NUMBER_RE = re.compile(r"^\s*([A-Za-z0-9]{2,6})\s*[ /#:\-]\s*(\d{1,4}[A-Za-z★]?)\s*$")


def parse_set_number(text):
    """'TLA 58' / 'tla/58' / 'tla #58' -> ('tla', '58'), otherwise None."""
    m = SET_NUMBER_RE.match(text)
    return (m.group(1).lower(), m.group(2).lower()) if m else None


def scryfall_autocomplete(text):
    r = scryfall("GET", "/cards/autocomplete", params={"q": text})
    return r.json().get("data", []) if r.status_code == 200 else []


def fetch_bytes(url):
    """Download a file from Scryfall's image server (which has no rate limit)."""
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


_IMG_CACHE = {}


def fetch_small(url):
    """A small decoded copy of an artwork picture (cached, so it is only fetched once)."""
    if url in _IMG_CACHE:
        return _IMG_CACHE[url]
    img = decode_image(fetch_bytes(url))
    if img is None:
        return None
    img = cv2.resize(img, (96, 72), interpolation=cv2.INTER_AREA)
    if len(_IMG_CACHE) > 400:
        _IMG_CACHE.clear()
    _IMG_CACHE[url] = img
    return img


# ------------------------------------------------------------------ updates
RELEASE_ASSET_SUFFIX = "-Setup.exe"
REPO_RE = re.compile(r"^[A-Za-z0-9_.-]{1,100}/[A-Za-z0-9_.-]{1,100}$")


class UpdateError(Exception):
    """A problem checking for or installing an update, in words a person can read."""


def parse_version(text):
    return tuple(int(x) for x in re.findall(r"\d+", text or ""))


def find_update(repo, current):
    """Ask GitHub for the newest release of `repo`. Returns None when `current` is
    up to date, otherwise {"version", "url", "size", "sha256", "notes"}."""
    if not REPO_RE.match(repo or ""):
        raise UpdateError("This copy doesn't know where to look for updates. Open Settings "
                          "and type your GitHub address (like yourname/your-repo).")
    try:
        r = requests.get(f"https://api.github.com/repos/{repo}/releases/latest",
                         headers={"User-Agent": HEADERS["User-Agent"],
                                  "Accept": "application/vnd.github+json"}, timeout=12)
    except requests.RequestException:
        raise UpdateError("Couldn't reach GitHub - check your internet connection.") from None
    if r.status_code == 404:
        raise UpdateError("No release found. The GitHub repository must be public, and its "
                          "build must have finished successfully.")
    if r.status_code in (403, 429):
        raise UpdateError("GitHub asked us to try again later. Wait a few minutes.")
    if r.status_code != 200:
        raise UpdateError(f"GitHub answered with an error ({r.status_code}).")
    data = r.json()
    latest = str(data.get("tag_name", "")).lstrip("vV")
    if not parse_version(latest) or parse_version(latest) <= parse_version(current):
        return None
    prefix = f"https://github.com/{repo}/releases/download/"
    for a in data.get("assets", []):
        url = str(a.get("browser_download_url", ""))
        if str(a.get("name", "")).endswith(RELEASE_ASSET_SUFFIX) and url.startswith(prefix):
            digest = str(a.get("digest") or "")
            return {"version": latest, "url": url, "size": int(a.get("size") or 0),
                    "sha256": digest.split(":", 1)[1].lower() if digest.startswith("sha256:") else "",
                    "notes": str(data.get("body") or "").strip()[:700]}
    raise UpdateError("The newest release has no installer attached yet. Try again in a few minutes.")


def download_update(info, progress=None):
    """Download the installer and check it is complete (and matches its checksum when
    GitHub provides one). Returns the file's path."""
    dest = Path(tempfile.mkdtemp(prefix="mtg_update_")) / "MTG-Card-Scanner-Setup.exe"
    digest, got = hashlib.sha256(), 0
    try:
        with requests.get(info["url"], headers={"User-Agent": HEADERS["User-Agent"]},
                          stream=True, timeout=30) as r:
            r.raise_for_status()
            total = int(r.headers.get("Content-Length") or info.get("size") or 0)
            with open(dest, "wb") as f:
                for chunk in r.iter_content(65536):
                    f.write(chunk)
                    digest.update(chunk)
                    got += len(chunk)
                    if progress and total:
                        progress(min(1.0, got / total))
    except requests.RequestException:
        raise UpdateError("The download was interrupted. Check your connection and try again.") from None
    if info.get("size") and got != info["size"]:
        raise UpdateError("The download was incomplete, so it was not installed.")
    if info.get("sha256") and digest.hexdigest() != info["sha256"]:
        raise UpdateError("The download didn't match its checksum, so it was not installed.")
    with open(dest, "rb") as f:
        if f.read(2) != b"MZ":
            raise UpdateError("The downloaded file isn't a Windows installer, so it was not run.")
    return dest


def launch_installer(path):
    """Start the installer (it closes this app, upgrades it in place, and reopens it)."""
    subprocess.Popen([str(path), "/SILENT", "/CLOSEAPPLICATIONS", "/NORESTART",
                      "/SUPPRESSMSGBOXES"], close_fds=True)


# ---------------------------------------------------------------- key binds
# (id, what it does, default key). Keys are stored as Tk key names, e.g. "space",
# "Control-e", "F5". An empty string means "not assigned".
ACTIONS = [
    ("snap", "Snap a card with the camera", "space"),
    ("auto", "Switch Manual / Auto capture", "a"),
    ("finish", "Switch new scans Non-foil / Foil", "t"),
    ("phone", "Open the phone link", "p"),
    ("photo", "Add from a photo file", "o"),
    ("add_name", "Add by name or number", "n"),
    ("qty_up", "+1 on the selected cards", "plus"),
    ("qty_down", "-1 on the selected cards", "minus"),
    ("flip", "Switch the selected cards foil / non-foil", "f"),
    ("remove", "Remove the selected cards", "Delete"),
    ("export_view", "Export the current view", "Control-e"),
    ("export_all", "Export all cards", ""),
    ("settings", "Open Settings", "Control-comma"),
    ("update", "Check for updates", ""),
    ("exit", "Exit the app", "Control-q"),
]
DEFAULT_KEYS = {a: k for a, _, k in ACTIONS}
ACTION_LABELS = {a: label for a, label, _ in ACTIONS}
_MODIFIER_KEYS = {"Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R", "Meta_L",
                  "Meta_R", "Caps_Lock", "Num_Lock", "Super_L", "Super_R", "ISO_Level3_Shift"}
_RESERVED_KEYS = {"Tab", "Return", "Escape", "Up", "Down", "Left", "Right", "Prior", "Next",
                  "Home", "End"}
_KEY_NAMES = {"space": "Space", "plus": "+", "minus": "-", "equal": "=", "comma": ",",
              "period": ".", "Delete": "Delete", "BackSpace": "Backspace", "Insert": "Insert"}


def format_key(key):
    if not key:
        return "(none)"
    *mods, sym = key.split("-")
    name = _KEY_NAMES.get(sym, sym.upper() if len(sym) == 1 else sym)
    return "+".join([("Ctrl" if m == "Control" else m) for m in mods] + [name])


def key_has_modifier(key):
    *mods, sym = key.split("-")
    return bool(mods) or (sym[:1] == "F" and sym[1:].isdigit())


def key_patterns(key):
    """The Tk binding strings for a stored key (letters work with Caps Lock too, and
    the plus / minus keys also answer to = and the number pad)."""
    *mods, sym = key.split("-")
    syms = [sym.lower(), sym.upper()] if len(sym) == 1 and sym.isalpha() else [sym]
    syms += {"plus": ["equal", "KP_Add"], "minus": ["KP_Subtract"]}.get(sym, [])
    return ["<" + "-".join(mods + ["Key", x]) + ">" for x in syms]


def event_to_key(event):
    """A key press -> stored key text, or None for a bare modifier / unusable key."""
    sym = event.keysym
    if sym in _MODIFIER_KEYS:
        return None
    mods = []
    if event.state & 0x4:
        mods.append("Control")
    if event.state & (0x20000 if os.name == "nt" else 0x8):
        mods.append("Alt")
    if len(sym) == 1 and sym.isalpha():
        sym = sym.lower()
    if sym in _RESERVED_KEYS and not mods:
        return "reserved"
    return "-".join(mods + [sym])


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
        if names:
            self.build(names)              # use the saved list right away...
        if not names or (age is not None and age > 14 * 86400):
            try:                           # ...and refresh it in the background if old
                r = scryfall("GET", "/catalog/card-names", timeout=60)
                r.raise_for_status()
                fresh = r.json().get("data", [])
                if fresh:
                    save_json(self.path, {"fetched": time.time(), "names": fresh})
                    if not names:
                        self.build(fresh)
            except Exception:
                pass

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
    """Yield (text, confidence) reads of the title, trying several image treatments,
    cheapest first. A generator so the caller can stop as soon as a read is good."""
    if not ocr_available():
        return
    h, w = card.shape[:2]
    strip = card[int(h * 0.02):int(h * 0.12), int(w * 0.05):int(w * 0.80)]
    strip = cv2.resize(strip, None, fx=2.5, fy=2.5, interpolation=cv2.INTER_CUBIC)
    gray = cv2.cvtColor(strip, cv2.COLOR_BGR2GRAY)
    clahe = cv2.createCLAHE(clipLimit=3.0, tileGridSize=(4, 4)).apply(gray)

    def plain():
        return strip

    def contrast():
        return cv2.cvtColor(clahe, cv2.COLOR_GRAY2BGR)

    def denoised_sharp():
        try:
            den = cv2.fastNlMeansDenoising(clahe, None, 6, 7, 21)
        except cv2.error:
            den = clahe
        soft = cv2.GaussianBlur(den, (0, 0), 2.5)
        return cv2.cvtColor(cv2.addWeighted(den, 1.8, soft, -0.8, 0), cv2.COLOR_GRAY2BGR)

    def inverted():                      # light-on-dark titles
        return cv2.cvtColor(255 - clahe, cv2.COLOR_GRAY2BGR)

    for make in (plain, contrast, denoised_sharp, inverted)[:treatments]:
        text, conf = _ocr_once(make())
        if text:
            yield text, conf


def recognize(cards, catalog, debug_dir=None, online=True, emit=None):
    """Work out which card this is. cards: straightened pictures, sharpest first.
    emit(kind, value) is called as results arrive so the screen can update early:
      "names" - text-only guesses (fast), "art" - guesses with artwork.
    Returns {"reads": [...], "cands": [{name, final, name_score, art_score, art_bytes}],
    "notes": [problems worth telling the user about]}"""
    emit = emit or (lambda kind, value: None)
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

    notes = []
    scores = dict(catalog.rank(reads, limit=10)) if catalog.ready else {}
    if reads and online and (not catalog.ready or max(scores.values(), default=0.0) < 0.7):
        best_text = max(reads, key=lambda r: r[1])[0]
        try:   # the local name list is unsure (or not loaded yet): ask Scryfall too
            if not catalog.ready:
                for i, nm in enumerate(scryfall_autocomplete(best_text)[:6]):
                    scores.setdefault(nm, 0.6 - 0.02 * i)
            hit = card_by_name(best_text, exact=False)
            if hit:
                scores[hit["name"]] = max(scores.get(hit["name"], 0.0), 0.8)
        except ScryfallBusy as e:
            notes.append(str(e))
        except Exception:
            pass

    ranked = sorted(scores.items(), key=lambda kv: -kv[1])[:6]
    cands = [{"name": n, "name_score": s, "art_score": None, "final": s, "art_bytes": None}
             for n, s in ranked]
    emit("names", {"cands": [dict(c) for c in cands], "reads": list(reads)})

    photo_art = art_region(prepared[0]) if prepared else None
    if cands and online and prepared:      # compare artwork like a visual search would
        try:                               # ONE request covers every guess
            recs = cards_by_names([c["name"] for c in cands])
        except ScryfallBusy as e:
            recs = {}
            notes.append(str(e))
        except Exception:
            recs = {}

        def look(c):                       # artwork files come from a server with no limits
            try:
                rec = recs.get(c["name"])
                if not rec:
                    return
                url = _art_url(rec)
                blob = fetch_bytes(url)
                img = decode_image(blob)
                if img is None:
                    return
                c["art_bytes"] = blob
                c["art_score"] = art_similarity(photo_art, img)
            except Exception:
                return

        with ThreadPoolExecutor(max_workers=6) as ex:
            list(ex.map(look, cands))
        for c in cands:
            if c["art_score"] is not None:
                c["final"] = min(1.0, 0.65 * c["name_score"] + 0.35 * c["art_score"])
        cands.sort(key=lambda c: -c["final"])
        emit("art", {"cands": [dict(c) for c in cands]})

    if cands and online and photo_art is not None:   # get the printings ready before they're asked for
        try:
            ms = search_mtg(cands[0]["name"])
            if len(ms) > 1:
                rank_printings_by_art(photo_art, ms)
        except Exception:
            pass

    if debug_dir:
        try:
            save_debug(debug_dir, cards, reads, cands)
        except Exception:
            pass
    return {"reads": reads, "cands": cands, "notes": notes}


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
        img = fetch_small(url)
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


def money(v):
    return f"${v:,.2f}"


def write_export(path, rows, header_lines):
    total = sum(line_total(c) for c in rows)
    count = sum(c["qty"] for c in rows)
    name_w = max([len(c["name"]) for c in rows] + [4])
    set_w = max([len(c["set"]) for c in rows] + [3])
    type_w = max([len(main_type(c)) for c in rows] + [4])
    col_w = max([len(color_text(c)) for c in rows] + [5])
    line_w = name_w + set_w + type_w + col_w + 56

    with open(path, "w", encoding="utf-8") as f:
        f.write("MTG card collection export\n")
        for h in header_lines:
            f.write(h + "\n")
        f.write("=" * line_w + "\n")
        f.write(f"{'#':>3}  {'Qty':>3}  {'Name':<{name_w}}  {'Type':<{type_w}}  "
                f"{'Color':<{col_w}}  {'Set':<{set_w}}  {'Finish':<8} {'Each':>9} {'Total':>10}\n")
        f.write("-" * line_w + "\n")
        for i, c in enumerate(rows, 1):
            each = money(c["price"]) if c["price"] else "n/a"
            tot = money(line_total(c)) if c["price"] else "n/a"
            f.write(f"{i:>3}  {c['qty']:>3}  {c['name']:<{name_w}}  {main_type(c):<{type_w}}  "
                    f"{color_text(c):<{col_w}}  {c['set']:<{set_w}}  "
                    f"{finish_text(c):<8} {each:>9} {tot:>10}\n")
        f.write("-" * line_w + "\n")
        f.write(f"{count} cards ({len(rows)} different), total value {money(total)}\n")


# ------------------------------------------------------------------ webcam
class CameraStream:
    """Reads the webcam in a background thread, so the window never waits on it
    (opening a camera can take a few seconds) and always shows the newest frame."""

    def __init__(self, index, width, height, autofocus, focus):
        self.index, self.width, self.height = index, width, height
        self.autofocus, self.focus = autofocus, focus
        self.state = "opening"                  # opening | live | none | lost
        self._frame, self._seq = None, 0
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._cmds = queue.Queue()
        threading.Thread(target=self._run, daemon=True).start()

    @staticmethod
    def _open(idx):
        cap = cv2.VideoCapture(idx, cv2.CAP_DSHOW) if os.name == "nt" else cv2.VideoCapture(idx)
        if cap is not None and cap.isOpened():
            return cap
        if cap is not None:
            cap.release()
        return None

    def _apply_focus(self, cap, auto, value):
        try:  # not every camera supports these; failures are harmless
            cap.set(cv2.CAP_PROP_AUTOFOCUS, 1 if auto else 0)
            if not auto:
                cap.set(cv2.CAP_PROP_FOCUS, float(value))
        except Exception:
            pass

    def _run(self):
        cap = self._open(self.index)
        if cap is None:                          # try the other camera numbers too
            for i in range(4):
                if i != self.index:
                    cap = self._open(i)
                    if cap is not None:
                        self.index = i
                        break
        if cap is None:
            self.state = "none"
            return
        try:
            cap.set(cv2.CAP_PROP_FOURCC, cv2.VideoWriter_fourcc(*"MJPG"))
            cap.set(cv2.CAP_PROP_FRAME_WIDTH, self.width)
            cap.set(cv2.CAP_PROP_FRAME_HEIGHT, self.height)
        except Exception:
            pass
        self._apply_focus(cap, self.autofocus, self.focus)
        self.state = "live"
        misses = 0
        while not self._stop.is_set():
            self._do_commands(cap)
            ok, frame = cap.read()
            if ok and frame is not None:
                misses = 0
                with self._lock:
                    self._frame = frame
                    self._seq += 1
            else:
                misses += 1
                if misses > 150:
                    self.state = "lost"
                    break
                time.sleep(0.02)
        cap.release()

    def _do_commands(self, cap):
        while True:
            try:
                cmd = self._cmds.get_nowait()
            except queue.Empty:
                return
            try:
                if cmd[0] == "focus":
                    self._apply_focus(cap, cmd[1], cmd[2])
                elif cmd[0] == "settings":
                    cap.set(cv2.CAP_PROP_SETTINGS, 1)
            except Exception:
                pass

    def send(self, *cmd):
        self._cmds.put(cmd)

    def latest(self):
        with self._lock:
            return self._frame, self._seq

    def stop(self):
        self._stop.set()


# -------------------------------------------------------------- phone link
PHONE_PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>MTG Card Scanner</title>
<style>
 :root{color-scheme:dark}
 *{box-sizing:border-box}
 body{margin:0;font-family:system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;background:#13151b;color:#e9ebf2;text-align:center}
 .wrap{padding:14px 16px 24px;max-width:560px;margin:0 auto}
 h1{font-size:20px;margin:6px 0 2px}
 p{color:#8f96a8;line-height:1.4;margin:6px 0 12px;font-size:15px}
 #stage{position:relative;background:#000;border-radius:14px;overflow:hidden;display:none}
 video{width:100%;display:block;max-height:68vh;object-fit:cover}
 #guide{position:absolute;border:3px solid #e1e1e1;border-radius:10px;pointer-events:none;transition:border-color .15s}
 #pill{position:absolute;left:10px;right:10px;bottom:10px;padding:8px 10px;border-radius:999px;background:#252938;color:#c8cddc;font-weight:700;font-size:15px}
 #pill.good{background:#38d996;color:#0d1117}#pill.warn{background:#ffb547;color:#0d1117}
 button,label.btn{display:block;width:100%;border:0;background:#6d8bff;color:#fff;font-weight:700;font-size:18px;padding:16px;border-radius:14px;margin:10px 0;font-family:inherit}
 .alt{background:#252938!important;color:#c8cddc!important;font-size:15px!important;padding:12px!important;font-weight:600!important}
 #msg{font-size:17px;min-height:26px;margin:8px 0}
 .ok{color:#38d996}.warn{color:#ffb547}
 #sent{max-width:60%;max-height:20vh;border-radius:8px;margin:4px auto;display:none}
</style></head><body><div class="wrap">
<h1>MTG Card Scanner</h1>
<p id="intro">Starting the camera...</p>
<div id="stage"><video id="v" playsinline muted autoplay></video><div id="guide"></div><div id="pill">Starting...</div></div>
<button id="now" class="alt" style="display:none">Send now</button>
<div id="msg"></div>
<img id="sent" alt="">
<label class="btn alt">Take a photo with the camera app<input id="cam" type="file" accept="image/*" capture="environment" hidden></label>
<label class="btn alt">Choose a saved photo<input id="pick" type="file" accept="image/*" hidden></label>
</div>
<canvas id="c" width="96" height="96" hidden></canvas>
<script>
const base = location.pathname.replace(/\/?$/, "/");
const $ = id => document.getElementById(id);
const msg = $("msg"), pill = $("pill"), guide = $("guide"), video = $("v");
function say(t, cls){ msg.textContent = t; msg.className = cls || ""; }
function setPill(t, cls){ pill.textContent = t; pill.className = cls || ""; guide.style.borderColor = cls === "good" ? "#38d996" : cls === "warn" ? "#ffb547" : "#e1e1e1"; }

let busy = false;            // a card is waiting for your OK on the computer
async function upload(blob, live, thumb){
  busy = true;
  if(thumb){ $("sent").src = thumb; $("sent").style.display = "block"; }
  say("Sending...");
  try{
    const r = await fetch(base + "upload?live=" + (live ? 1 : 0), {method: "POST", body: blob});
    const j = await r.json();
    if(!r.ok) throw new Error(j.error || "upload failed");
    say("Sent! Confirm it on the computer.", "ok");
    poll(j.id);
  }catch(e){ say("Couldn't send: " + e.message, "warn"); busy = false; }
}
async function poll(id){
  for(let i = 0; i < 900; i++){
    await new Promise(r => setTimeout(r, 1000));
    try{
      const j = await (await fetch(base + "status?id=" + id)).json();
      if(j.state === "added"){ say("Added: " + j.text + "  - next card!", "ok"); done(); return; }
      if(j.state === "skipped"){ say("Skipped. Show the next card.", "warn"); done(); return; }
    }catch(e){}
  }
  done();
}
function done(){ busy = false; waitGone = true; goneCount = 0; still = 0; }
function fileSend(f){ if(f){ upload(f, false, URL.createObjectURL(f)); } }
for(const id of ["cam", "pick"]) $(id).addEventListener("change", e => { fileSend(e.target.files[0]); e.target.value = ""; });

// ---------------- live camera: watches for a sharp, still card, then sends one frame
const W = 96, H = 96, cv = $("c"), cx = cv.getContext("2d", {willReadFrequently: true});
let prev = null, still = 0, bestSharp = 0, waitGone = false, goneCount = 0, refFrame = null, sharpHist = [];
let g = {x: 0, y: 0, w: 1, h: 1};     // card-shaped guide in video pixels

function layoutGuide(){
  const vw = video.videoWidth, vh = video.videoHeight; if(!vw) return;
  const bw0 = vh * 0.92 * 63 / 88, bw = Math.min(vw, bw0), bh = bw === bw0 ? vh * 0.92 : bw * 88 / 63;
  g = {x: (vw - bw) / 2, y: (vh - bh) / 2, w: bw, h: bh};
  const r = video.getBoundingClientRect(), s = Math.max(r.width / vw, r.height / vh);
  const ox = (r.width - vw * s) / 2, oy = (r.height - vh * s) / 2;
  Object.assign(guide.style, {left: (ox + g.x * s) + "px", top: (oy + g.y * s) + "px", width: (g.w * s) + "px", height: (g.h * s) + "px"});
}
function sample(){            // small grayscale picture of the guide area
  cx.drawImage(video, g.x, g.y, g.w, g.h, 0, 0, W, H);
  const d = cx.getImageData(0, 0, W, H).data, a = new Float32Array(W * H);
  for(let i = 0; i < a.length; i++) a[i] = 0.299 * d[i*4] + 0.587 * d[i*4+1] + 0.114 * d[i*4+2];
  return a;
}
function analyze(a){
  let lap = 0, edges = 0, n = 0;
  for(let y = 1; y < H - 1; y++) for(let x = 1; x < W - 1; x++){
    const i = y * W + x, l = 4 * a[i] - a[i-1] - a[i+1] - a[i-W] - a[i+W];
    lap += l * l; n++;
    if(Math.abs(a[i+1] - a[i-1]) + Math.abs(a[i+W] - a[i-W]) > 40) edges++;
  }
  return {sharp: lap / n, edge: edges / n};
}
function diff(a, b){ let s = 0; for(let i = 0; i < a.length; i++) s += Math.abs(a[i] - b[i]); return s / a.length; }

function grab(){ // full-resolution frame -> jpeg
  const c = document.createElement("canvas"); c.width = video.videoWidth; c.height = video.videoHeight;
  c.getContext("2d").drawImage(video, 0, 0);
  return new Promise(res => c.toBlob(b => res({blob: b, thumb: c.toDataURL("image/jpeg", 0.3)}), "image/jpeg", 0.92));
}
async function sendNow(){
  if(busy) return;
  const f = await grab(); refFrame = sample();
  upload(f.blob, true, f.thumb);
}
$("now").addEventListener("click", sendNow);

function tick(){
  if(!video.videoWidth) return;
  layoutGuide();
  const a = sample(), m = analyze(a);
  sharpHist.push(m.sharp); if(sharpHist.length > 25) sharpHist.shift();
  const best = Math.max(...sharpHist);
  const moved = prev ? diff(a, prev) : 99; prev = a;
  if(busy){ setPill("Waiting for you to confirm on the computer", ""); return; }
  if(waitGone){
    const changed = refFrame ? diff(a, refFrame) : 99;
    goneCount = (changed > 14 || m.edge < 0.04) ? goneCount + 1 : 0;
    if(goneCount >= 6){ waitGone = false; sharpHist = []; }
    else { setPill("Remove the card to scan the next one", ""); return; }
  }
  if(m.edge < 0.07){ still = 0; setPill("Hold a card inside the frame", ""); return; }
  if(moved > 5){ still = 0; setPill("Hold still...", "warn"); return; }
  if(m.sharp < 0.85 * best || m.sharp < 25){ still = 0; setPill("Not sharp yet - hold steady", "warn"); return; }
  still++;
  setPill("Hold still...  " + Math.min(100, Math.round(still * 100 / 6)) + "%", "good");
  if(still >= 6){ still = 0; setPill("Captured!", "good"); sendNow(); }
}

async function startCamera(){
  if(!window.isSecureContext || !navigator.mediaDevices || !navigator.mediaDevices.getUserMedia){
    $("intro").textContent = "Live camera needs the secure link, so use the photo buttons below.";
    return;
  }
  try{
    const s = await navigator.mediaDevices.getUserMedia({audio: false, video: {
      facingMode: {ideal: "environment"}, width: {ideal: 1920}, height: {ideal: 1080}}});
    video.srcObject = s; await video.play();
    $("stage").style.display = "block"; $("now").style.display = "block";
    $("intro").textContent = "Put a card inside the frame and hold it still. It is sent automatically, and you confirm it on the computer.";
    try{ const t = s.getVideoTracks()[0]; t.applyConstraints({advanced: [{focusMode: "continuous"}]}).catch(() => {}); }catch(e){}
    try{ if(navigator.wakeLock) navigator.wakeLock.request("screen").catch(() => {}); }catch(e){}
    setInterval(tick, 110);
    document.addEventListener("visibilitychange", () => { if(!document.hidden && navigator.wakeLock) navigator.wakeLock.request("screen").catch(() => {}); });
  }catch(e){
    $("intro").textContent = "Couldn't open the camera (" + (e.name || "error") + "). Allow camera access for this page, or use the photo buttons below.";
  }
}
startCamera();
</script></body></html>
"""


def lan_ip():
    """This computer's address on the home network (what a phone must connect to)."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))           # no data is sent; it just picks the right network
        return s.getsockname()[0]
    except OSError:
        try:
            return socket.gethostbyname(socket.gethostname())
        except OSError:
            return "127.0.0.1"
    finally:
        s.close()


def make_qr_image(text, box=8):
    """A QR code as a picture (PIL image), or None if this OpenCV can't make one."""
    try:
        enc = (cv2.QRCodeEncoder.create() if hasattr(cv2.QRCodeEncoder, "create")
               else cv2.QRCodeEncoder_create())
        qr = enc.encode(text)
        if qr is None or qr.size == 0:
            return None
        qr = cv2.copyMakeBorder(qr, 4, 4, 4, 4, cv2.BORDER_CONSTANT, value=255)
        qr = cv2.resize(qr, None, fx=box, fy=box, interpolation=cv2.INTER_NEAREST)
        return Image.fromarray(qr).convert("RGB")
    except Exception:
        return None


CERT_DIR = DATA_DIR / "PhoneCertificate"


def ensure_certificate(ip, folder=None):
    """A self-signed certificate (so the phone can use https and open its camera).
    It is created once, kept in your files, and remade only if this PC's address changes.
    Returns (certificate file, key file)."""
    import ipaddress
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import rsa
    from cryptography.x509.oid import NameOID

    folder = Path(folder or CERT_DIR)
    folder.mkdir(parents=True, exist_ok=True)
    crt, key, meta = folder / "cert.pem", folder / "key.pem", folder / "meta.json"
    info = load_json(meta, {})
    fresh = False
    try:
        fresh = (crt.exists() and key.exists() and info.get("ip") == ip
                 and time.time() < float(info.get("expires", 0)))
    except (TypeError, ValueError):
        fresh = False
    if fresh:
        return crt, key
    private = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, "MTG Card Scanner")])
    now = datetime.datetime.now(datetime.timezone.utc)
    expires = now + datetime.timedelta(days=800)
    sans = [x509.DNSName("localhost"), x509.IPAddress(ipaddress.ip_address("127.0.0.1"))]
    try:
        sans.append(x509.IPAddress(ipaddress.ip_address(ip)))
    except ValueError:
        pass
    cert = (x509.CertificateBuilder().subject_name(name).issuer_name(name)
            .public_key(private.public_key()).serial_number(x509.random_serial_number())
            .not_valid_before(now - datetime.timedelta(days=1)).not_valid_after(expires)
            .add_extension(x509.SubjectAlternativeName(sans), critical=False)
            .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
            .sign(private, hashes.SHA256()))
    crt.write_bytes(cert.public_bytes(serialization.Encoding.PEM))
    key.write_bytes(private.private_bytes(
        serialization.Encoding.PEM, serialization.PrivateFormat.TraditionalOpenSSL,
        serialization.NoEncryption()))
    save_json(meta, {"ip": ip, "expires": expires.timestamp() - 86400})
    return crt, key


class PhoneLink:
    """A tiny web page served from this PC. A phone on the same Wi-Fi opens it (via a
    QR code); the page watches the phone camera and, when a card is sharp and still,
    sends one full-resolution frame, which lands in `incoming`.
    It uses https (needed for the phone's camera). If a certificate can't be made it
    falls back to plain http, where the phone can only send photos."""
    MAX_BYTES = 40 * 1024 * 1024

    def __init__(self, cert_dir=None):
        self.token = secrets.token_urlsafe(9)     # makes the address impossible to guess
        self.incoming = queue.Queue()             # (job id, picture, came from live view?)
        self.status = {}                          # job id -> {"state", "text"}
        self.received = 0
        self.secure = False
        self.warning = ""
        self._next_id = 1
        self._lock = threading.Lock()
        self._cert_dir = cert_dir
        self.server = None
        self.url = ""

    def new_job(self, img, live=False):
        with self._lock:
            job = self._next_id
            self._next_id += 1
            self.status[job] = {"state": "waiting", "text": ""}
            self.received += 1
        self.incoming.put((job, img, live))
        return job

    def set_status(self, job, state, text=""):
        with self._lock:
            self.status[job] = {"state": state, "text": text}

    def get_status(self, job):
        with self._lock:
            return dict(self.status.get(job, {"state": "unknown", "text": ""}))

    def start(self):
        import ssl
        link = self
        base = f"/s/{self.token}/"
        ip = lan_ip()

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *args, **kwargs):
                pass

            def _reply(self, code, body, ctype="application/json"):
                data = body if isinstance(body, bytes) else body.encode("utf-8")
                self.send_response(code)
                self.send_header("Content-Type", ctype)
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Cache-Control", "no-store")
                self.end_headers()
                self.wfile.write(data)

            def do_GET(self):
                u = urlparse(self.path)
                if u.path.rstrip("/") == base.rstrip("/"):
                    self._reply(200, PHONE_PAGE, "text/html; charset=utf-8")
                elif u.path == base + "status":
                    try:
                        job = int(parse_qs(u.query).get("id", ["0"])[0])
                    except ValueError:
                        job = 0
                    self._reply(200, json.dumps(link.get_status(job)))
                else:
                    self._reply(404, '{"error": "not found"}')

            def do_POST(self):
                u = urlparse(self.path)
                if u.path != base + "upload":
                    self._reply(404, '{"error": "not found"}')
                    return
                try:
                    n = int(self.headers.get("Content-Length", "0"))
                except ValueError:
                    n = 0
                if n <= 0 or n > link.MAX_BYTES:
                    self._reply(413, '{"error": "picture too big or empty"}')
                    return
                data = self.rfile.read(n)
                img = cv2.imdecode(np.frombuffer(data, np.uint8), cv2.IMREAD_COLOR)
                if img is None:
                    self._reply(400, '{"error": "that does not look like a picture"}')
                    return
                live = parse_qs(u.query).get("live", ["0"])[0] == "1"
                self._reply(200, json.dumps({"id": link.new_job(img, live)}))

        ctx = None
        try:
            crt, key = ensure_certificate(ip, self._cert_dir)
            ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ctx.load_cert_chain(str(crt), str(key))
        except Exception as e:  # noqa: BLE001 - fall back to plain http, photos only
            ctx = None
            self.warning = f"Secure link unavailable ({type(e).__name__}); photos only."

        class Server(ThreadingHTTPServer):
            daemon_threads = True

            def get_request(self):
                sock, addr = self.socket.accept()
                if ctx is not None:      # the handshake happens in the worker thread, so a
                    sock = ctx.wrap_socket(sock, server_side=True,   # stalled phone can't block us
                                           do_handshake_on_connect=False)
                return sock, addr

            def handle_error(self, request, client_address):
                pass                     # phones drop connections while accepting the certificate

        server = None
        for port in (8765, 8766, 8767, 0):
            try:
                server = Server(("0.0.0.0", port), Handler)
                break
            except OSError:
                continue
        if server is None:
            raise OSError("couldn't open a network port")
        self.server = server
        self.secure = ctx is not None
        self.url = f"{'https' if self.secure else 'http'}://{ip}:{server.server_address[1]}{base}"
        threading.Thread(target=lambda: server.serve_forever(poll_interval=0.2),
                         daemon=True).start()

    def stop(self):
        if self.server is not None:
            threading.Thread(target=self.server.shutdown, daemon=True).start()
            try:
                self.server.server_close()
            except Exception:
                pass
            self.server = None


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


def center_on(win, parent):
    win.update_idletasks()
    try:
        x = parent.winfo_rootx() + (parent.winfo_width() - win.winfo_width()) // 2
        y = parent.winfo_rooty() + (parent.winfo_height() - win.winfo_height()) // 2
        win.geometry(f"+{max(x, 0)}+{max(y, 0)}")
    except tk.TclError:
        pass


# ------------------------------------------------------------ add-card popup
class AddCardDialog(tk.Toplevel):
    """Shown after a snap: reads the card, lists the best guesses with artwork,
    lets you pick the printing, finish and quantity - or find it by set + number."""

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
        self._typed = False
        self._suggest_after = None
        self.name_var = tk.StringVar()
        self.finish_var = tk.StringVar(value=finish)
        self.value_var = tk.StringVar()
        self.qty_var = tk.StringVar(value="1")
        self.set_var = tk.StringVar()
        self.num_var = tk.StringVar()
        self.msg_var = tk.StringVar()
        self.photo_art = art_region(enhance(cards[0])) if cards else None

        body = ttk.Frame(self, padding=18)
        body.pack(fill="both", expand=True)

        # ---- left: what the camera saw
        left = ttk.Frame(body, style="Panel.TFrame", padding=12)
        left.grid(row=0, column=0, sticky="n", padx=(0, 18))
        if cards:
            pil = Image.fromarray(cv2.cvtColor(cards[0], cv2.COLOR_BGR2RGB))
            pil.thumbnail((240, 336))
            self._photo = ImageTk.PhotoImage(pil)
            ttk.Label(left, image=self._photo, style="Panel.TLabel").pack()
            ttk.Label(left, text="Your photo, straightened",
                      style="PanelMuted.TLabel").pack(pady=(8, 0))
        else:
            ttk.Label(left, text="Type a card name,\nor a set code and number,\nto add it by hand",
                      style="PanelMuted.TLabel", justify="center").pack(padx=36, pady=120)

        # ---- right: name, guesses, printings
        right = ttk.Frame(body)
        right.grid(row=0, column=1, sticky="nsew")

        ttk.Label(right, text="Card name  (or set code + number, like TLA 58)",
                  style="Section.TLabel").pack(anchor="w")
        row = ttk.Frame(right)
        row.pack(fill="x", pady=(4, 0))
        self.entry = ttk.Entry(row, textvariable=self.name_var, width=44, font=F(12))
        self.entry.pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Search", command=self.search).pack(side="left", padx=(8, 0))
        ttk.Label(right, textvariable=self.msg_var, style="Muted.TLabel",
                  wraplength=580, justify="left").pack(anchor="w", pady=(8, 6))

        ttk.Label(right, text="Best guesses", style="Section.TLabel").pack(anchor="w")
        cf = ttk.Frame(right, style="Panel.TFrame")
        cf.pack(fill="x", pady=(4, 8))
        self.cand_tree = ttk.Treeview(cf, columns=("pct", "detail"), show="tree", height=3,
                                      style="Cand.Treeview", selectmode="browse")
        self.cand_tree.column("#0", width=330, stretch=True)
        self.cand_tree.column("pct", width=60, anchor="e", stretch=False)
        self.cand_tree.column("detail", width=130, anchor="e", stretch=False)
        csb = ttk.Scrollbar(cf, orient="vertical", command=self.cand_tree.yview)
        self.cand_tree.configure(yscrollcommand=csb.set)
        self.cand_tree.pack(side="left", fill="x", expand=True)
        csb.pack(side="right", fill="y")

        ttk.Label(right, text="Printings", style="Section.TLabel").pack(anchor="w")
        pf = ttk.Frame(right, style="Panel.TFrame")
        pf.pack(fill="x", pady=(4, 8))
        cols = [("set", "Set", 230), ("num", "No.", 55), ("rarity", "Rarity", 75),
                ("nonfoil", "Non-foil", 75), ("foil", "Foil", 75)]
        self.tree = ttk.Treeview(pf, columns=[c[0] for c in cols], show="headings",
                                 height=4, selectmode="browse")
        for key, text, width in cols:
            self.tree.heading(key, text=text)
            self.tree.column(key, width=width, anchor="w" if key == "set" else "e")
        psb = ttk.Scrollbar(pf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=psb.set)
        self.tree.pack(side="left", fill="x", expand=True)
        psb.pack(side="right", fill="y")

        numrow = ttk.Frame(right)
        numrow.pack(fill="x", pady=(0, 8))
        ttk.Label(numrow, text="Or by the number printed on the card:",
                  style="Muted.TLabel").pack(side="left")
        ttk.Entry(numrow, textvariable=self.set_var, width=6).pack(side="left", padx=(8, 4))
        ttk.Label(numrow, text="set", style="Muted.TLabel").pack(side="left")
        ttk.Entry(numrow, textvariable=self.num_var, width=6).pack(side="left", padx=(8, 4))
        ttk.Label(numrow, text="no.", style="Muted.TLabel").pack(side="left")
        ttk.Button(numrow, text="Find", style="Small.TButton",
                   command=self.find_by_number).pack(side="left", padx=(8, 0))

        opts = ttk.Frame(right)
        opts.pack(fill="x", pady=(0, 10))
        ttk.Radiobutton(opts, text="Non-foil", value="nonfoil", variable=self.finish_var,
                        style="Seg.Toolbutton", takefocus=0).pack(side="left")
        ttk.Radiobutton(opts, text="Foil", value="foil", variable=self.finish_var,
                        style="Seg.Toolbutton", takefocus=0).pack(side="left", padx=(2, 0))
        ttk.Label(opts, text="Quantity", style="Muted.TLabel").pack(side="left", padx=(20, 6))
        ttk.Spinbox(opts, from_=1, to=999, width=4, textvariable=self.qty_var).pack(side="left")
        ttk.Label(opts, text="Custom value $", style="Muted.TLabel").pack(side="left", padx=(20, 6))
        ttk.Entry(opts, textvariable=self.value_var, width=7).pack(side="left")

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

        center_on(self, parent)
        try:
            self.wait_visibility()
            self.grab_set()
        except tk.TclError:
            pass
        self.entry.focus_set()

        if cards:
            self.msg_var.set("Reading the card...")
            self._stream(lambda emit: recognize(self.cards, self.catalog, self.debug_dir, emit=emit),
                         self._on_stage)
        else:
            self.msg_var.set("Type a few letters of the card name - suggestions appear as you type.")

    # ---------------------------------------------------------- background work
    def _alive(self):
        try:
            return bool(self.winfo_exists())
        except tk.TclError:
            return False

    def _stream(self, fn, handler):
        """Run fn(emit) in a thread. handler(kind, value) is called on the screen
        thread for each emit(...), then once with "done" (or "error")."""
        q = queue.Queue()

        def run():
            try:
                q.put(("done", fn(lambda kind, value: q.put((kind, value)))))
            except Exception as e:  # noqa: BLE001 - shown to the user, not hidden
                q.put(("error", e))

        threading.Thread(target=run, daemon=True).start()

        def poll():
            if not self._alive():
                return
            while True:
                try:
                    kind, val = q.get_nowait()
                except queue.Empty:
                    self.after(60, poll)
                    return
                handler(kind, val)
                if kind in ("done", "error"):
                    return

        self.after(60, poll)

    def _bg(self, fn, done):
        """Run fn in a thread; call done(ok, value) back on the screen thread."""
        def handler(kind, val):
            if kind == "done":
                done(True, val)
            elif kind == "error":
                done(False, val)
        self._stream(lambda emit: fn(), handler)

    def _on_stage(self, kind, val):
        if kind == "error":
            self.msg_var.set("Couldn't read the card automatically. Type a few letters of "
                             "the name, or use the set code and number.")
        elif kind == "names":
            self.cands = val["cands"]
            self._show_candidates(self.cands)
            if val["reads"] and not self._typed and not self.name_var.get().strip():
                self.name_var.set(max(val["reads"], key=lambda r: r[1])[0])
            if not self.cands:
                self.msg_var.set("Couldn't read this card clearly. Type a few letters of the "
                                 "name (suggestions appear as you type), or use the set code and number.")
            else:
                self.msg_var.set("Checking the artwork...")
        elif kind == "art":
            self.cands = val["cands"]
            self._show_candidates(self.cands)
            self._pick_top()
            self.msg_var.set("Best guess is highlighted. Not right? Pick another, or type the name.")
        elif kind == "done":
            if self.cands and not self.loaded_name:      # artwork never arrived: use the name guess
                self._pick_top()
            if val.get("notes"):
                self.msg_var.set(self.msg_var.get() + "  (Scryfall asked us to slow down, "
                                 "so some previews may be missing.)")

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
            detail = ""
            if c.get("name_score") is not None:
                art = c.get("art_score")
                detail = (f"name {int(round(c['name_score'] * 100))}  art "
                          + (f"{int(round(art * 100))}" if art is not None else "-"))
            self.cand_tree.insert("", "end", iid=str(i), text="  " + c["name"],
                                  image=img, values=(pct, detail))

    def _pick_top(self):
        """Highlight the best guess (unless the user has already taken over). The list is
        ordered by name AND artwork together, so the top row is the best overall."""
        if self._typed or not self.cands or self.cands[0].get("final") is None:
            return
        if self.cands[0]["final"] < 0.5:
            return
        self.cand_tree.selection_set("0")
        self._on_cand_select()          # make sure it loads even if the selection didn't change

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
        self._typed = True
        if self._suggest_after is not None:
            self.after_cancel(self._suggest_after)
        self._suggest_after = self.after(220, self._suggest)

    def _suggest(self):
        self._suggest_after = None
        text = self.name_var.get().strip()
        if len(text) < 2:
            return
        if self.catalog.ready:
            self._set_suggestions(self.catalog.suggest(text))
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
        text = self.name_var.get().strip()
        if not text:
            return
        self._typed = True
        sn = parse_set_number(text)
        if sn:                       # "TLA 58" -> that exact card; if not found, try it as a name
            self.set_var.set(sn[0].upper())
            self.num_var.set(sn[1])
            self._lookup_number(sn[0], sn[1], fallback=text)
        else:
            self.load_printings(text)

    def find_by_number(self):
        set_code, num = self.set_var.get().strip(), self.num_var.get().strip()
        if not set_code or not num:
            self.msg_var.set("Type the set code and the number from the bottom-left of the card "
                             "(for example TLA and 58).")
            return
        self._typed = True
        self._lookup_number(set_code, num)

    def _lookup_number(self, set_code, num, fallback=None):
        self._job += 1
        token = self._job
        self.msg_var.set(f"Looking up {set_code.upper()} #{num}...")
        self._bg(lambda: card_by_set_number(set_code, num),
                 lambda ok, val: self._on_number(token, ok, val, set_code, num, fallback))

    def _on_number(self, token, ok, val, set_code, num, fallback):
        if token != self._job:
            return
        if not ok:
            self._explain_failure(val)
            return
        if not val:
            if fallback:
                self.load_printings(fallback)
            else:
                self.msg_var.set(f"No card found for {set_code.upper()} #{num}. Check the set code "
                                 "(3-4 letters) and number at the bottom-left of the card.")
            return
        self.matches = [val]
        self.loaded_name = val["name"]
        self.name_var.set(val["name"])
        self._fill_printings(self.matches)
        self.tree.selection_set("0")
        self.msg_var.set(f"Found {val['name']} - {val['set']} #{val['number']}.")

    def load_printings(self, name):
        self.loaded_name = name
        self._job += 1
        token = self._job
        self.msg_var.set(f"Looking up {name}...")
        self._fill_printings([])
        self._bg(lambda: search_mtg(name),
                 lambda ok, val: self._on_printings(token, ok, val))

    def _explain_failure(self, err):
        self.matches = []
        self.loaded_name = ""
        if isinstance(err, ScryfallBusy):
            self.msg_var.set(f"Scryfall asked us to slow down. Wait about {err.seconds} "
                             "seconds, then try again.")
        else:
            self.msg_var.set("Couldn't reach Scryfall - check your internet connection. "
                             "You can still add the card with a custom value.")

    def _on_printings(self, token, ok, val):
        if token != self._job:
            return
        if not ok:
            self._explain_failure(val)
            return
        self.matches = val
        self._fill_printings(val)
        if not val:
            self.msg_var.set("No card found with that name - check the spelling, use the "
                             "set code and number, or add it with a custom value.")
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
            nf = money(m["price_nonfoil"]) if m["price_nonfoil"] else "n/a"
            fo = money(m["price_foil"]) if m["price_foil"] else "n/a"
            self.tree.insert("", "end", iid=str(i),
                             values=(m["set"], m["number"], m["rarity"], nf, fo))

    # --------------------------------------------------------------------- add
    def _quantity(self):
        try:
            q = int(self.qty_var.get().strip() or "1")
            if 1 <= q <= 999:
                return q
        except ValueError:
            pass
        messagebox.showerror(APP_NAME, "Quantity must be a whole number from 1 to 999.", parent=self)
        return None

    def add(self):
        qty = self._quantity()
        if qty is None:
            return
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
        card["qty"] = qty
        self.result = card
        self.destroy()


# ------------------------------------------------------------- phone window
class PhoneWindow(tk.Toplevel):
    """Shows the QR code to scan with a phone. Closing it turns the link off."""

    def __init__(self, parent, link, on_close):
        super().__init__(parent)
        self.configure(bg=C["bg"])
        self.title("Scan with your phone")
        self.resizable(False, False)
        self.link = link
        self.on_close_cb = on_close
        self.status_var = tk.StringVar(value="Waiting for your phone...")
        body = ttk.Frame(self, padding=20)
        body.pack()
        ttk.Label(body, text="Scan with your phone", style="Title.TLabel").pack(anchor="w")
        steps = ("1. Connect your phone to the same Wi-Fi as this computer.\n"
                 "2. Point your phone's camera at this code and open the link.\n"
                 "3. The first time, Safari says the connection isn't private: tap Show Details, "
                 "then visit this website. That's our own secure link.\n"
                 "4. Allow the camera, then hold a card in the frame. It is sent when it's sharp "
                 "and still, and you confirm it here.") if link.secure else (
                 "1. Connect your phone to the same Wi-Fi as this computer.\n"
                 "2. Point your phone's camera at this code and open the link.\n"
                 "3. Tap Take a photo. It appears here for you to confirm.\n\n"
                 + (link.warning or "The secure link isn't available, so live scanning is off."))
        ttk.Label(body, style="Muted.TLabel", justify="left", wraplength=380,
                  text=steps).pack(anchor="w", pady=(6, 12))
        qr = make_qr_image(link.url)
        panel = ttk.Frame(body, style="Panel.TFrame", padding=14)
        panel.pack()
        if qr is not None:
            qr.thumbnail((300, 300), Image.NEAREST)
            self._qr = ImageTk.PhotoImage(qr)
            ttk.Label(panel, image=self._qr, style="Panel.TLabel").pack()
        else:
            ttk.Label(panel, text="(Couldn't draw the QR code - type the address\nbelow into your phone's browser.)",
                      style="PanelMuted.TLabel", justify="center").pack()
        addr = ttk.Entry(body, width=44)
        addr.insert(0, link.url)
        addr.configure(state="readonly")
        addr.pack(fill="x", pady=(12, 4))
        ttk.Label(body, style="Muted.TLabel", justify="left", wraplength=360, text=(
            "If Windows asks about the firewall, choose Allow (private networks). "
            "The link only works while this window is open, and only for people "
            "with this exact address. Keep the phone screen on.")).pack(anchor="w", pady=(0, 8))
        ttk.Label(body, textvariable=self.status_var, style="Section.TLabel").pack(anchor="w")
        ttk.Button(body, text="Stop phone link", command=self.close).pack(anchor="e", pady=(10, 0))
        self.protocol("WM_DELETE_WINDOW", self.close)
        center_on(self, parent)

    def set_count(self, n):
        if n:
            self.status_var.set(f"Photos received: {n}. Keep sending - each one asks you to confirm.")

    def close(self):
        self.on_close_cb()
        self.destroy()


# ------------------------------------------------------------ settings window
def _num(value, default, lo, hi):
    try:
        return max(lo, min(hi, float(value)))
    except (TypeError, ValueError):
        return default


class SettingsWindow(tk.Toplevel):
    """General options, scanning sensitivity and key binds. Changes apply at once."""

    def __init__(self, parent, app):
        super().__init__(parent)
        self.app = app
        self.configure(bg=C["bg"])
        self.title("Settings")
        self.transient(parent)
        self.resizable(False, False)
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.hold_var = tk.DoubleVar(value=app.auto_hold_s)
        self.blur_var = tk.DoubleVar(value=app.blur_min)
        self.upd_var = tk.BooleanVar(value=app.check_updates)
        self.repo_var = tk.StringVar(value=app.settings.get("update_repo", ""))
        self.hold_text = tk.StringVar()
        self.blur_text = tk.StringVar()
        self.key_vars = {}

        outer = ttk.Frame(self, padding=16)
        outer.pack(fill="both", expand=True)
        nb = ttk.Notebook(outer)
        nb.pack(fill="both", expand=True)
        for title, build in (("General", self._general), ("Scanning", self._scanning),
                             ("Keys", self._keys)):
            page = ttk.Frame(nb, style="Panel.TFrame", padding=18)
            nb.add(page, text=title)
            build(page)
        ttk.Button(outer, text="Done", style="Accent.TButton", command=self.close).pack(
            anchor="e", pady=(14, 0))
        self.bind("<Escape>", lambda e: self.close())
        center_on(self, parent)

    def close(self):
        self._save_repo()
        self.app.settings_window = None
        self.destroy()

    # ---- tabs
    def _general(self, f):
        ttk.Label(f, text=f"MTG Card Scanner   version {APP_VERSION}",
                  style="Panel.TLabel", font=F(11, "bold")).pack(anchor="w")
        ttk.Label(f, style="PanelMuted.TLabel", justify="left", wraplength=460, text=(
            "Your cards, settings and scan photos are saved in your Documents folder and are "
            "kept when the app updates.")).pack(anchor="w", pady=(4, 14))
        ttk.Checkbutton(f, text="Look for updates when the app starts", variable=self.upd_var,
                        command=lambda: self.app.set_option("check_updates", bool(self.upd_var.get()))
                        ).pack(anchor="w")
        ttk.Label(f, text="Update source on GitHub (owner/name)", style="PanelMuted.TLabel").pack(
            anchor="w", pady=(14, 2))
        e = ttk.Entry(f, textvariable=self.repo_var, width=40)
        e.pack(anchor="w")
        e.bind("<FocusOut>", lambda ev: self._save_repo())
        e.bind("<Return>", lambda ev: self._save_repo())
        built = BUILD_INFO.get("repo", "")
        ttk.Label(f, style="PanelMuted.TLabel", wraplength=460, justify="left", text=(
            f"Leave blank to use the one built into this app ({built or 'none'}). The repository "
            "has to be public.")).pack(anchor="w", pady=(2, 14))
        row = ttk.Frame(f, style="Panel.TFrame")
        row.pack(anchor="w")
        ttk.Button(row, text="Check for updates now", command=self._check).pack(side="left")
        ttk.Button(row, text="Read me", command=self.app.open_readme).pack(side="left", padx=8)
        ttk.Button(row, text="My files", command=lambda: open_folder(DATA_DIR)).pack(side="left")

    def _check(self):
        self._save_repo()
        self.app.start_update_check(manual=True)

    def _save_repo(self):
        value = self.repo_var.get().strip()
        if value != self.app.settings.get("update_repo", ""):
            self.app.set_option("update_repo", value)

    def _scanning(self, f):
        ttk.Label(f, text="Auto mode: how long a card must be held still", style="Panel.TLabel").pack(anchor="w")
        row = ttk.Frame(f, style="Panel.TFrame")
        row.pack(fill="x", pady=(4, 2))
        sc = ttk.Scale(row, from_=0.5, to=3.0, variable=self.hold_var, orient="horizontal",
                       length=260, command=lambda v: self._show())
        sc.pack(side="left")
        sc.bind("<ButtonRelease-1>", lambda e: self.app.set_option("auto_hold", round(self.hold_var.get(), 1)))
        ttk.Label(row, textvariable=self.hold_text, style="Panel.TLabel", width=12).pack(side="left", padx=10)
        ttk.Label(f, style="PanelMuted.TLabel", wraplength=460, justify="left", text=(
            "Shorter is faster but may grab a card while it is still moving.")).pack(anchor="w", pady=(0, 16))
        ttk.Label(f, text="How sharp the picture must be before it counts as ready",
                  style="Panel.TLabel").pack(anchor="w")
        row = ttk.Frame(f, style="Panel.TFrame")
        row.pack(fill="x", pady=(4, 2))
        sc = ttk.Scale(row, from_=20, to=90, variable=self.blur_var, orient="horizontal",
                       length=260, command=lambda v: self._show())
        sc.pack(side="left")
        sc.bind("<ButtonRelease-1>", lambda e: self.app.set_option("blur_min", round(self.blur_var.get())))
        ttk.Label(row, textvariable=self.blur_text, style="Panel.TLabel", width=12).pack(side="left", padx=10)
        ttk.Label(f, style="PanelMuted.TLabel", wraplength=460, justify="left", text=(
            "The small 'focus' number under the camera shows what your camera reaches with a "
            "card held steady. If the status keeps saying Blurry when it looks fine, lower this. "
            "If blurry cards slip through, raise it.")).pack(anchor="w", pady=(0, 16))
        ttk.Button(f, text="Reset these two", command=self._reset_scan).pack(anchor="w")
        self._show()

    def _show(self):
        self.hold_text.set(f"{self.hold_var.get():.1f} seconds")
        self.blur_text.set(f"{int(round(self.blur_var.get()))}")

    def _reset_scan(self):
        self.hold_var.set(1.0)
        self.blur_var.set(45)
        self.app.set_option("auto_hold", 1.0)
        self.app.set_option("blur_min", 45)
        self._show()

    def _keys(self, f):
        ttk.Label(f, style="PanelMuted.TLabel", wraplength=500, justify="left", text=(
            "Click Change, then press the key (or a combination like Ctrl+E). Single keys are "
            "ignored while you are typing in a box.")).pack(anchor="w", pady=(0, 10))
        grid = ttk.Frame(f, style="Panel.TFrame")
        grid.pack(anchor="w")
        for r, (aid, label, _) in enumerate(ACTIONS):
            ttk.Label(grid, text=label, style="Panel.TLabel", width=40).grid(row=r, column=0, sticky="w", pady=2)
            var = tk.StringVar()
            self.key_vars[aid] = var
            ttk.Label(grid, textvariable=var, style="Panel.TLabel", width=12, anchor="center").grid(row=r, column=1, padx=6)
            ttk.Button(grid, text="Change", style="Small.TButton",
                       command=lambda a=aid: self._capture(a)).grid(row=r, column=2, padx=2)
            ttk.Button(grid, text="Clear", style="Small.TButton",
                       command=lambda a=aid: self._clear(a)).grid(row=r, column=3, padx=2)
        ttk.Button(f, text="Reset all keys", command=self._reset_keys).pack(anchor="w", pady=(12, 0))
        self._refresh_keys()

    def _refresh_keys(self):
        keys = self.app.current_keys()
        for aid, var in self.key_vars.items():
            var.set(format_key(keys.get(aid, "")))

    def _clear(self, aid):
        self.app.set_key(aid, "")
        self._refresh_keys()

    def _reset_keys(self):
        self.app.reset_keys()
        self._refresh_keys()

    def _capture(self, aid):
        win = tk.Toplevel(self)
        win.configure(bg=C["bg"])
        win.title("Set key")
        win.transient(self)
        win.resizable(False, False)
        ttk.Label(win, text=f"Press the key for:\n{ACTION_LABELS[aid]}\n\n(Esc cancels)",
                  justify="center", padding=24).pack()
        info = tk.StringVar()
        ttk.Label(win, textvariable=info, style="Muted.TLabel", wraplength=280).pack(pady=(0, 14))

        def on_key(e):
            if e.keysym == "Escape":
                win.destroy()
                return "break"
            key = event_to_key(e)
            if key is None:
                return "break"
            if key == "reserved":
                info.set("That key is used to move around the lists. Pick another.")
                return "break"
            other = next((a for a, k in self.app.current_keys().items() if k == key and a != aid), None)
            if other and not messagebox.askyesno(
                    APP_NAME, f'{format_key(key)} is already used for "{ACTION_LABELS[other]}". '
                              "Use it here instead?", parent=win):
                return "break"
            if other:
                self.app.set_key(other, "")
            self.app.set_key(aid, key)
            win.destroy()
            self._refresh_keys()
            return "break"

        win.bind("<Key>", on_key)
        center_on(win, self)
        try:
            win.wait_visibility()
            win.grab_set()
        except tk.TclError:
            pass
        win.focus_force()


class UpdateDialog(tk.Toplevel):
    """Offers a new version, downloads it with a progress bar, and starts the installer."""

    def __init__(self, parent, app, info):
        super().__init__(parent)
        self.app, self.info = app, info
        self.configure(bg=C["bg"])
        self.title("Update available")
        self.transient(parent)
        self.resizable(False, False)
        self._q = queue.Queue()
        body = ttk.Frame(self, padding=20)
        body.pack()
        ttk.Label(body, text=f"Version {info['version']} is ready", style="Title.TLabel").pack(anchor="w")
        ttk.Label(body, style="Muted.TLabel", text=f"You have version {APP_VERSION}.").pack(anchor="w", pady=(2, 10))
        if info.get("notes"):
            ttk.Label(body, text=info["notes"], style="Muted.TLabel", wraplength=420,
                      justify="left").pack(anchor="w", pady=(0, 10))
        ttk.Label(body, style="PanelMuted.TLabel", wraplength=420, justify="left", text=(
            "The app will close, update itself and reopen. Your cards and settings are kept.")
                  ).pack(anchor="w", pady=(0, 10))
        self.bar = ttk.Progressbar(body, length=420, maximum=1.0)
        self.status = tk.StringVar()
        ttk.Label(body, textvariable=self.status, style="Muted.TLabel").pack(anchor="w")
        row = ttk.Frame(body)
        row.pack(fill="x", pady=(12, 0))
        self.go = ttk.Button(row, text="Update now", style="Accent.TButton", command=self.start)
        self.go.pack(side="right")
        self.later = ttk.Button(row, text="Later", command=self.destroy)
        self.later.pack(side="right", padx=(0, 8))
        self._body = body
        center_on(self, parent)

    def start(self):
        self.go.state(["disabled"])
        self.later.state(["disabled"])
        self.bar.pack(fill="x", pady=(4, 4), before=self._body.winfo_children()[-1])
        self.status.set("Downloading...")
        info, q = self.info, self._q

        def work():
            try:
                path = download_update(info, lambda f: q.put(("progress", f)))
                q.put(("done", path))
            except UpdateError as e:
                q.put(("error", str(e)))
            except Exception as e:  # noqa: BLE001
                q.put(("error", f"The update failed ({type(e).__name__})."))

        threading.Thread(target=work, daemon=True).start()
        self.after(100, self._poll)

    def _poll(self):
        try:
            if not self.winfo_exists():
                return
        except tk.TclError:
            return
        while True:
            try:
                kind, val = self._q.get_nowait()
            except queue.Empty:
                break
            if kind == "progress":
                self.bar["value"] = val
                self.status.set(f"Downloading...  {int(val * 100)}%")
            elif kind == "error":
                self.status.set(val)
                self.go.state(["!disabled"])
                self.later.state(["!disabled"])
                return
            elif kind == "done":
                self.status.set("Starting the installer...")
                try:
                    launch_installer(val)
                except OSError as e:
                    self.status.set(f"Couldn't start the installer: {e}")
                    self.later.state(["!disabled"])
                    return
                self.app.root.after(300, self.app.on_close)
                return
        self.after(100, self._poll)


# ---------------------------------------------------------------- main app
class ScannerApp:
    def __init__(self, root):
        self.root = root
        root.title(APP_NAME)
        try:
            sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
            root.geometry(f"{min(1440, sw - 40)}x{min(840, sh - 90)}+20+20")
        except (tk.TclError, TypeError):
            root.geometry("1380x800")
        root.minsize(1180, 640)
        ensure_dirs()
        apply_theme(root)
        start_ocr_warmup()                 # everything slow loads in the background
        self.settings = load_json(SETTINGS_FILE, {})
        if not isinstance(self.settings, dict):
            self.settings = {}
        saved_keys = self.settings.get("keys", {})
        self.keys = dict(DEFAULT_KEYS)
        if isinstance(saved_keys, dict):
            self.keys.update({a: k for a, k in saved_keys.items()
                              if a in DEFAULT_KEYS and isinstance(k, str)})
        self.auto_hold_s = _num(self.settings.get("auto_hold", 1.0), 1.0, 0.5, 3.0)
        self.blur_min = _num(self.settings.get("blur_min", 45), 45.0, 20.0, 90.0)
        self.check_updates = bool(self.settings.get("check_updates", True))
        self.pending_update = None
        self.update_btn = None
        self.settings_window = None
        self._bound = []
        self._bgq = queue.Queue()
        self.cards = load_cards()
        self.catalog = NameCatalog(NAMES_FILE)
        self.catalog.start()

        self.finish = tk.StringVar(value=self.settings.get("finish", "nonfoil"))
        self.mode_var = tk.StringVar(value=self.settings.get("mode", "manual"))
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

        self.stream = None
        self.last_frame = None
        self.photo = None
        self.busy = False
        self.quad = None
        self.quad_miss = 0
        self.quad_motion = 999.0
        self.frame_count = 0
        self.sharp_avg = 0.0
        self.frame_buffer = deque(maxlen=6)   # recent (sharpness, frame, quad)
        self._pill_state = None
        self._seen_seq = -1
        self._opened_cam_settings = False
        self.auto_t0 = None                   # auto mode: when the card became ready and still
        self.auto_armed = True
        self.auto_gone = 0
        self.phone = None
        self.phone_window = None

        self.build_ui()
        self.start_camera()
        self.refresh_table()
        self.update_preview()
        self.apply_keybinds()
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.canvas.focus_set()
        root.after(300, self.poll_bg)
        if IS_BUILT and self.check_updates:        # quietly, a few seconds after start-up
            root.after(4000, lambda: self.start_update_check(False))

    # ---------------------------------------------------------------- UI
    def build_ui(self):
        root = self.root
        root.columnconfigure(0, weight=0)
        root.columnconfigure(1, weight=1)
        root.rowconfigure(1, weight=1)

        # ---- header
        head = ttk.Frame(root, padding=(22, 14, 22, 4))
        head.grid(row=0, column=0, columnspan=2, sticky="ew")
        head.columnconfigure(0, weight=1)
        titles = ttk.Frame(head)
        titles.grid(row=0, column=0, sticky="w")
        ttk.Label(titles, text="MTG Card Scanner", style="Title.TLabel").pack(anchor="w")
        ttk.Label(titles, text=f"Scan, price and sort your Magic cards   -   version {APP_VERSION}",
                  style="Muted.TLabel").pack(anchor="w")
        tiles = ttk.Frame(head)
        tiles.grid(row=0, column=1, sticky="e")
        t1, self.tile_count = stat_tile(tiles, "Cards shown")
        t2, self.tile_view = stat_tile(tiles, "Value of this view")
        t3, self.tile_all = stat_tile(tiles, "Whole collection")
        for t in (t1, t2, t3):
            t.pack(side="left", padx=(8, 0))
        hb = ttk.Frame(head)
        hb.grid(row=0, column=2, sticky="e", padx=(16, 0))
        ttk.Button(hb, text="Settings", style="Small.TButton", command=self.open_settings,
                   takefocus=0).pack(side="left", padx=(0, 6))
        self.update_btn = ttk.Button(hb, text="Check for updates", style="Small.TButton",
                                     command=self.on_update_click, takefocus=0)
        self.update_btn.pack(side="left", padx=(0, 6))
        ttk.Button(hb, text="Exit", style="Danger.TButton", command=self.on_close,
                   takefocus=0).pack(side="left")

        # ---- left: camera
        left = ttk.Frame(root, padding=(22, 8, 10, 12))
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

        ttk.Button(cam, text="Snap card   (Space)", style="Accent.TButton",
                   command=self.snap, takefocus=0).pack(fill="x", pady=(12, 0))
        row = ttk.Frame(cam, style="Panel.TFrame")
        row.pack(fill="x", pady=(8, 0))
        for text, cmd in (("Phone...", self.open_phone), ("Photo file...", self.scan_file),
                          ("Add by name / number...", self.add_by_name)):
            ttk.Button(row, text=text, command=cmd, takefocus=0).pack(
                side="left", fill="x", expand=True, padx=(0, 6))

        opt = ttk.Frame(cam, style="Panel.TFrame")
        opt.pack(fill="x", pady=(12, 0))
        ttk.Label(opt, text="Capture", style="PanelMuted.TLabel").pack(side="left", padx=(0, 8))
        for text, val in (("Manual", "manual"), ("Auto", "auto")):
            ttk.Radiobutton(opt, text=text, value=val, variable=self.mode_var,
                            style="Seg.Toolbutton", command=self.on_mode_change,
                            takefocus=0).pack(side="left", padx=(0, 2))
        ttk.Label(opt, text="   New scans are", style="PanelMuted.TLabel").pack(side="left", padx=(0, 8))
        for text, val in (("Non-foil", "nonfoil"), ("Foil", "foil")):
            ttk.Radiobutton(opt, text=text, value=val, variable=self.finish,
                            style="Seg.Toolbutton", command=self.on_finish_change,
                            takefocus=0).pack(side="left", padx=(0, 2))
        self.cam_toggle = ttk.Button(opt, text="Camera  v", style="Link.TButton",
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
            "on it without glare. In Auto mode the app snaps when the card is sharp and "
            "still, then asks you to confirm - remove the card to scan the next one.")
                  ).pack(anchor="w", pady=(10, 0))

        # ---- right: collection
        right = ttk.Frame(root, padding=(10, 8, 22, 12))
        right.grid(row=1, column=1, sticky="nsew")
        panel = ttk.Frame(right, style="Panel.TFrame", padding=14)
        panel.pack(fill="both", expand=True)
        panel.columnconfigure(0, weight=1)
        panel.rowconfigure(1, weight=1)

        bar = ttk.Frame(panel, style="Panel.TFrame")
        bar.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        for label, var, values, width in (
                ("Type", self.type_var, TYPE_FILTERS, 11),
                ("Color", self.color_var, COLOR_FILTERS, 10),
                ("Sort", self.sort_var, [n for n, _ in SORT_MODES], 19)):
            ttk.Label(bar, text=label, style="PanelMuted.TLabel").pack(side="left", padx=(0, 6))
            c = ttk.Combobox(bar, textvariable=var, values=values, width=width,
                             state="readonly")
            c.pack(side="left", padx=(0, 14))
            c.bind("<<ComboboxSelected>>", self.on_filter_change)

        cols = [("qty", "Qty", 42, "e"), ("name", "Name", 180, "w"), ("type", "Type", 80, "w"),
                ("color", "Color", 78, "w"), ("set", "Set", 140, "w"),
                ("finish", "Finish", 66, "w"), ("each", "Each", 62, "e"), ("value", "Total", 72, "e")]
        tframe = ttk.Frame(panel, style="Panel.TFrame")
        tframe.grid(row=1, column=0, sticky="nsew")
        tframe.columnconfigure(0, weight=1)
        tframe.rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(tframe, columns=[c[0] for c in cols], show="headings",
                                 selectmode="extended")
        for key, text, width, anchor in cols:
            self.tree.heading(key, text=text, anchor=anchor)
            self.tree.column(key, width=width, anchor=anchor, stretch=(key in ("name", "set")))
        self.tree.tag_configure("odd", background=C["stripe"])
        self.tree.tag_configure("foil", foreground=C["gold"])
        sb = ttk.Scrollbar(tframe, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.bind("<<TreeviewSelect>>", lambda e: self.canvas.focus_set())

        btns = ttk.Frame(panel, style="Panel.TFrame")
        btns.grid(row=2, column=0, sticky="ew", pady=(12, 0))
        for text, cmd, style in (("+1", lambda: self.change_qty(1), "Small.TButton"),
                                 ("-1", lambda: self.change_qty(-1), "Small.TButton"),
                                 ("Switch foil", self.flip_selected, "TButton"),
                                 ("Remove", self.remove_selected, "Danger.TButton"),
                                 ("Export view", self.export_view, "TButton"),
                                 ("Export all", self.export_all, "TButton"),
                                 ("My files", lambda: open_folder(DATA_DIR), "TButton")):
            ttk.Button(btns, text=text, command=cmd, style=style,
                       takefocus=0).pack(side="left", padx=(0, 6))

        tk.Label(root, textvariable=self.status_var, anchor="w", bg=C["panel"],
                 fg=C["muted"], font=F(9), padx=22, pady=6).grid(
            row=2, column=0, columnspan=2, sticky="ew")

    def toggle_camera_settings(self):
        if self.cam_frame.winfo_ismapped():
            self.cam_frame.pack_forget()
            self.cam_toggle.configure(text="Camera  v")
        else:
            self.cam_frame.pack(fill="x")
            self.cam_toggle.configure(text="Camera  ^")

    # ------------------------------------------------------------ camera
    def start_camera(self):
        if self.stream is not None:
            self.stream.stop()
        _, rw, rh = next((r for r in RESOLUTIONS if r[0] == self.res_var.get()), RESOLUTIONS[0])
        self.stream = CameraStream(int(self.camera_var.get()), rw, rh,
                                   bool(self.autofocus.get()), float(self.focus_value.get()))
        self.last_frame = None
        self.quad = None
        self._seen_seq = -1
        self.frame_buffer.clear()
        self.apply_focus()

    def update_preview(self):
        try:
            self._update_preview_once()
        except Exception as e:  # keep the preview loop alive
            print("preview error:", e, file=sys.stderr)
        self.root.after(33, self.update_preview)

    def _show_message(self, text, pill_text):
        self.canvas.itemconfig(self.img_item, image="")
        self.canvas.itemconfig(self.msg_item, state="normal", text=text)
        self.set_pill("warn" if "found" in pill_text or "lost" in pill_text else "idle", pill_text)
        self.detail_var.set("")

    def _update_preview_once(self):
        st = self.stream.state
        if st == "opening":
            self.last_frame = None
            self._show_message("Starting camera...", "Starting camera...")
            return
        if st in ("none", "lost"):
            self.last_frame = None
            if st == "none":
                self._show_message(
                    "No camera found.\nMake sure it's plugged in and not being used by another "
                    "app, then open Camera and try another camera number. You can still use "
                    "Phone..., Photo file... or Add by name / number...", "No camera found")
            else:
                self._show_message("The camera stopped sending pictures. Unplug it and plug it "
                                   "back in, then choose its number under Camera.", "Camera lost")
            if not self._opened_cam_settings:
                self._opened_cam_settings = True
                if not self.cam_frame.winfo_ismapped():
                    self.toggle_camera_settings()
            return
        frame, seq = self.stream.latest()
        if frame is None or seq == self._seen_seq:
            return                                   # nothing new to draw
        self._seen_seq = seq
        if str(self.stream.index) != self.camera_var.get():
            self.camera_var.set(str(self.stream.index))

        self.last_frame = frame
        self.frame_count += 1
        if self.frame_count % 3 == 0:                     # look for the card outline
            q = detect_card(frame)
            if q is not None:
                self.quad_motion = float(np.abs(self.quad - q).max()) if self.quad is not None else 999.0
                if self.quad is not None and self.quad_motion < 40:
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
        if self.mode_var.get() == "auto" and not self.busy:
            state, text = self.auto_step(frame, state, text)
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
        if self.sharp_avg < self.blur_min:
            return "warn", "Blurry - hold steady or adjust focus"
        return "good", "Ready - press Space"

    def auto_step(self, frame, state, text):
        """Auto mode: when the card is ready AND still for a moment, capture it.
        The confirm window still opens, so nothing is added without your OK."""
        if self.quad is None:
            self.auto_t0 = None
            self.auto_gone += 1
            if self.auto_gone >= 8:
                self.auto_armed = True
            return "idle", "Auto: place a card in the frame"
        self.auto_gone = 0
        if not self.auto_armed:
            return "idle", "Remove the card to scan the next one (or press Space)"
        if state != "good":
            self.auto_t0 = None
            return state, text
        if self.quad_motion > max(6.0, frame.shape[1] * 0.006):
            self.auto_t0 = None
            return "warn", "Hold still..."
        now = time.time()
        if self.auto_t0 is None:
            self.auto_t0 = now
        progress = (now - self.auto_t0) / max(0.2, self.auto_hold_s)
        if progress >= 1.0:
            self.auto_t0 = None
            self.auto_armed = False                 # one scan per card placement
            self.root.after(10, self.snap)
            return "good", "Captured!"
        return "good", f"Hold still...  {int(100 * progress)}%"

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
    # ------------------------------------------------------------ key binds
    def current_keys(self):
        return dict(self.keys)

    def set_key(self, action, key):
        self.keys[action] = key
        self._save_keys()

    def reset_keys(self):
        self.keys = dict(DEFAULT_KEYS)
        self._save_keys()

    def _save_keys(self):
        self.settings["keys"] = {a: k for a, k in self.keys.items() if k != DEFAULT_KEYS[a]}
        save_json(SETTINGS_FILE, self.settings)
        self.apply_keybinds()

    def key_actions(self):
        return {"snap": self.snap, "auto": self.toggle_mode, "finish": self.toggle_finish,
                "phone": self.open_phone, "photo": self.scan_file, "add_name": self.add_by_name,
                "qty_up": lambda: self.change_qty(1), "qty_down": lambda: self.change_qty(-1),
                "flip": self.flip_selected, "remove": self.remove_selected,
                "export_view": self.export_view, "export_all": self.export_all,
                "settings": self.open_settings,
                "update": lambda: self.start_update_check(True), "exit": self.on_close}

    def apply_keybinds(self):
        for seq in self._bound:
            try:
                self.root.unbind(seq)
            except tk.TclError:
                pass
        self._bound = []
        for action, key in self.keys.items():
            if not key:
                continue
            for seq in key_patterns(key):
                try:
                    self.root.bind(seq, lambda e, a=action, k=key: self.on_key_action(a, k))
                    self._bound.append(seq)
                except tk.TclError:
                    pass

    def on_key_action(self, action, key):
        if not key_has_modifier(key):         # plain keys must not steal typing
            try:
                w = self.root.focus_get()
            except (KeyError, tk.TclError):
                w = None
            if isinstance(w, (tk.Entry, ttk.Entry, ttk.Combobox, ttk.Spinbox, tk.Text)):
                return None
        if self.busy and action != "exit":
            return None
        self.key_actions()[action]()
        return "break"

    def toggle_mode(self):
        self.mode_var.set("manual" if self.mode_var.get() == "auto" else "auto")
        self.on_mode_change()

    def toggle_finish(self):
        self.finish.set("nonfoil" if self.finish.get() == "foil" else "foil")
        self.on_finish_change()

    # ------------------------------------------------------ settings window
    def set_option(self, name, value):
        self.settings[name] = value
        save_json(SETTINGS_FILE, self.settings)
        if name == "auto_hold":
            self.auto_hold_s = _num(value, 1.0, 0.5, 3.0)
        elif name == "blur_min":
            self.blur_min = _num(value, 45.0, 20.0, 90.0)
        elif name == "check_updates":
            self.check_updates = bool(value)

    def open_settings(self):
        if self.busy:
            return
        if self.settings_window is not None:
            try:
                self.settings_window.lift()
                return
            except tk.TclError:
                self.settings_window = None
        self.settings_window = SettingsWindow(self.root, self)

    def open_readme(self):
        base = Path(sys.executable).parent if IS_BUILT else Path(__file__).resolve().parent
        path = base / "README.md"
        if path.exists():
            open_folder(path)
        else:
            messagebox.showinfo(APP_NAME, "The read me wasn't found next to the app. "
                                "It is also on your GitHub page.")

    # ------------------------------------------------------------- updates
    def update_repo(self):
        return (self.settings.get("update_repo") or BUILD_INFO.get("repo") or "").strip()

    def start_update_check(self, manual):
        if not IS_BUILT:
            if manual:
                messagebox.showinfo(APP_NAME, "You're running from the source code. Updates are "
                                    "for the installed app.")
            return
        repo, current = self.update_repo(), APP_VERSION
        if manual:
            self.set_status("Checking for updates...")

        def work():
            try:
                self._bgq.put(("update", manual, find_update(repo, current)))
            except UpdateError as e:
                self._bgq.put(("update_error", manual, str(e)))
            except Exception as e:  # noqa: BLE001
                self._bgq.put(("update_error", manual, f"Couldn't check for updates ({type(e).__name__})."))

        threading.Thread(target=work, daemon=True).start()

    def poll_bg(self):
        try:
            while True:
                try:
                    item = self._bgq.get_nowait()
                except queue.Empty:
                    break
                self.handle_bg(*item)
        finally:
            self.root.after(300, self.poll_bg)

    def handle_bg(self, kind, manual, value):
        if kind == "update_error":
            if manual:
                self.set_status(value)
                messagebox.showerror(APP_NAME, value)
        elif kind == "update":
            self.pending_update = value
            if self.update_btn is not None:
                if value:
                    self.update_btn.configure(text=f"Update to {value['version']}", style="Accent.TButton")
                else:
                    self.update_btn.configure(text="Check for updates", style="Small.TButton")
            if value:
                self.set_status(f"Version {value['version']} is available - click Update in the top right.")
                if manual:
                    self.show_update_dialog()
            elif manual:
                self.set_status("You're up to date.")
                messagebox.showinfo(APP_NAME, f"You're up to date (version {APP_VERSION}).")

    def on_update_click(self):
        if self.pending_update:
            self.show_update_dialog()
        else:
            self.start_update_check(True)

    def show_update_dialog(self):
        if self.pending_update:
            UpdateDialog(self.root, self, self.pending_update)

    def on_mode_change(self):
        self.settings["mode"] = self.mode_var.get()
        save_json(SETTINGS_FILE, self.settings)
        self.auto_t0 = None
        self.auto_armed = True
        self.set_status("Auto mode: hold a card still in the frame and it is captured for you "
                        "to confirm." if self.mode_var.get() == "auto" else "Manual mode: press Space to snap.")
        self.canvas.focus_set()

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
        self.start_camera()
        self.canvas.focus_set()

    def on_debug_change(self):
        self.settings["debug"] = bool(self.debug_var.get())
        save_json(SETTINGS_FILE, self.settings)
        if self.debug_var.get():
            self.set_status(f"Diagnostic pictures will be saved in: {DEBUG_DIR}")

    def apply_focus(self):
        auto = self.autofocus.get()
        self.focus_scale.state(["disabled"] if auto else ["!disabled"])
        if self.stream is not None:
            self.stream.send("focus", auto, float(self.focus_value.get()))

    def on_focus_change(self):
        self.settings["autofocus"] = bool(self.autofocus.get())
        self.settings["focus"] = float(self.focus_value.get())
        save_json(SETTINGS_FILE, self.settings)
        self.apply_focus()
        self.canvas.focus_set()

    def open_driver_settings(self):
        """Opens the camera maker's own settings window (focus, brightness...)."""
        if self.stream is None or self.stream.state != "live":
            messagebox.showinfo(APP_NAME, "The camera isn't working yet.")
            return
        self.stream.send("settings")
        self.set_status("Opened the camera's own settings window (it may appear behind this window).")

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
                c["qty"], c["name"], main_type(c), color_text(c), c["set"],
                finish_text(c), money(c["price"]), money(line_total(c))))
        keep = [i for i in keep_selection if self.tree.exists(i)]
        if keep:
            self.tree.selection_set(keep)
        shown = sum(c["qty"] for c in view)
        total = sum(c["qty"] for c in self.cards)
        self.tile_count.set(f"{shown}" if shown == total else f"{shown} of {total}")
        self.tile_view.set(money(sum(line_total(c) for c in view)))
        self.tile_all.set(money(sum(line_total(c) for c in self.cards)))

    def selected_cards(self):
        ids = set(self.tree.selection())
        return [c for c in self.cards if c["id"] in ids]

    def save_cards(self):
        save_json(CARDS_FILE, self.cards)

    # ---------------------------------------------------------- adding cards
    def snap(self):
        if self.busy:
            return
        if self.last_frame is None or not self.frame_buffer:
            messagebox.showinfo(APP_NAME, "The camera isn't working yet, so there's nothing "
                                "to snap. You can use Phone..., Photo file... or Add by name / "
                                "number... instead.")
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
        """Open the confirm window. Returns the card as stored (or None if cancelled)."""
        self.busy = True
        try:
            dlg = AddCardDialog(self.root, cards, self.catalog, self.finish.get(),
                                DEBUG_DIR if self.debug_var.get() else None)
            self.root.wait_window(dlg)
            card = dlg.result
        finally:
            self.busy = False
            self.auto_armed = False        # auto mode waits until the card is taken away
            self.auto_t0 = None
        try:
            self.canvas.focus_set()
        except tk.TclError:
            pass
        if not card:
            self.set_status("Cancelled - nothing added.")
            return None

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
        stored = self.add_to_collection(card)
        self.save_cards()
        self.refresh_table()
        self.set_status(
            f"Added {card['qty']}x {card['name']} ({finish_text(card)}) - {money(card['price'])} each"
            + (f".  You now have {stored['qty']}." if stored is not card else "."))
        return stored

    def add_to_collection(self, card):
        """Scanning the same printing again adds to its quantity instead of a new row."""
        for c in self.cards:
            if same_card(c, card):
                c["qty"] += card["qty"]
                c["price_nonfoil"], c["price_foil"] = card["price_nonfoil"], card["price_foil"]
                apply_finish(c, c["finish"])           # refresh the price
                return c
        self.cards.append(card)
        return card

    # ------------------------------------------------------- list actions
    def change_qty(self, delta):
        sel = self.selected_cards()
        if not sel:
            messagebox.showinfo(APP_NAME, "Click a card in the list first "
                                "(hold Ctrl to pick several).")
            return
        ids = [c["id"] for c in sel]
        gone = [c for c in sel if c["qty"] + delta < 1]
        if gone and not messagebox.askyesno(
                APP_NAME, f"{len(gone)} card(s) would drop to zero. Remove them from your list?"):
            sel = [c for c in sel if c not in gone]
            gone = []
        for c in sel:
            if c in gone:
                continue
            c["qty"] += delta
        if gone:
            drop = {c["id"] for c in gone}
            self.cards = [c for c in self.cards if c["id"] not in drop]
        self.save_cards()
        self.refresh_table(keep_selection=ids)

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

    # ------------------------------------------------------------- phone
    def open_phone(self):
        if self.phone_window is not None:
            try:
                self.phone_window.lift()
                return
            except tk.TclError:
                self.phone_window = None
        link = PhoneLink()
        try:
            link.start()
        except OSError as e:
            messagebox.showerror(APP_NAME, f"Couldn't start the phone link:\n{e}")
            return
        self.phone = link
        self.phone_window = PhoneWindow(self.root, link, self.close_phone)
        self.root.after(400, self.process_phone)

    def close_phone(self):
        if self.phone is not None:
            self.phone.stop()
        self.phone = None
        self.phone_window = None

    def process_phone(self):
        link = self.phone
        if link is None:
            return
        try:
            if self.phone_window is not None:
                self.phone_window.set_count(link.received)
            if not self.busy and not link.incoming.empty():
                job, img, live = link.incoming.get_nowait()
                self.bring_to_front()
                self.handle_phone_photo(link, job, img, live)
        finally:
            if self.phone is not None:
                self.root.after(400, self.process_phone)

    def handle_phone_photo(self, link, job, img, live=False):
        # live frames are framed by the phone's card-shaped guide; photos are the whole picture
        card = self.run_add_dialog([extract_card(img, None, frac=BOX_HEIGHT_FRACTION if live else 1.0)])
        if card:
            link.set_status(job, "added", f"{card['name']} - {money(card['price'])}")
        else:
            link.set_status(job, "skipped")

    def bring_to_front(self):
        try:
            self.root.deiconify()
            self.root.lift()
            self.root.attributes("-topmost", True)
            self.root.after(400, lambda: self.root.attributes("-topmost", False))
        except tk.TclError:
            pass

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
        self.set_status(f"Saved {len(rows)} lines to {path}")

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
        if self.stream is not None:
            self.stream.stop()
        self.close_phone()
        self.root.destroy()


def main():
    root = tk.Tk()
    ScannerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
