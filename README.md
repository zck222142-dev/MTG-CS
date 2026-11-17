[README.md](https://github.com/user-attachments/files/34991011/README.md)
# MTG Card Scanner

A Windows desktop app that identifies Magic: The Gathering cards from a webcam or a phone
camera, looks up their prices, and keeps a sortable, exportable collection list on your own
computer. It is built for beginners: install it, hold up a card, confirm the guess.

> This is an unofficial fan project. It is not affiliated with or endorsed by Wizards of the
> Coast or Scryfall. Prices are estimates, and the card reader can be wrong. Read the
> [Warnings](#warnings) before relying on it for anything that matters.

---

## What it does

- **Scans cards** from a webcam, from your phone's camera, from a photo file, or by typing a
  name or a set code and collector number (for example `TLA 58`).
- **Shows a guess list** with the card artwork next to each guess, so you can pick the right
  one at a glance. You always confirm before a card is added.
- **Looks up the price** of the exact printing, foil or non-foil, from Scryfall.
- **Counts copies.** Scanning the same printing again adds to its quantity (handy for lands).
- **Sorts and filters** by value, name, set, quantity, scan order, card type and colour.
- **Exports** your list (or just the filtered view) to a text file.
- **Saves everything locally** in your Documents folder. No account, no cloud.
- **Updates itself** with one click.

---

## Install

1. Run `MTG-Card-Scanner-Setup.exe` and follow the steps. It installs for your user only and
   does not ask for administrator rights. Nothing else needs to be installed.
2. Windows may show a blue **"Windows protected your PC"** screen because the installer is not
   code-signed. Click **More info**, then **Run anyway**. See [Warnings](#warnings).
3. Start **MTG Card Scanner** from the Start menu or the desktop shortcut.

To update later, use the **Update** button in the app (see [Updating](#updating)). You do not
need to uninstall first.

---

## How to use it

### Scan with the webcam
1. Put a card in front of the camera, fill the frame, hold it flat, and keep light on it
   without glare.
2. The status pill under the camera tells you what to fix: *Place the card inside the frame*,
   *Too dark*, *Blurry*, *Ready*.
3. Press **Space** (or click **Snap card**). A window opens with the straightened photo and a
   list of best guesses with artwork.
4. Pick the right guess, pick the printing (the set the card is from), choose foil or
   non-foil, set the quantity, and click **Add card**.

### Auto mode
Switch **Capture** from *Manual* to *Auto*. When the card is sharp and held still for about a
second, the app snaps it for you and opens the same confirm window, so nothing is added
without your OK. Take the card away before showing the next one. You can change how long it
waits in **Settings > Scanning**.

### Scan with your phone
1. Click **Phone...**. A QR code appears.
2. Connect your phone to the **same Wi-Fi** as the PC and scan the QR code with the phone's
   camera.
3. The first time, Safari or Chrome says the connection is not private. That is expected (see
   [How the phone link works](#how-the-phone-link-works)). On an iPhone tap **Show Details**,
   then **visit this website**. Then allow the camera.
4. Hold a card inside the frame on your phone. When it is sharp and still, the phone sends one
   full-resolution photo to the PC, where you confirm it. There is also a **Send now** button
   and buttons to use the phone's camera app or a saved photo.

### Add without a camera
Click **Add by name / number...** and type part of a name (suggestions appear as you type),
or type a set code and collector number such as `TLA 58`. The set code and number are printed
at the bottom-left of most cards.

### Your list
- **Qty** shows how many copies you have. Use **+1** and **-1** on the selected rows.
- **Switch foil** flips the selected cards between foil and non-foil prices.
- **Remove** deletes the selected cards (it asks first).
- **Type**, **Color** and **Sort** change what is shown. The tiles at the top show the card
  count and the value of the current view and of the whole collection.
- **Export view** saves what you are looking at; **Export all** saves everything. **My files**
  opens your data folder.

### Settings and key binds
Click **Settings** (or press **Ctrl+comma**).

- **General:** update options and the update source.
- **Scanning:** how long Auto waits, and how sharp the picture must be before it counts as
  ready. The small `focus` number under the camera shows what your camera reaches.
- **Keys:** every action can have its own key. Defaults: Space snap, A switch Manual/Auto,
  T switch Non-foil/Foil for new scans, P phone, O photo file, N add by name or number,
  + and - change quantity, F switch foil, Delete remove, Ctrl+E export view, Ctrl+Q exit.
  Single-letter keys are ignored while you are typing in a box.

### Exit
Click **Exit** in the top right, press **Ctrl+Q**, or close the window.

---

## How it works

1. **Finding the card.** The app looks for a card-shaped outline in the camera picture, then
   straightens it into a flat, upright image, even if the card is tilted.
2. **Reading the name.** It brightens and sharpens the title strip and reads it with an
   offline text reader that is bundled inside the app. It tries several versions of the image
   and stops early once it is confident.
3. **Matching the name.** The text is compared with a local list of every Magic card name
   (downloaded from Scryfall once, then refreshed every couple of weeks), which fixes
   misreads such as `0` for `O`.
4. **Checking the artwork.** The artwork from your photo is compared with the official artwork
   of each guess. Name and artwork together decide the order of the guess list, which is why
   the list is far more reliable than reading the name alone. Each guess shows its `name` and
   `art` scores.
5. **Choosing the printing.** The same artwork comparison suggests which printing you hold.
   Prices come from that printing, foil or non-foil.
6. **You confirm.** Nothing is added until you click **Add card**.

### How the phone link works
The PC runs a small web page that only your local network can reach. The QR code contains its
address, which includes a long random secret, so other devices cannot guess it. Phone browsers
only allow camera access on secure `https://` pages, so the app creates its own certificate
(stored in `Documents/MTG Card Scanner/PhoneCertificate`). A self-signed certificate is
encrypted but not vouched for by a public authority, which is why the browser warns you the
first time. If the app can't create one, the phone page falls back to photo upload only. The
link works only while the phone window is open.

### Updating
The installer build publishes a numbered release on your GitHub repository each time it
succeeds. The app asks GitHub for the newest release, and when it is newer than the installed
one it shows **Update to x.y.z**. Clicking it downloads the installer, checks it is complete
(and matches its checksum when GitHub provides one), closes the app, upgrades it in place, and
reopens it. Your cards, settings and scan photos are not touched. The repository must be
**public** for this to work. Updating only works in the installed app, not when run from
source.

---

## Where your data lives

`Documents/MTG Card Scanner/`

| Item | What it is |
| --- | --- |
| `cards.json` | Your collection |
| `settings.json` | Your settings and key binds |
| `Scans/` | A photo of every card you scanned |
| `Exports/` | Default place for exported text files |
| `card_names.json` | Cached list of card names |
| `PhoneCertificate/` | The phone link's certificate and private key |
| `Debug/` | Only exists if you turn on *Save diagnostic pictures* |

---

## Warnings

**Accuracy**
- The card reader is not perfect. Dim light, glare, a blurry webcam, sleeves, worn or foil
  cards, unusual frames, and non-English cards can all cause wrong guesses. Check the guess
  and the printing before you click **Add card**.
- Many cards have dozens of printings with different prices. If the app picks the wrong
  printing, the value will be wrong. Compare the set and number with your card.
- Foil and special treatments (etched, borderless, showcase) are not detected from the photo.
  Choose foil or non-foil yourself.

**Prices**
- Prices come from Scryfall's data (market estimates, mainly US dollars) and can be out of date
  or missing (shown as `n/a`). They are not offers, buylist prices or appraisals. Condition,
  grading and demand change what a card actually sells for. Do not rely on this app to price
  a sale, trade, insurance claim or tax filing.

**Internet and privacy**
- The app needs the internet for names, artwork and prices. Card names and set numbers you scan
  are sent to Scryfall. Your photos are not uploaded; they are analysed on your PC.
- Scryfall limits how fast it can be asked for things, and the app keeps to its published
  limits. If you scan very fast you may see *Scryfall asked us to slow down*. Wait about 30
  seconds. Repeatedly ignoring Scryfall's limits can get an address blocked, so don't modify
  the app to bypass them.
- The update check contacts GitHub (`api.github.com`) and sends no personal data. You can turn
  it off in Settings.

**Phone link**
- Use it only on a network you trust, such as your own home Wi-Fi. Don't use it on public or
  shared Wi-Fi: anyone on the same network who gets the link could send pictures to your app.
- The first time, Windows will ask whether to allow the app through the firewall. Choose
  **Private networks** only.
- Phones and PCs on a guest network, or on routers with "client isolation", can't reach each
  other. Put both on the main Wi-Fi.
- The certificate warning on the phone is expected, but don't tap through that kind of warning
  on other websites.
- Keep the phone screen on and unlocked while scanning. iPhones may dim or lock the screen.
- Live scanning on the phone's browser has been tested here only with simulated data. If your
  phone refuses the camera, use the *Take a photo with the camera app* button on that page.
- Close the phone window when you are done; that turns the link off.

**Windows and security software**
- The installer is **not code-signed** (certificates cost money), so Windows SmartScreen shows
  "Windows protected your PC", and some antivirus programs may flag it. Only install copies you
  built yourself or downloaded from your own GitHub repository.
- The update button downloads and runs an installer from your repository's releases. Only
  people with write access to the repository can publish one, so keep that account secure
  (use two-factor authentication). If you don't want self-updating, turn off the startup check
  and don't click Update.

**Your data**
- Everything is stored in plain files. **Back up** `Documents/MTG Card Scanner/` if your
  collection matters: copy `cards.json` somewhere safe now and then. Uninstalling the app does
  not delete it, but deleting the folder does.
- *Remove*, and *-1* on a card with quantity 1, permanently delete rows. There is no undo.
- Scan photos can take up disk space over time. You can delete files in `Scans/`; the list
  keeps working.
- The *Save diagnostic pictures* option writes every scan's photos and scores to `Debug/`. It
  is for troubleshooting; turn it off afterwards and delete the folder.

**Camera**
- Close other apps that use the webcam (Zoom, Teams, camera apps) or the app may show
  *No camera found*. If you have several cameras, pick the right number under **Camera**.
- Some webcams ignore manual focus. Very cheap webcams may never be sharp enough for small
  text; a phone usually gives a much better picture.

**General**
- This software is provided as is, with no warranty. It is a hobby tool, not a professional
  grading or valuation service.
- Magic: The Gathering, its card names, artwork and symbols are property of Wizards of the
  Coast. Card data and images come from Scryfall. This project is not affiliated with either.

---

## Troubleshooting

| Problem | Try this |
| --- | --- |
| *No camera found* | Close other apps using the camera, try another camera number under **Camera**, or use Phone / Photo file |
| Status keeps saying *Blurry* | Add light, hold the card steadier, move it a bit further away, or lower the sharpness setting in **Settings > Scanning** |
| Wrong guesses | Use the best light you can, fill the frame, hold the card flat, and use your phone for scanning |
| No artwork thumbnails | Scryfall asked us to slow down; wait 30 seconds and scan again |
| Phone can't connect | Same Wi-Fi? Not a guest network? Firewall prompt allowed? Try opening the address shown in the phone window |
| Phone page says the camera is blocked | Allow camera access for the page in the browser settings, or use the camera-app button |
| *No release found* when updating | Make sure the GitHub repository is public and the **Build Windows installer** run finished with a green check |
| Update downloads but doesn't finish | Close any other copy of the app and click Update again |

If something odd happens, turn on **Camera > Save diagnostic pictures**, scan the card, and look
in `Documents/MTG Card Scanner/Debug/`. Each scan saves its photos and a `result.txt` listing
what was read and each guess's name and artwork scores.

---

## For the person who builds it (developer notes)

- The app is one Python file, `mtg_card_scanner.py` (Tkinter, OpenCV, RapidOCR, Pillow,
  requests, cryptography). Run from source with `pip install -r requirements.txt` then
  `python mtg_card_scanner.py`.
- **Building:** push the files to your GitHub repository's `main` branch (or click *Run
  workflow* on the **Actions** tab). The workflow builds the app with PyInstaller, wraps it
  with Inno Setup (`installer.iss`), and attaches `MTG-Card-Scanner-Setup.exe` to both the run's
  artifacts and a new **release**.
- **Versions:** the version is `APP_BASE_VERSION` in the Python file plus the workflow run
  number, for example `1.3.27`. Every successful build is therefore newer than the last, and
  you don't need to edit anything to publish an update. Raise `APP_BASE_VERSION` for bigger
  milestones.
- **Update source:** the workflow writes `build_info.txt` (version and repository name) into
  the app, so the Update button already knows where to look. A different repository can be set
  in **Settings > General**.
- The repository must be **public** for the Update button to work without a sign-in. If it
  must stay private, turn off update checks and distribute the installer yourself.
- Don't reduce `SLOW_GAP`/`FAST_GAP` in the code: they keep the app within Scryfall's published
  rate limits.
