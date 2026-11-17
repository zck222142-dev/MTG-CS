; Inno Setup script - builds MTG-Card-Scanner-Setup.exe from the PyInstaller output.
#define MyAppName "MTG Card Scanner"
#ifndef MyAppVersion
  #define MyAppVersion "1.0"
#endif
#define MyAppExe "MTG Card Scanner.exe"

[Setup]
AppId={{B7E1C3A2-5D4F-4C8E-9A61-2F3D7E8B9C10}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
DefaultDirName={autopf}\{#MyAppName}
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
OutputDir=installer_output
OutputBaseFilename=MTG-Card-Scanner-Setup
Compression=lzma2
SolidCompression=yes
; No administrator prompt: installs just for the current Windows user.
PrivilegesRequired=lowest
WizardStyle=modern
UninstallDisplayIcon={app}\{#MyAppExe}
; Lets an update run over a running copy: it closes the app, upgrades it in place, reopens it.
CloseApplications=yes
RestartApplications=no

[Tasks]
Name: "desktopicon"; Description: "Create a desktop shortcut"; GroupDescription: "Shortcuts:"

[Files]
Source: "dist\{#MyAppName}\*"; DestDir: "{app}"; Flags: recursesubdirs createallsubdirs ignoreversion
Source: "README.md"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{group}\{#MyAppName}"; Filename: "{app}\{#MyAppExe}"
Name: "{group}\Read me"; Filename: "{app}\README.md"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExe}"; Tasks: desktopicon

[Run]
Filename: "{app}\{#MyAppExe}"; Description: "Launch {#MyAppName}"; Flags: nowait postinstall skipifsilent
; After an in-app update (silent install) the app reopens by itself.
Filename: "{app}\{#MyAppExe}"; Flags: nowait; Check: WizardSilent
