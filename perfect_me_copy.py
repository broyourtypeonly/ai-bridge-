# AI Bridge repaired iteration: atomic rich-editor entry, strict line verification,
# non-interrupting Stop, and safer short-response completion detection.
"""
AI Bridge (macOS Tk-safe image/GitHub build) - your code lives in a GitHub repository, not on your laptop.

  * Reads selected text files from a local VS Code workspace or a GitHub branch.
  * Sends source/text files as fenced code; optionally attaches non-code reference files.
  * Uses Chrome CDP to submit one prompt to ChatGPT, Gemini and DeepSeek.
  * Waits 10 seconds after Start; Stop cancels bridge monitoring without cutting off website generation.
  * ChatGPT and Gemini receive one atomic rich-text insert; DeepSeek uses verified textarea chunks.
  * All three sites use a guarded CDP Send click, with a verified Enter-key fallback.
  * Collects newly generated replies, preserves code blocks, and downloads actual generated images.
  * Can upload downloaded image files to a connected GitHub branch after user confirmation.
  * Applies approved code edits locally with backups, or commits them to a GitHub branch.
  * Copies full browser/website status text (including errors) for easy sharing.

Browser mode uses Google Chrome via Chrome DevTools Protocol (CDP), with a persistent
AI Bridge profile and manual sign-in. A site is sent once: guarded Send click, or guarded
Enter-key fallback only when the prompt is still present and no submission is detected.
No AI API keys, Playwright or Selenium are used.

Requires: python -m pip install websocket-client certifi\nGitHub TLS: verified using OS trust roots plus certifi; never disables verification
Run: python3 -X faulthandler AI_Bridge_Three_AI_CDP_Cooldown.py
"""

import ast
import base64
import difflib
import faulthandler
import json
import mimetypes
import os
import queue
import re
import shutil
import subprocess
import ssl
import sys
import threading
import time
import tempfile
from datetime import datetime
from pathlib import Path
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from tkinter import filedialog, messagebox, scrolledtext, ttk

# Emit Python thread stacks to Terminal if a native extension crashes.
try:
    faulthandler.enable(all_threads=True)
except (RuntimeError, OSError):
    pass

API = "https://api.github.com"
MAX_FILE_BYTES = 300_000
MAX_GITHUB_MEDIA_BYTES = 15 * 1024 * 1024
BINARY_EXT = (
    ".png", ".jpg", ".jpeg", ".gif", ".bmp", ".ico", ".webp", ".svgz", ".pdf", ".zip", ".gz", ".tar", ".7z",
    ".mp3", ".mp4", ".mov", ".avi", ".wav", ".woff", ".woff2", ".ttf", ".otf", ".eot", ".exe", ".dll", ".so",
    ".dylib", ".class", ".jar", ".pyc", ".bin", ".lock", ".psd", ".xlsx", ".docx", ".pptx",
)
WARN_CHARS = 300_000

# Only files that are not practical to represent as source text are eligible for
# browser attachment. Code/config/text files always stay in the prompt as fenced code.
NON_CODE_FILETYPES = (
    ("Images", "*.png *.jpg *.jpeg *.gif *.bmp *.webp *.tif *.tiff *.heic *.avif"),
    ("PDF and office documents", "*.pdf *.doc *.docx *.ppt *.pptx *.xls *.xlsx *.odt *.ods *.odp"),
    ("Audio and video", "*.mp3 *.wav *.m4a *.aac *.flac *.ogg *.mp4 *.mov *.avi *.mkv *.webm"),
    ("Archives and other binary files", "*.zip *.7z *.rar *.tar *.gz *.bin *.stl *.obj"),
)
CODE_TEXT_EXTENSIONS = {
    ".py", ".pyw", ".js", ".jsx", ".ts", ".tsx", ".mjs", ".cjs", ".java", ".kt",
    ".kts", ".go", ".rs", ".c", ".h", ".cc", ".cpp", ".hpp", ".cs", ".fs",
    ".rb", ".php", ".swift", ".m", ".mm", ".r", ".R", ".dart", ".lua", ".pl",
    ".pm", ".sql", ".sh", ".bash", ".zsh", ".fish", ".ps1", ".bat", ".cmd",
    ".html", ".htm", ".css", ".scss", ".sass", ".less", ".vue", ".svelte",
    ".json", ".jsonc", ".yaml", ".yml", ".toml", ".ini", ".cfg", ".conf",
    ".xml", ".md", ".mdx", ".txt", ".rst", ".csv", ".tsv", ".log", ".diff",
    ".patch", ".properties", ".env", ".gradle",
    ".make", ".mk", ".dockerfile", ".tf", ".hcl", ".ipynb", ".graphql", ".gql",
}


def is_code_or_text_file(path):
    """Return True for files that should be embedded as readable prompt text."""
    path = Path(path)
    if path.suffix.lower() in {ext.lower() for ext in CODE_TEXT_EXTENSIONS}:
        return True
    mime, _ = mimetypes.guess_type(str(path))
    if mime and (mime.startswith("text/") or mime in {
        "application/json", "application/xml", "application/javascript",
        "application/x-javascript", "application/yaml", "application/toml",
    }):
        return True
    # Extensionless / unusual source files: classify by their actual bytes.
    try:
        sample = path.read_bytes()[:8192]
    except OSError:
        return False
    if not sample:
        return True
    if b"\x00" in sample:
        return False
    try:
        sample.decode("utf-8")
        return True
    except UnicodeDecodeError:
        return False

def build_ssl_context():
    """Build a verified TLS context using both OS roots and certifi roots.

    Do not disable certificate verification. Combining both stores supports
    Python.org macOS installs (system trust) and venvs (certifi trust).
    """
    context = ssl.create_default_context()
    sources = ["Python/system default CA store"]
    try:
        import certifi
        ca_file = certifi.where()
        if ca_file and os.path.isfile(ca_file):
            # Add certifi to the default trust store rather than replacing the
            # OS roots. This is important for Macs using custom Keychain CAs.
            context.load_verify_locations(cafile=ca_file)
            sources.append(f"certifi ({ca_file})")
        else:
            sources.append("certifi bundle unavailable")
    except ImportError:
        sources.append("certifi is not installed")
    except (OSError, ssl.SSLError) as exc:
        sources.append(f"certifi bundle could not be loaded ({type(exc).__name__})")
    stats = context.cert_store_stats()
    if not stats.get("x509_ca", 0):
        raise RuntimeError("No trusted CA certificates were loaded. Install/update certifi.")
    return context, "; ".join(sources)


SSL_CONTEXT, SSL_CA_DESCRIPTION = build_ssl_context()

AIS = {
    "ChatGPT": "https://chatgpt.com/",
    "Gemini": "https://gemini.google.com/app",
    "DeepSeek": "https://chat.deepseek.com/",
}

FILE_BLOCK = re.compile(
    r"^[ \t>#*_`-]*file(?:name)?\s*:\s*[`*_ ]*([^\n`*]+?)[`*_ ]*[ \t]*\n+"
    r"(?:[ \t]*(?:text|plain[ \t]+text|plaintext|json|javascript|typescript|python|"
    r"html|css|xml|yaml|yml|toml|ini|bash|shell)[ \t]*\n+)?"
    r"[ \t]*(`{3,})[^\n]*\n(.*?)\n[ \t]*\2",
    re.I | re.M | re.S,
)
ANY_BLOCK = re.compile(r"(`{3,})[^\n]*\n(.*?)\n[ \t]*\1", re.S)


class GitHubError(Exception):
    pass


def normalize(text):
    return text.replace("\r\n", "\n")


def normalize_repo(value):
    """Accept 'owner/name' or a full GitHub URL and return 'owner/name'."""
    v = value.strip()
    v = re.sub(r"^(https?://)?(www\.)?github\.com/", "", v)
    v = re.sub(r"\.git$", "", v).strip("/")
    parts = v.split("/")
    if len(parts) < 2 or not parts[0] or not parts[1]:
        raise GitHubError("Enter the repository as owner/name, for example: myname/myproject")
    return f"{parts[0]}/{parts[1]}"


def code_block(code):
    body = normalize(code).rstrip("\n")
    runs = re.findall(r"`+", body)
    fence = "`" * max(3, max((len(r) for r in runs), default=0) + 1)
    return f"{fence}\n{body}\n{fence}"


def parse_reply(text, names):
    """Return ({file_name: code}, [mentioned names that are not loaded])."""
    lower = {n.lower(): n for n in names}
    by_base = {}
    for n in names:
        by_base.setdefault(n.split("/")[-1].lower(), []).append(n)

    found, unknown = {}, []
    for m in FILE_BLOCK.finditer(text):
        raw = m.group(1).strip().replace("\\", "/")
        target = lower.get(raw.lower())
        if target is None:
            options = by_base.get(raw.split("/")[-1].lower(), [])
            target = options[0] if len(options) == 1 else None
        if target is None:
            unknown.append(raw)
        else:
            found[target] = m.group(3)

    if not found and len(names) == 1:
        blocks = [m.group(2) for m in ANY_BLOCK.finditer(text)]
        if blocks:
            found[names[0]] = max(blocks, key=len)
    return found, unknown




class CDPError(RuntimeError):
    """A browser automation error that is safe to show in the UI."""


class CDPPage:
    """Small synchronous Chrome DevTools Protocol client for one page target."""
    def __init__(self, target):
        try:
            import websocket
        except ImportError:
            raise CDPError(
                "Missing dependency websocket-client. Install with: "
                "python3 -m pip install websocket-client certifi"
            ) from None
        self.target = target
        self.ws = websocket.create_connection(
            target["webSocketDebuggerUrl"], timeout=12,
            suppress_origin=True, enable_multithread=True,
        )
        self._next_id = 0
        self._lock = threading.Lock()

    def call(self, method, params=None, timeout=12):
        with self._lock:
            self._next_id += 1
            command_id = self._next_id
            self.ws.settimeout(timeout)
            self.ws.send(json.dumps({
                "id": command_id, "method": method, "params": params or {}
            }))
            deadline = time.monotonic() + timeout
            while time.monotonic() < deadline:
                try:
                    message = json.loads(self.ws.recv())
                except Exception as exc:
                    raise CDPError(f"CDP connection failed: {exc}") from None
                if message.get("id") != command_id:
                    continue
                if "error" in message:
                    raise CDPError(message["error"].get("message", "CDP command failed"))
                return message.get("result", {})
            raise CDPError(f"Timed out waiting for CDP command: {method}")

    def evaluate(self, expression, timeout=12):
        result = self.call("Runtime.evaluate", {
            "expression": expression,
            "returnByValue": True,
            "awaitPromise": True,
            "userGesture": True,
        }, timeout=timeout)
        if result.get("exceptionDetails"):
            detail = result["exceptionDetails"].get("text", "JavaScript evaluation failed")
            raise CDPError(detail)
        return result.get("result", {}).get("value")

    def close(self):
        try:
            self.ws.close()
        except Exception:
            pass


class BrowserIntegration:
    """Chrome CDP automation using a persistent, dedicated profile and manual login."""
    PROFILE = Path.home() / ".ai_bridge_chrome_profile"
    PORT = 9222
    PRE_SEND_COOLDOWN_SECONDS = 10
    SITE_VISIT_SECONDS = 2.0  # each website is shown for exactly this long after the cooldown
    RESPONSE_TIMEOUT_SECONDS = 60  # per site, counted from the moment its prompt was submitted
    COMPOSERS = {
        "ChatGPT": {
            # ChatGPT has shipped several composer variants. Prefer stable IDs/test IDs,
            # then fall back to accessible contenteditable editors.
            "selectors": [
                'div.ProseMirror[contenteditable="true"][aria-label="Ask ChatGPT"]',
                '#prompt-textarea[contenteditable="true"]',
                'div#prompt-textarea',
                '[data-testid="prompt-textarea"][contenteditable="true"]',
                '[contenteditable="true"][aria-label="Ask ChatGPT"]',
                '[contenteditable="true"][aria-label*="ChatGPT" i]',
                '[contenteditable="true"][data-placeholder*="Ask" i]',
                '[role="textbox"][contenteditable="true"]',
                'textarea#prompt-textarea',
                'textarea[placeholder*="Message" i]',
            ],
            "timeout": 25,
        },
        "Gemini": {
            "selectors": [
                'div.ql-editor[contenteditable="true"][aria-label="Enter a prompt for Gemini"]',
                'div[contenteditable="true"][role="textbox"][data-placeholder="Ask Gemini"]',
            ],
            "timeout": 3,
        },
        "DeepSeek": {
            "selectors": [
                'textarea[placeholder="Message DeepSeek"][name="search"]',
                'textarea[placeholder="Message DeepSeek"]',
            ],
            "timeout": 3,
        },
    }
    RESPONSES = {
        # The first selector for each site is its strongest assistant-message marker.
        # Fallbacks are filtered again in _response_snapshot before being accepted.
        "ChatGPT": [
            '[data-message-author-role="assistant"]',
            '[data-message-author-role="assistant"] .markdown',
            '[data-message-author-role="assistant"] .prose',
            'article[data-testid^="conversation-turn"] [data-message-author-role="assistant"]',
            '[data-testid*="conversation-turn"] [data-message-author-role="assistant"]',
            '[data-turn="assistant"]',
        ],
        "Gemini": [
            'model-response',
            'model-response .markdown-main-panel',
            'model-response .response-content',
            '[data-testid*="model-response"]',
            '[data-test-id*="model-response"]',
            '[data-message-author-role="assistant"]',
            '.response-container',
            'message-content',
            '[class*="generated-image"]',
        ],
        "DeepSeek": [
            '[data-message-author-role="assistant"]',
            '.ds-markdown',
            '[class*="ds-markdown"]',
            '[class*="assistant"] [class*="markdown"]',
            '[data-testid*="assistant"]',
            '[class*="assistant-message"]',
            '[class*="message-content"]',
            '[class*="generated-image"]',
        ],
    }

    def __init__(self, callback):
        self.callback = callback
        self.started = False
        self._starting = False
        self._pages = {}
        self._targets = {}
        self._baseline = {}
        self._baseline_media = {}
        self._prompt_anchor = {}
        self._response_media = {}
        self.result_dir = Path.home() / "Downloads" / "AI Bridge Results"
        self._submitted = set()
        self._prepared = set()
        self._lock = threading.Lock()
        self._collecting = False
        self._cancel_event = threading.Event()
        self._diag_lock = threading.Lock()
        self._diag_enabled = False
        self._diag_path = None

    @property
    def diagnostic_path(self):
        return self._diag_path

    def configure_diagnostics(self, enabled=True):
        """Enable a privacy-conscious diagnostic log (never records prompt/file contents)."""
        enabled = bool(enabled)
        was_enabled = self._diag_enabled
        if enabled and self._diag_path is None:
            root = Path.home() / "Downloads" / "AI Bridge Results" / "Diagnostics"
            root.mkdir(parents=True, exist_ok=True)
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            self._diag_path = root / f"AI_Bridge_diagnostics_{stamp}.txt"
            header = (
                "AI Bridge diagnostic log\n"
                f"Started: {datetime.now().astimezone().isoformat(timespec='seconds')}\n"
                f"Python: {sys.version.split()[0]}\n"
                f"Sites: {', '.join(AIS)}\n"
                "Privacy: prompt text, file contents, passwords, cookies and browser storage are NOT logged.\n"
                "This log contains technical event metadata, timings, counts and error messages only.\n"
                + "=" * 78 + "\n"
            )
            self._diag_path.write_text(header, encoding="utf-8")
        if not enabled and self._diag_enabled and self._diag_path:
            self._diag("SYSTEM", "Diagnostic logging disabled by user")
        self._diag_enabled = enabled
        if enabled and not was_enabled:
            self._diag("SYSTEM", "Diagnostic logging enabled", metadata_only=True)
        self.callback("diagnostics", {
            "enabled": self._diag_enabled,
            "path": str(self._diag_path) if self._diag_path else "",
        })
        return self._diag_path

    def _diag(self, ai, event, **fields):
        """Append one safe diagnostic event. Callers must pass metadata, never content."""
        if not self._diag_enabled or not self._diag_path:
            return

        def clean(value, limit=500):
            if value is None:
                return "-"
            if isinstance(value, bool):
                return str(value).lower()
            if isinstance(value, (int, float)):
                return str(value)
            value = str(value).replace("\r", " ").replace("\n", " ")
            value = re.sub(r"(?i)(authorization|password|passwd|secret|api[_ -]?key|access[_ -]?token)\s*[:=]\s*[^ ,;]+", r"\1=[REDACTED]", value)
            value = re.sub(r"(?i)\bBearer\s+[A-Za-z0-9._~+/-]+=*", "Bearer [REDACTED]", value)
            value = re.sub(r"https?://[^\s]+", "[URL REDACTED]", value)
            return value[:limit] + ("…" if len(value) > limit else "")

        def clean_field(key, value):
            if re.search(r"(?i)(authorization|password|passwd|secret|api[_ -]?key|access[_ -]?token|cookie)", str(key)):
                return "[REDACTED]"
            return clean(value)

        timestamp = datetime.now().astimezone().isoformat(timespec="milliseconds")
        flat = {}
        for key, value in fields.items():
            if isinstance(value, dict):
                # Structured values (e.g. DOM probe counts) become readable key_subkey=value pairs
                # instead of one long repr that used to be cut off mid-way.
                for sub_key, sub_value in value.items():
                    flat[f"{key}_{sub_key}"] = sub_value
            else:
                flat[key] = value
        suffix = " ".join(f"{key}={clean_field(key, value)}" for key, value in sorted(flat.items()))
        line = f"[{timestamp}] [{clean(ai)}] {clean(event)}"
        if suffix:
            line += " | " + suffix
        try:
            with self._diag_lock:
                with self._diag_path.open("a", encoding="utf-8") as handle:
                    handle.write(line + "\n")
        except OSError:
            # Diagnostics must never interrupt browser automation.
            pass

    def set_result_dir(self, path):
        self.result_dir = Path(path).expanduser().resolve()

    @staticmethod
    def _chrome_candidates():
        candidates = []
        if sys.platform == "darwin":
            candidates += [
                "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
                str(Path.home() / "Applications/Google Chrome.app/Contents/MacOS/Google Chrome"),
            ]
        elif os.name == "nt":
            for base in (os.environ.get("PROGRAMFILES"), os.environ.get("PROGRAMFILES(X86)"),
                         os.environ.get("LOCALAPPDATA")):
                if base:
                    candidates.append(str(Path(base) / "Google/Chrome/Application/chrome.exe"))
        else:
            for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
                found = shutil.which(name)
                if found:
                    candidates.append(found)
        return [c for c in candidates if Path(c).is_file()]

    def _json_endpoint(self, path):
        url = f"http://127.0.0.1:{self.PORT}{path}"
        try:
            with urllib.request.urlopen(url, timeout=2) as response:
                return json.loads(response.read().decode("utf-8"))
        except Exception:
            return None

    def _wait_for_browser(self, timeout=25):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            targets = self._json_endpoint("/json")
            if isinstance(targets, list):
                return targets
            time.sleep(0.4)
        raise CDPError(
            f"Chrome did not expose CDP on 127.0.0.1:{self.PORT}. "
            "Close other AI Bridge Chrome instances and try again."
        )

    def _find_targets(self, targets):
        found = {}
        for ai, url in AIS.items():
            host = urllib.parse.urlparse(url).hostname
            matches = [
                t for t in targets
                if t.get("type") == "page"
                and urllib.parse.urlparse(t.get("url", "")).hostname == host
                and t.get("webSocketDebuggerUrl")
            ]
            if matches:
                found[ai] = matches[0]
        return found

    def start(self):
        if self.started:
            self.callback("phase", "The AI Bridge Chrome sessions are already open.")
            return
        if self._starting:
            self.callback("phase", "Chrome startup is already in progress.")
            return
        self._starting = True
        def worker():
            self._diag("SYSTEM", "Browser startup requested", cdp_port=self.PORT, dedicated_profile_configured=True)
            try:
                if self._collecting:
                    raise CDPError("Wait for the current response collection to finish before reconnecting.")
                for old_page in self._pages.values():
                    old_page.close()
                self._pages.clear()
                # Reuse an already-running AI Bridge CDP instance only when its
                # DevToolsActivePort file confirms the dedicated profile.
                targets = self._json_endpoint("/json")
                if isinstance(targets, list):
                    active_port = self.PROFILE / "DevToolsActivePort"
                    recorded_port = ""
                    for _wait in range(8):  # up to ~3s: the file can lag behind a freshly started Chrome
                        try:
                            recorded_port = active_port.read_text(encoding="utf-8").splitlines()[0].strip()
                        except (OSError, IndexError):
                            recorded_port = ""
                        if recorded_port == str(self.PORT):
                            break
                        time.sleep(0.4)
                    if recorded_port != str(self.PORT):
                        self._diag("SYSTEM", "Dedicated-profile check failed",
                                   active_port_file_exists=active_port.exists(),
                                   recorded_port=recorded_port or "(empty)", expected_port=self.PORT)
                        raise CDPError(
                            f"Port {self.PORT} is already serving a Chrome instance that cannot be "
                            "confirmed as the dedicated AI Bridge profile. Close that debugging "
                            "Chrome instance and restart AI Bridge."
                        )
                if not isinstance(targets, list):
                    chrome = self._chrome_candidates()
                    if not chrome:
                        raise CDPError(
                            "Google Chrome executable was not found. Install Chrome or "
                            "adjust the executable detection paths."
                        )
                    self.PROFILE.mkdir(parents=True, exist_ok=True)
                    args = [
                        chrome[0], f"--remote-debugging-port={self.PORT}",
                        "--remote-debugging-address=127.0.0.1",
                        f"--user-data-dir={self.PROFILE}", "--no-first-run",
                        "--no-default-browser-check",
                        # AI Bridge sits on top of Chrome. Without these, Chrome treats covered/background
                        # tabs as hidden and throttles or pauses them, so a streaming ChatGPT reply stops
                        # updating in the DOM and is never "seen" (or is seen very late).
                        "--disable-backgrounding-occluded-windows",
                        "--disable-renderer-backgrounding",
                        "--disable-background-timer-throttling",
                        "--disable-features=CalculateNativeWinOcclusion,IntensiveWakeUpThrottling",
                    ] + list(AIS.values())
                    subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    targets = self._wait_for_browser()
                    settle_deadline = time.monotonic() + 12
                    while time.monotonic() < settle_deadline:
                        targets = self._json_endpoint("/json") or targets
                        if len(self._find_targets(targets)) == len(AIS):
                            break
                        time.sleep(0.4)
                found = self._find_targets(targets)
                # Open any missing site in the controlled Chrome instance.
                for ai, url in AIS.items():
                    if ai not in found:
                        request = urllib.request.Request(
                            f"http://127.0.0.1:{self.PORT}/json/new?{urllib.parse.quote(url, safe=':/?=&')}",
                            method="PUT",
                        )
                        try:
                            with urllib.request.urlopen(request, timeout=5) as response:
                                target = json.loads(response.read().decode("utf-8"))
                            if target.get("webSocketDebuggerUrl"):
                                found[ai] = target
                        except Exception as exc:
                            self.callback("site_status", {
                                "ai": ai, "status": f"Tab could not be opened: {exc}"
                            })
                self._targets = found
                self.started = True
                self._diag("SYSTEM", "Browser tabs ready", available_sites=", ".join(found),
                           missing_sites=", ".join(ai for ai in AIS if ai not in found))
                self.callback("ready", {
                    "browser": "Google Chrome",
                    "profile": str(self.PROFILE),
                    "sites": list(found),
                })
                for ai in AIS:
                    state = "Tab ready — sign in if needed" if ai in found else "Tab unavailable"
                    self.callback("site_status", {"ai": ai, "status": state})
                self._starting = False
            except Exception as exc:
                self._diag("SYSTEM", "Browser startup failed", error_type=type(exc).__name__, error=str(exc))
                self.callback("error", str(exc))
                self._starting = False
        threading.Thread(target=worker, daemon=True, name="ai-bridge-chrome-start").start()

    def _page(self, ai):
        # Return a live CDP page, refreshing stale Chrome target IDs before reconnecting.
        existing = self._pages.get(ai)
        if existing is not None:
            try:
                # A quick round-trip detects a closed socket or tab that was replaced.
                existing.evaluate("location.href", timeout=3)
                return existing
            except Exception as exc:
                self._diag(ai, "Cached CDP page is stale; refreshing target", error=str(exc))
                try:
                    existing.close()
                except Exception:
                    pass
                self._pages.pop(ai, None)

        started = time.monotonic()
        last_error = None
        preferred_id = (self._targets.get(ai) or {}).get("id")
        for attempt in range(1, 4):
            # /json/list is the current target list. The old in-memory WebSocket URL
            # can point to a target Chrome has already discarded (No such target id).
            targets = self._json_endpoint("/json/list")
            if not isinstance(targets, list):
                targets = self._json_endpoint("/json")
            fresh = self._find_targets(targets) if isinstance(targets, list) else {}
            target = fresh.get(ai)
            if target is None:
                target = self._targets.get(ai)
            if target is None:
                last_error = CDPError("Chrome tab was not found. Click Start browser sessions again.")
                time.sleep(0.25 * attempt)
                continue
            # If the saved target still exists, retain it; otherwise use the newly
            # discovered target for the same site's host.
            if preferred_id and target.get("id") != preferred_id:
                self._diag(ai, "CDP target ID refreshed", old_target_id=preferred_id,
                           new_target_id=target.get("id"), attempt=attempt)
            self._targets[ai] = target
            host = urllib.parse.urlparse(target.get("url", "")).hostname or "unknown"
            self._diag(ai, "CDP page connection started", host=host, attempt=attempt)
            page = None
            try:
                page = CDPPage(target)
                page.call("Runtime.enable", timeout=5)
                try:
                    # Makes the page behave as focused even when Chrome's window is not the OS-active one
                    # (AI Bridge takes focus back after the site visit).
                    page.call("Emulation.setFocusEmulationEnabled", {"enabled": True}, timeout=5)
                except Exception as exc:
                    self._diag(ai, "Focus emulation unavailable", error=str(exc))
                page.evaluate("location.href", timeout=5)
                self._pages[ai] = page
                self._diag(ai, "CDP page connected", host=host, attempt=attempt,
                           elapsed_ms=int((time.monotonic()-started)*1000))
                return page
            except Exception as exc:
                last_error = exc
                self._diag(ai, "CDP page connection failed", attempt=attempt,
                           error_type=type(exc).__name__, error=str(exc))
                if page is not None:
                    page.close()
                self._pages.pop(ai, None)
                time.sleep(0.25 * attempt)
        raise CDPError(
            f"Could not connect to the current {ai} Chrome tab after refreshing its CDP target three times: {last_error}"
        )

    def stop(self):
        """Cancel AI Bridge automation/monitoring without interrupting website generation."""
        self._cancel_event.set()
        self._diag("SYSTEM", "AI Bridge run cancelled; website generation deliberately left running")
        self.callback(
            "phase",
            "AI Bridge automation stopped. ChatGPT, Gemini and DeepSeek are left generating; use Collect replies after they finish."
        )
        self.callback("stopped", {"sites": [], "generations_left_running": True})

    @staticmethod
    def _js_string(value):
        return json.dumps(value, ensure_ascii=False)

    def _detect_composer(self, page, ai):
        """Find the live editor and return a unique DOM path, not a brittle site selector."""
        config = self.COMPOSERS[ai]
        selectors = self._js_string(config["selectors"])
        script = f"""(() => {{
          const ai = {self._js_string(ai)};
          const preferred = {selectors};
          const visible = el => {{
            if (!el) return false;
            const r=el.getBoundingClientRect(), s=getComputedStyle(el);
            return r.width>20 && r.height>12 && s.display!=='none' && s.visibility!=='hidden'
              && el.getAttribute('aria-hidden')!=='true';
          }};
          const editable = el => el && (el.isContentEditable || /^(TEXTAREA|INPUT)$/.test(el.tagName));
          const path = el => {{
            const parts=[];
            while (el && el.nodeType===1 && el!==document.body) {{
              let part=el.tagName.toLowerCase();
              if (el.id) {{ part += '#'+CSS.escape(el.id); parts.unshift(part); break; }}
              const testid=el.getAttribute('data-testid');
              const aria=el.getAttribute('aria-label');
              const ph=el.getAttribute('placeholder');
              if (testid) part += '[data-testid="'+CSS.escape(testid)+'"]';
              else if (aria) part += '[aria-label="'+CSS.escape(aria)+'"]';
              else if (ph) part += '[placeholder="'+CSS.escape(ph)+'"]';
              else {{
                const siblings=el.parentElement ? [...el.parentElement.children].filter(x=>x.tagName===el.tagName) : [];
                if (siblings.length>1) part += ':nth-of-type('+(siblings.indexOf(el)+1)+')';
              }}
              parts.unshift(part); el=el.parentElement;
            }}
            return parts.join(' > ');
          }};
          let candidates=[];
          for (const sel of preferred) {{
            try {{
              for (let el of document.querySelectorAll(sel)) {{
                if (el.matches('p[data-placeholder]')) el=el.closest('[contenteditable="true"]') || el.parentElement;
                if (editable(el) && visible(el) && !candidates.includes(el)) candidates.push(el);
              }}
            }} catch(e) {{}}
          }}
          if (!candidates.length) {{
            let pool=[...document.querySelectorAll('[contenteditable="true"],textarea,input')].filter(el=>editable(el)&&visible(el));
            const score=el => {{
              const t=[el.getAttribute('aria-label'),el.getAttribute('data-placeholder'),el.getAttribute('placeholder'),el.innerText].filter(Boolean).join(' ').toLowerCase();
              let n=0;
              if (ai==='ChatGPT' && (el.id==='prompt-textarea' || /ask chatgpt|message chatgpt|send a message|ask anything|message/i.test(t))) n+=12;
              if (ai==='Gemini' && /prompt|message|gemini|ask/.test(t)) n+=8;
              if (ai==='DeepSeek' && /message|deepseek|ask/.test(t)) n+=8;
              if (el.tagName==='TEXTAREA') n+=3;
              if (el.getAttribute('contenteditable')==='true' || el.isContentEditable) n+=3;
              if (el.getAttribute('role')==='textbox') n+=2;
              if (el.closest('form')) n+=2;
              return n;
            }};
            pool.sort((a,b)=>score(b)-score(a));
            if (pool.length && score(pool[0])>0 && (pool.length===1 || score(pool[0])>score(pool[1]))) candidates=[pool[0]];
          }}
          if (!candidates.length) return {{ok:false,url:location.href,title:document.title}};
          // Prefer the most specific editor (not a nested wrapper) when selectors overlap.
          candidates.sort((a,b)=>a.getBoundingClientRect().width*a.getBoundingClientRect().height - b.getBoundingClientRect().width*b.getBoundingClientRect().height);
          const el=candidates[0];
          const r=el.getBoundingClientRect();
          // Prefer a stable selector that matches ONLY this editor. A positional DOM path
          // (nth-of-type) breaks when the site inserts a sibling after a large paste, which
          // made the composer look "missing" right after the prompt was inserted.
          let stableSelector='';
          for (const sel of preferred) {{
            try {{ const m=document.querySelectorAll(sel); if (m.length===1 && m[0]===el) {{ stableSelector=sel; break; }} }} catch(e) {{}}
          }}
          return {{ok:true,selector:stableSelector||path(el),tag:el.tagName,aria:el.getAttribute('aria-label')||'',
            placeholder:el.getAttribute('placeholder')||'',id:el.id||'',role:el.getAttribute('role')||'',
            contenteditable:!!el.isContentEditable,x:r.left+r.width/2,y:r.top+r.height/2}};
        }})()"""
        started = time.monotonic()
        self._diag(ai, "Composer detection started", preferred_selector_count=len(config["selectors"]))
        deadline = started + max(config["timeout"], 8)
        last = None
        while time.monotonic() < deadline:
            try:
                last = page.evaluate(script)
            except Exception as exc:
                self._diag(ai, "Composer probe CDP error", error_type=type(exc).__name__, error=str(exc))
                raise
            if last and last.get("ok"):
                self._diag(ai, "Composer detected", tag=last.get("tag"), element_id=last.get("id"),
                           role=last.get("role"), aria=last.get("aria"),
                           placeholder=last.get("placeholder"), elapsed_ms=int((time.monotonic()-started)*1000))
                return last
            time.sleep(0.3)
        self._diag(ai, "Composer detection timed out", elapsed_ms=int((time.monotonic()-started)*1000),
                   last_probe_ok=bool(last and last.get("ok")))
        raise CDPError(
            f"Composer not detected within {max(config['timeout'], 8)}s. "
            "Check sign-in and wait for the chat page to finish loading."
        )

    def _file_input_nodes(self, page):
        """Return live file inputs, including open shadow roots, with fresh backend ids."""
        try:
            try:
                page.call("DOM.enable", {})
            except Exception:
                pass
            document = page.call("DOM.getDocument", {"depth": -1, "pierce": True})
            root = document.get("root", {})
            found, seen = [], set()

            def visit(node):
                if not isinstance(node, dict):
                    return
                node_id = node.get("nodeId")
                if node_id and node_id not in seen:
                    seen.add(node_id)
                    if node.get("nodeName", "").lower() == "input":
                        raw = node.get("attributes", [])
                        attrs = {str(raw[i]).lower(): str(raw[i + 1])
                                 for i in range(0, len(raw) - 1, 2)}
                        if attrs.get("type", "").lower() == "file" and "disabled" not in attrs:
                            found.append({"nodeId": node_id,
                                          "backendNodeId": node.get("backendNodeId"),
                                          "attributes": attrs})
                for key in ("children", "shadowRoots"):
                    for child in node.get(key, []) or []:
                        visit(child)
                if node.get("templateContent"):
                    visit(node["templateContent"])

            visit(root)
            return found
        except Exception:
            try:
                root_id = page.call("DOM.getDocument", {"depth": -1}).get("root", {}).get("nodeId")
                node_ids = page.call("DOM.querySelectorAll", {
                    "nodeId": root_id, "selector": 'input[type="file"]'
                }).get("nodeIds", [])
                result = []
                for node_id in node_ids:
                    try:
                        node = page.call("DOM.describeNode", {"nodeId": node_id}).get("node", {})
                        raw = node.get("attributes", [])
                        attrs = {str(raw[i]).lower(): str(raw[i + 1])
                                 for i in range(0, len(raw) - 1, 2)}
                        if attrs.get("type", "").lower() == "file" and "disabled" not in attrs:
                            result.append({"nodeId": node_id, "backendNodeId": node.get("backendNodeId"),
                                           "attributes": attrs})
                    except Exception:
                        continue
                return result
            except Exception:
                return []

    @staticmethod
    def _accepts_file(accept, path):
        accept = (accept or "").strip().lower()
        if not accept or accept == "*/*":
            return True
        suffix = Path(path).suffix.lower()
        mime = mimetypes.guess_type(str(path))[0] or "application/octet-stream"
        for token in (part.strip() for part in accept.split(",")):
            if not token:
                continue
            if token.startswith(".") and suffix == token:
                return True
            if token.endswith("/*") and mime.startswith(token[:-1]):
                return True
            if token == mime.lower():
                return True
        return False

    def _open_upload_picker(self, page, ai):
        """Open only an attachment control near the detected chat composer."""
        detected = self._detect_composer(page, ai)
        composer_selector = self._js_string(detected["selector"])
        script = f"""(() => {{
          const composer=document.querySelector({composer_selector});
          if (!composer) return {{ok:false,reason:'Chat composer is no longer present'}};
          const cr=composer.getBoundingClientRect();
          const visible=el=>{{const r=el.getBoundingClientRect(),s=getComputedStyle(el);
            return r.width>0&&r.height>0&&s.display!=='none'&&s.visibility!=='hidden';}};
          const buttons=[...document.querySelectorAll('button,[role="button"]')].filter(visible);
          const matches=buttons.map(el=>{{
            const label=[el.innerText,el.getAttribute('aria-label'),el.getAttribute('title'),
              el.getAttribute('data-testid'),el.getAttribute('data-state')].filter(Boolean).join(' ').toLowerCase();
            if (!/(attach|attachment|upload|add files?|add image|insert files?|choose files?|paperclip)/.test(label)) return null;
            if (/(remove|delete|clear|close|stop|cancel)/.test(label)) return null;
            const r=el.getBoundingClientRect();
            const dy=Math.abs((r.top+r.height/2)-(cr.top+cr.height/2));
            const dx=Math.abs((r.left+r.width/2)-(cr.left+Math.min(cr.width,180)));
            if (dy>Math.max(190,cr.height*2.5) || r.left<cr.left-110 || r.left>cr.right+180) return null;
            let score=20-dy*0.06-dx*0.015;
            if (/attach|upload|add file|choose file/.test(label)) score+=25;
            if (el.closest('form') && composer.closest('form')===el.closest('form')) score+=12;
            return {{x:r.left+r.width/2,y:r.top+r.height/2,score,label}};
          }}).filter(Boolean).sort((a,b)=>b.score-a.score);
          if (!matches.length) return {{ok:false,reason:'No clearly labelled attachment control near the composer was found'}};
          if (matches.length>1 && matches[0].score-matches[1].score<2)
            return {{ok:false,reason:'Attachment control near the composer is ambiguous'}};
          return {{ok:true,x:matches[0].x,y:matches[0].y,label:matches[0].label}};
        }})()"""
        control = page.evaluate(script)
        if not control or not control.get("ok"):
            return False
        page.call("Input.dispatchMouseEvent", {
            "type": "mousePressed", "x": control["x"], "y": control["y"],
            "button": "left", "clickCount": 1,
        })
        page.call("Input.dispatchMouseEvent", {
            "type": "mouseReleased", "x": control["x"], "y": control["y"],
            "button": "left", "clickCount": 1,
        })
        # Some sites reveal the file input only after opening the attachment menu.
        deadline = time.monotonic() + 3.5
        while time.monotonic() < deadline:
            if self._file_input_nodes(page):
                return True
            time.sleep(0.2)
        return False

    def _wait_for_upload_processing(self, page, ai, timeout=28):
        """Wait for visible upload-progress indicators to settle before sending."""
        try:
            composer_selector = self._js_string(self._detect_composer(page, ai)["selector"])
        except Exception:
            composer_selector = '"body"'
        script = f"""(() => {{
          const composer=document.querySelector({composer_selector});
          const region=(composer&&composer.closest('form'))||(composer&&composer.parentElement&&composer.parentElement.parentElement)||document.body;
          const visible=el=>{{const r=el.getBoundingClientRect(),s=getComputedStyle(el);
            return r.width>0&&r.height>0&&s.display!=='none'&&s.visibility!=='hidden'&&Number(s.opacity)!==0;}};
          const body=region.innerText||'';
          const textPending=/(uploading|upload in progress|preparing (?:the )?(?:file|attachment)|processing (?:the )?(?:file|attachment)|scanning (?:the )?(?:file|attachment))/i.test(body);
          const bars=[...region.querySelectorAll('[role="progressbar"],progress')].filter(visible);
          const pendingBars=bars.some(el=>{{
            const value=Number(el.getAttribute('aria-valuenow'));
            const max=Number(el.getAttribute('aria-valuemax'))||100;
            return !Number.isFinite(value)||value<max;
          }});
          const failed=/(failed to upload|upload failed|could not upload|couldn't upload|unsupported file type)/i.test(body);
          return {{pending:textPending||pendingBars,failed}};
        }})()"""
        deadline = time.monotonic() + timeout
        settled = 0
        while time.monotonic() < deadline:
            state = page.evaluate(script, timeout=10) or {}
            if state.get("failed"):
                raise CDPError(f"{ai} reported that a selected file could not be uploaded.")
            if not state.get("pending"):
                settled += 1
                if settled >= 2:
                    return True
            else:
                settled = 0
                self.callback("site_status", {
                    "ai": ai, "status": "Website is processing the selected file(s)… prompt will send after upload settles."
                })
            time.sleep(0.6)
        raise CDPError(f"{ai} still shows an upload in progress after {timeout} seconds.")

    def _attach_non_code_files(self, page, ai, attachments):
        """Attach selected non-code files, refreshing CDP node handles after rerenders."""
        paths = [str(Path(item).expanduser().resolve()) for item in attachments]
        total_bytes = sum(Path(path).stat().st_size for path in paths if Path(path).is_file())
        self._diag(ai, "Attachment workflow started", file_count=len(paths), total_bytes=total_bytes)
        for path in paths:
            item = Path(path)
            if not item.is_file():
                raise CDPError(f"Attachment no longer exists: {item.name}")
            if is_code_or_text_file(item):
                raise CDPError(f"{item.name} is readable code/text; it belongs in the prompt, not the upload control.")

        inputs = self._file_input_nodes(page)
        self._diag(ai, "File inputs inspected", visible_input_count=len(inputs))
        if not inputs:
            picker_opened = self._open_upload_picker(page, ai)
            self._diag(ai, "Attachment picker opened", success=bool(picker_opened))
            time.sleep(0.25)
            inputs = self._file_input_nodes(page)
            self._diag(ai, "File inputs rechecked after picker", visible_input_count=len(inputs))
        if not inputs:
            self._diag(ai, "No file input available for selected attachment")
            raise CDPError("The site did not expose a usable file input; continuing with the prompt without the attachment.")

        # Prefer file inputs whose accept attribute matches the selected media.
        remaining = list(paths)
        selected = []
        while remaining:
            fresh_inputs = self._file_input_nodes(page)  # refresh after every React/UI update
            choice = None
            compatible_sets = []
            for candidate in fresh_inputs:
                accept = candidate["attributes"].get("accept", "")
                compatible = [path for path in remaining if self._accepts_file(accept, path)]
                if compatible:
                    compatible_sets.append((candidate, compatible))
            if compatible_sets:
                # Prefer the input that accepts the largest share; do not rely on
                # stale DOM node IDs retained across a page rerender.
                compatible_sets.sort(key=lambda pair: len(pair[1]), reverse=True)
                choice, compatible = compatible_sets[0]
                batch = compatible if "multiple" in choice["attributes"] else [compatible[0]]
                self._diag(ai, "Compatible file input selected",
                           accept=choice["attributes"].get("accept", "(any)"),
                           input_name=choice["attributes"].get("name", ""),
                           multiple="multiple" in choice["attributes"],
                           backend_node_available=bool(choice.get("backendNodeId")))
            else:
                names = ", ".join(Path(path).name for path in remaining)
                raise CDPError(f"No upload input accepts the selected file(s): {names}")

            # Use backendNodeId where available. Frontend nodeIds are invalidated
            # by common React rerenders (the Gemini 'No node with given id' failure).
            last_error = None
            assigned = False
            for attempt in range(3):
                if attempt:
                    time.sleep(0.35 * attempt)
                refreshed = self._file_input_nodes(page)
                # Find the same compatible input from a fresh DOM snapshot.
                fresh_choice = None
                for candidate in refreshed:
                    attrs = candidate["attributes"]
                    if all(self._accepts_file(attrs.get("accept", ""), path) for path in batch):
                        fresh_choice = candidate
                        break
                if fresh_choice is None:
                    self._open_upload_picker(page, ai)
                    refreshed = self._file_input_nodes(page)
                    for candidate in refreshed:
                        attrs = candidate["attributes"]
                        if all(self._accepts_file(attrs.get("accept", ""), path) for path in batch):
                            fresh_choice = candidate
                            break
                if fresh_choice is None:
                    last_error = CDPError("The upload input was replaced or disappeared while opening the attachment picker.")
                    continue
                try:
                    params = {"files": batch}
                    if fresh_choice.get("backendNodeId"):
                        params["backendNodeId"] = fresh_choice["backendNodeId"]
                    else:
                        params["nodeId"] = fresh_choice["nodeId"]
                    page.call("DOM.setFileInputFiles", params, timeout=20)
                    self._diag(ai, "CDP file assignment dispatched", attempt=attempt + 1,
                               batch_file_count=len(batch), method="DOM.setFileInputFiles",
                               used_backend_node=bool(fresh_choice.get("backendNodeId")))
                    # Verify the exact input through its backend node handle first; this
                    # also works when an uploader is rendered in a closed shadow root.
                    actual_files = []
                    object_id = None
                    try:
                        resolved = page.call("DOM.resolveNode", {
                            "backendNodeId": fresh_choice["backendNodeId"]
                        })
                        object_id = resolved.get("object", {}).get("objectId")
                        if object_id:
                            result = page.call("Runtime.callFunctionOn", {
                                "objectId": object_id,
                                "functionDeclaration": "function(){return Array.from(this.files||[]).map(f=>({name:f.name,size:f.size,type:f.type||''}));}",
                                "returnByValue": True,
                            })
                            actual_files = result.get("result", {}).get("value", []) or []
                    except Exception:
                        actual_files = []
                    finally:
                        if object_id:
                            try:
                                page.call("Runtime.releaseObject", {"objectId": object_id})
                            except Exception:
                                pass
                    # The CDP RemoteObject normally returns an array, but some Chromium
                    # versions / custom uploader wrappers can yield a scalar (for example
                    # a numeric count). Never call len() on that scalar: re-query live DOM.
                    if not isinstance(actual_files, list):
                        self._diag(ai, "File verification returned a non-list CDP value; using DOM fallback",
                                   returned_type=type(actual_files).__name__)
                        actual_files = []
                    actual_files = [item for item in actual_files if isinstance(item, dict)]
                    # Fallback query includes every open shadow root in current DOM.
                    if not actual_files:
                        verify_script = """(() => {
                          const roots=[document],seen=new Set(),inputs=[];
                          while(roots.length){const root=roots.shift();if(!root||seen.has(root))continue;seen.add(root);
                            try{inputs.push(...root.querySelectorAll('input[type="file"]'));}catch(e){}
                            try{root.querySelectorAll('*').forEach(el=>{if(el.shadowRoot)roots.push(el.shadowRoot);});}catch(e){}
                          }
                          return inputs.flatMap(input=>[...(input.files||[])].map(file=>({name:file.name,size:file.size,type:file.type||''})));
                        })()"""
                        actual_files = page.evaluate(verify_script) or []
                    if not isinstance(actual_files, list):
                        actual_files = []
                    actual_files = [item for item in actual_files if isinstance(item, dict)]
                    expected = [{"name": Path(path).name, "size": Path(path).stat().st_size}
                                for path in batch]
                    actual_remaining = list(actual_files)
                    retained = 0
                    for item in expected:
                        match_index = next((index for index, got in enumerate(actual_remaining)
                                            if got.get("name") == item["name"] and got.get("size") == item["size"]), None)
                        if match_index is not None:
                            retained += 1
                            actual_remaining.pop(match_index)
                    self._diag(ai, "File input assignment verification", expected_count=len(expected),
                               retained_count=retained, verified=retained == len(expected))
                    if retained == len(expected):
                        assigned = True
                        break
                    last_error = CDPError(
                        f"Chrome retained {retained}/{len(expected)} selected file(s) in the upload input. "
                        "The website did not confirm the attachment preview."
                    )
                except Exception as exc:
                    last_error = exc
                    self._diag(ai, "File input assignment attempt failed", attempt=attempt + 1,
                               error_type=type(exc).__name__, error=str(exc))
                    message = str(exc).lower()
                    if "node with given id" not in message and "no node" not in message and attempt >= 1:
                        break
            if not assigned:
                detail = str(last_error or "unknown upload error")
                self._diag(ai, "Attachment could not be confirmed", error=detail)
                raise CDPError(f"Could not confirm attachment in {ai}: {detail}")

            selected.extend(batch)
            remaining = [path for path in remaining if path not in batch]
            # Let the site's native change handler consume the input and render a
            # preview before touching another file or proceeding to prompt entry.
            time.sleep(1.0)

        self._wait_for_upload_processing(page, ai)
        self._diag(ai, "Attachment workflow completed", selected_count=len(selected), total_count=len(paths))
        self.callback("site_status", {
            "ai": ai,
            "status": f"Selected {len(selected)}/{len(paths)} file(s); upload settled; sending prompt next…",
        })
        return selected

    RELAXED_RESPONSES = {
        "ChatGPT": ['[data-message-author-role="assistant"]', '[data-turn="assistant"]',
                    'article .markdown', 'div.markdown', '.markdown'],
        "Gemini": ['model-response', '.model-response-text', 'message-content', '.markdown'],
        "DeepSeek": ['.ds-markdown', '[class*="ds-markdown"]', '[class*="markdown"]'],
    }

    def _response_snapshot(self, page, ai, relaxed=False, anchor=""):
        """Return distinct, visible assistant messages with code/toolbars normalized.

        relaxed=True is a fallback used only when the precise selectors find nothing: broader
        selectors, no visibility requirement, and only user-authored turns are excluded."""
        selectors = self._js_string(self.RELAXED_RESPONSES[ai] if relaxed else self.RESPONSES[ai])
        script = r"""(() => {
          const ai = __AI__;
          const selectors = __SELECTORS__;
          const relaxed = __RELAXED__;
          const anchor = __ANCHOR__;
          const composedParent = el => el && (el.parentElement ||
            (el.getRootNode && el.getRootNode().host) || null);
          const queryDeep = selector => {
            // Fast path: the whole-DOM shadow-root walk below is very slow on ChatGPT's large DOM.
            try { const direct=[...document.querySelectorAll(selector)]; if (direct.length) return direct; } catch(e) {}
            const found=[], roots=[document], visited=new Set();
            while (roots.length) {
              const root=roots.shift();
              if (!root || visited.has(root)) continue;
              visited.add(root);
              try { found.push(...root.querySelectorAll(selector)); } catch(e) {}
              try {
                root.querySelectorAll('*').forEach(el=>{ if (el.shadowRoot) roots.push(el.shadowRoot); });
              } catch(e) {}
            }
            return [...new Set(found)];
          };
          const visible = el => {
            if (!el || !el.isConnected) return false;
            const r=el.getBoundingClientRect(), s=getComputedStyle(el);
            if (r.width<2 || r.height<2 || s.display==='none' || s.visibility==='hidden'
                || Number(s.opacity)===0 || el.getAttribute('aria-hidden')==='true') return false;
            for (let p=composedParent(el); p && p!==document.body; p=composedParent(p)) {
              const ps=getComputedStyle(p);
              if (ps.display==='none' || ps.visibility==='hidden' || p.getAttribute('aria-hidden')==='true') return false;
            }
            return true;
          };
          const attrText = el => [
            el.getAttribute('data-message-author-role'), el.getAttribute('data-testid'),
            el.getAttribute('data-role'), el.getAttribute('aria-label'),
            typeof el.className==='string' ? el.className : ''
          ].filter(Boolean).join(' ').toLowerCase();
          const userContext = el => {
            for (let p=el, depth=0; p && p!==document.body && depth<8; p=composedParent(p), depth++) {
              const role=(p.getAttribute('data-message-author-role')||'').toLowerCase();
              const meta=attrText(p);
              if (role==='assistant') return false;
              if (role==='user' || role==='human' || /user[-_ ](message|turn)|human[-_ ](message|turn)|(^|[\s_-])user([\s_-]|$)|(^|[\s_-])human([\s_-]|$)/.test(meta)) return true;
            }
            return false;
          };
          const trustedAssistant = (el, selector) => {
            if (userContext(el)) return false;
            const meta=attrText(el);
            if (ai==='ChatGPT') {
              if (el.matches('[data-turn="assistant"]') || el.closest('[data-turn="assistant"]')) return true;
              for (let p=el,depth=0;p&&p!==document.body&&depth<10;p=composedParent(p),depth++) {
                const role=(p.getAttribute('data-message-author-role')||'').toLowerCase();
                if (role==='user'||role==='human') return false;
                if (role==='assistant') return true;
              }
              return /data-message-author-role/.test(selector) && el.getAttribute('data-message-author-role')==='assistant';
            }
            if (ai==='Gemini') {
              for (let p=el,depth=0;p&&p!==document.body&&depth<12;p=p.parentElement,depth++) {
                const role=(p.getAttribute('data-message-author-role')||'').toLowerCase();
                if (role==='user'||role==='human') return false;
                if (role==='assistant'||p.matches('model-response,[data-testid*="model-response"],[data-test-id*="model-response"]')) return true;
                const parentMeta=attrText(p).replace(/[A-Z]/g,'-$&').toLowerCase();
                if (/user[-_ ](message|turn|query)|human[-_ ](message|turn)/.test(parentMeta)) return false;
                if (/model[-_ ]response|assistant[-_ ]response|generated[-_ ]image/.test(parentMeta)) return true;
              }
              return false;
            }
            if (ai==='DeepSeek') {
              for (let p=el,depth=0;p&&p!==document.body&&depth<10;p=p.parentElement,depth++) {
                const role=(p.getAttribute('data-message-author-role')||'').toLowerCase();
                if (role==='user'||role==='human') return false;
                if (role==='assistant') return true;
                const parentMeta=attrText(p);
                if (/user[-_ ](message|turn|query)/.test(parentMeta)) return false;
                if (/ds[-_ ]markdown|assistant[-_ ]message|assistant[-_ ]response|generated[-_ ]image/.test(parentMeta)) return true;
              }
              return el.matches('.ds-markdown,[class*="ds-markdown"]') || /assistant/.test(meta) && /(markdown|message|response)/.test(meta);
            }
            return false;
          };
          const skipNode = el => {
            if (!el || el.nodeType!==1) return false;
            const tag=el.tagName.toLowerCase();
            if (/^(button|input|textarea|select|option|svg|script|style|noscript)$/.test(tag)) return true;
            if (el.hidden || el.getAttribute('aria-hidden')==='true' || el.getAttribute('role')==='button') return true;
            const label=[el.getAttribute('aria-label'),el.getAttribute('title'),
                         el.getAttribute('data-testid'),el.getAttribute('data-state'),
                         typeof el.className==='string'?el.className:''].filter(Boolean).join(' ').toLowerCase();
            if (/copy|download|share|regenerate|retry|feedback|thumbs|read[- ]?aloud|message[- ]actions|response[- ]actions|code[- ](actions|toolbar)|toolbar|language[- ](label|badge)|token[- ]count|word[- ]count/.test(label)) return true;
            // Screen-reader-only headings such as "Gemini said" / "ChatGPT said:" are clipped to 1px,
            // not display:none, so they must be skipped by class/size as well.
            const cls=typeof el.className==='string'?el.className:'';
            if (/(^|[\s_-])(cdk-visually-hidden|visually-hidden|sr-only|screen-reader-only|screenreader|a11y-hidden)([\s_-]|$)/i.test(cls)) return true;
            const style=getComputedStyle(el);
            if (style.position==='absolute' && el.getBoundingClientRect().width<=2 && el.getBoundingClientRect().height<=2 && (style.overflow==='hidden' || style.clip!=='auto')) return true;
            return style.display==='none' || style.visibility==='hidden' || Number(style.opacity)===0;
          };
          const cleanText = root => {
            const codeBlocks=[];
            const blockTags=/^(address|article|blockquote|dd|div|dl|dt|fieldset|figcaption|figure|footer|h[1-6]|header|hr|li|main|ol|p|section|table|tbody|td|tfoot|th|thead|tr|ul)$/;
            const serialize = node => {
              if (node.nodeType===Node.TEXT_NODE) return node.nodeValue || '';
              if (node.nodeType!==Node.ELEMENT_NODE) return '';
              const tag=node.tagName.toLowerCase();
              if (skipNode(node)) return '';
              if (node.classList && node.classList.contains('cm-editor') && !node.closest('pre')) {
                const cmText=[...node.querySelectorAll('.cm-line')].map(l=>l.textContent||'').join('\n').replace(/\n+$/,'');
                const cmToken='\u0000AI_BRIDGE_CODE_'+codeBlocks.length+'\u0000';
                codeBlocks.push('```\n'+cmText+'\n```');
                return '\n'+cmToken+'\n';
              }
              if (tag==='pre') {
                const code=node.querySelector('code') || node;
                const cmLines=node.querySelectorAll('.cm-line');
                const body=(cmLines.length ? [...cmLines].map(l=>l.textContent||'').join('\n') : (code.textContent || '')).replace(/\r\n?/g,'\n').replace(/\n+$/,'');
                const cls=(code.className||'')+' '+(node.className||'');
                const match=cls.match(/(?:language-|lang-)([a-z0-9_+#.-]+)/i);
                const lang=match ? match[1] : '';
                const token='\u0000AI_BRIDGE_CODE_'+codeBlocks.length+'\u0000';
                codeBlocks.push('```'+lang+'\n'+body+'\n```');
                return '\n'+token+'\n';
              }
              if (tag==='br') return '\n';
              if (tag==='img') return node.getAttribute('alt') ? '['+node.getAttribute('alt')+']' : '';
              if (tag==='tr') return [...node.children].map(serialize).join(' | ')+'\n';
              if (tag==='li') return '\n- '+[...node.childNodes].map(serialize).join('').trim();
              const sourceChildren=(node.shadowRoot && node.shadowRoot.childNodes.length)
                ? [...node.shadowRoot.childNodes] : [...node.childNodes];
              const children=sourceChildren.map(serialize).join('');
              if (blockTags.test(tag)) return '\n'+children+'\n';
              return children;
            };
            let text=serialize(root).replace(/\r\n?/g,'\n');
            text=text.split('\n').map(line=>line.replace(/[\t ]+$/,'')).join('\n');
            text=text.replace(/\n{3,}/g,'\n\n').trim();
            // Safety net: drop a leading screen-reader label if it still slipped through.
            text=text.replace(/^(?:gemini|chatgpt|deepseek)\s+said\s*:?\s*\n+/i,'');
            codeBlocks.forEach((block,index)=>{ text=text.replace('\u0000AI_BRIDGE_CODE_'+index+'\u0000',block); });
            return text;
          };
          // Markup-independent extraction: find OUR sent prompt in the page by its text, then read what
          // follows it. Used when a site's DOM no longer matches any known assistant selector.
          const anchorCollect = () => {
            const norm = t => String(t||'').replace(/\s+/g,' ').trim();
            const docs=[document];
            document.querySelectorAll('iframe').forEach(f=>{ try { if (f.contentDocument) docs.push(f.contentDocument); } catch(e) {} });
            for (const doc of docs) {
              const root=doc.querySelector('main') || doc.body;
              if (!root) continue;
              const tw=doc.createTreeWalker(root, NodeFilter.SHOW_TEXT);
              let hit=null, node;
              while ((node=tw.nextNode())) {
                const v=node.nodeValue;
                if (!v || v.length<anchor.length) continue;
                if (!norm(v).includes(anchor)) continue;
                const pe=node.parentElement;
                if (!pe || pe.closest('#prompt-textarea, form, [data-testid*="composer" i], [contenteditable="true"], script, style')) continue;
                hit=node;   // keep the LAST match = the newest sent prompt
              }
              if (!hit) continue;
              let turn=hit.parentElement;
              for (let depth=0; turn && depth<14; depth++) {
                const parent=turn.parentElement;
                if (!parent || parent===doc.documentElement) break;
                if (parent.querySelector('#prompt-textarea, form, [data-testid*="composer" i]')) return [];
                const texts=[];
                for (let sib=turn.nextElementSibling; sib; sib=sib.nextElementSibling) {
                  const t=cleanText(sib);
                  if (t && t.length>=1) texts.push(t);
                }
                if (texts.length) return [texts.join('\n\n')];
                turn=parent;
              }
            }
            return [];
          };
          let collected=[];
          for (const selector of selectors) {
            let nodes=[];
            try { nodes=queryDeep(selector); } catch(e) { continue; }
            for (const el of nodes) {
              if (relaxed ? (!el.isConnected || userContext(el)) : (!visible(el) || !trustedAssistant(el,selector))) continue;
              // Never read from a candidate that contains the editor or a dialog.
              // Only reject candidates that contain the real chat composer. Code blocks (CodeMirror)
              // are contenteditable too and must NOT disqualify an answer that contains code.
              // ChatGPT: the only real composer is #prompt-textarea / a <form>; answers never contain one.
              const hasComposer = ai==='ChatGPT'
                ? !!el.querySelector('#prompt-textarea, form, [data-testid*="composer" i]')
                : [...el.querySelectorAll('[contenteditable="true"],textarea,input')]
                    .some(n=>!n.closest('pre,code,.cm-editor,[class*="code-block"],[class*="codeblock"]'));
              if (hasComposer || el.querySelector('[role="dialog"]')) continue;
              const text=cleanText(el);
              if (text.length<2) continue;
              collected.push({el,text,selector});
            }
            if (collected.length) break; // selector precedence prevents broad duplicates
          }
          if (!collected.length) return anchor ? anchorCollect() : [];
          // Collapse nested wrappers that expose the same answer twice. Keep the
          // innermost candidate, which normally contains the actual assistant text.
          const keep=collected.filter((item,i,all)=>!all.some((other,j)=>j!==i &&
            item.el!==other.el && item.el.contains(other.el)));
          keep.sort((a,b)=>{
            const pos=a.el.compareDocumentPosition(b.el);
            return pos & Node.DOCUMENT_POSITION_FOLLOWING ? -1 :
                   pos & Node.DOCUMENT_POSITION_PRECEDING ? 1 : 0;
          });
          const seen=new Set(), output=[];
          for (const item of keep) {
            const normalized=item.text.replace(/\r\n?/g,'\n').trim();
            if (seen.has(normalized)) continue;
            seen.add(normalized);
            output.push(item.text);
          }
          return output;
        })()""".replace('__AI__', self._js_string(ai)).replace('__SELECTORS__', selectors).replace('__RELAXED__', 'true' if relaxed else 'false').replace('__ANCHOR__', self._js_string(anchor or ''))
        value = page.evaluate(script)
        return value if isinstance(value, list) else []

    def _response_media_snapshot(self, page, ai):
        """Find image assets in assistant turns (never user-uploaded prompt attachments)."""
        selectors = self._js_string(self.RESPONSES[ai])
        script = r"""(() => {
          const ai=__AI__, selectors=__SELECTORS__;
          const queryDeep=selector=>{
            const found=[], roots=[document], seen=new Set();
            while(roots.length){const root=roots.shift();if(!root||seen.has(root))continue;seen.add(root);
              try{found.push(...root.querySelectorAll(selector));}catch(e){}
              try{root.querySelectorAll('*').forEach(el=>{if(el.shadowRoot)roots.push(el.shadowRoot);});}catch(e){}
            } return [...new Set(found)];
          };
          const visible=el=>{const r=el.getBoundingClientRect(),s=getComputedStyle(el);
            return el.isConnected&&r.width>=80&&r.height>=60&&s.display!=='none'&&s.visibility!=='hidden'&&Number(s.opacity)!==0;};
          const meta=el=>[el.getAttribute('data-message-author-role'),el.getAttribute('data-testid'),
            el.getAttribute('aria-label'),typeof el.className==='string'?el.className:''].filter(Boolean).join(' ').toLowerCase();
          const assistant=(el,selector)=>{
            for(let p=el,depth=0;p&&p!==document.body&&depth<9;p=p.parentElement,depth++){
              const role=(p.getAttribute('data-message-author-role')||'').toLowerCase();
              if(role==='user'||role==='human')return false;
              if(role==='assistant')return true;
              const m=meta(p);
              if(/user[-_ ](message|turn)|human[-_ ](message|turn)/.test(m))return false;
              if(ai==='Gemini'&&(p.matches('model-response,[data-testid*="model-response"],[data-test-id*="model-response"]')||/model[-_ ]response|assistant[-_ ]response|generated[-_ ]image/.test(m)))return true;
              if(ai==='DeepSeek'&&(p.matches('.ds-markdown,[class*="ds-markdown"]')||/ds[-_ ]markdown|assistant[-_ ]message|assistant[-_ ]response|generated[-_ ]image/.test(m)))return true;
            }
            return ai==='ChatGPT'&&/data-message-author-role/.test(selector);
          };
          const out=[],seen=new Set();
          const add=(src,alt,w,h,kind)=>{
            if(!src||seen.has(src)||w<80||h<60)return;
            if(/avatar|profile|logo|icon|spinner|copy|download/i.test(alt||''))return;
            seen.add(src);out.push({src,alt:alt||'',width:w,height:h,kind:kind||'image'});
          };
          for(const selector of selectors){
            for(const box of queryDeep(selector)){
              if(!assistant(box,selector))continue;
              const descendants=[box],rootsSeen=new Set(),elements=[];
              while(descendants.length){
                const root=descendants.shift();if(!root||rootsSeen.has(root))continue;rootsSeen.add(root);
                try{elements.push(...root.querySelectorAll('*'));}catch(e){}
                try{root.querySelectorAll('*').forEach(el=>{if(el.shadowRoot)descendants.push(el.shadowRoot);});}catch(e){}
              }
              const all=[box,...elements];
              for(const img of all.filter(el=>el.tagName==='IMG')){
                if(!visible(img))continue;
                const r=img.getBoundingClientRect();
                add(img.currentSrc||img.src||img.getAttribute('src'),img.alt||'Generated image',
                    img.naturalWidth||r.width||img.width||0,img.naturalHeight||r.height||img.height||0,'image');
              }
              for(const canvas of all.filter(el=>el.tagName==='CANVAS')){
                if(!visible(canvas))continue;
                try{add(canvas.toDataURL('image/png'),canvas.getAttribute('aria-label')||'Generated image',
                        canvas.width,canvas.height,'canvas');}catch(e){}
              }
              for(const el of all){
                if(!visible(el))continue;
                const bg=getComputedStyle(el).backgroundImage||'';
                const match=bg.match(/url\(["']?(.*?)["']?\)/i);
                if(match){const r=el.getBoundingClientRect();add(match[1],el.getAttribute('aria-label')||'Generated image',r.width,r.height,'background');}
                if(el.tagName==='VIDEO'&&el.poster){const r=el.getBoundingClientRect();add(el.poster,'Generated video preview',r.width,r.height,'poster');}
              }
              if(out.length>=16)return out;
            }
          }
          return out;
        })()""".replace('__AI__', self._js_string(ai)).replace('__SELECTORS__', selectors)
        value = page.evaluate(script, timeout=25)
        return value if isinstance(value, list) else []

    def _download_response_media(self, page, ai, candidates):
        """Download newly generated image data through the signed-in page context."""
        if not candidates:
            return []
        script = r"""(async () => {
          const items=__ITEMS__;
          const result=[];
          for(const item of items){
            try{
              if(item.src.startsWith('data:')){result.push({...item,dataUrl:item.src});continue;}
              const response=await fetch(item.src,{credentials:'include'});
              if(!response.ok)throw new Error('HTTP '+response.status);
              const blob=await response.blob();
              if(blob.size>15*1024*1024)throw new Error('Image exceeds 15 MB export limit');
              const dataUrl=await new Promise((resolve,reject)=>{
                const reader=new FileReader();reader.onload=()=>resolve(reader.result);reader.onerror=()=>reject(reader.error);reader.readAsDataURL(blob);
              });
              result.push({...item,dataUrl,mime:blob.type||''});
            }catch(error){result.push({...item,downloadError:String(error)});}
          }
          return result;
        })()""".replace('__ITEMS__', self._js_string(candidates))
        try:
            values=page.evaluate(script, timeout=45)
        except Exception as exc:
            self.callback("site_status", {"ai":ai,"status":f"Reply captured; image export unavailable: {exc}"})
            return [{**item,"downloadError":str(exc)} for item in candidates]
        saved=[]
        for index,item in enumerate(values if isinstance(values,list) else [] ,1):
            data_url=item.get('dataUrl','')
            if not data_url.startswith('data:'):
                saved.append({"name":item.get("alt") or f"Image {index}","source":item.get("src",""),"error":item.get("downloadError","Image could not be downloaded by this site")})
                continue
            try:
                header,encoded=data_url.split(',',1)
                mime=header[5:].split(';',1)[0].lower()
                ext=mimetypes.guess_extension(mime) or ".png"
                if ext=='.jpe': ext='.jpg'
                raw=base64.b64decode(encoded,validate=False)
                if not raw or len(raw)>15*1024*1024:
                    raise ValueError("Empty or oversized image")
                folder=self.result_dir / re.sub(r'[^A-Za-z0-9_-]+','_',ai)
                folder.mkdir(parents=True,exist_ok=True)
                filename=f"{ai.lower()}_image_{index:02d}_{datetime.now().strftime('%H%M%S')}{ext}"
                destination=folder/filename
                destination.write_bytes(raw)
                saved.append({"name":filename,"path":str(destination),"source":item.get("src",""),"alt":item.get("alt","")})
            except Exception as exc:
                saved.append({"name":item.get("alt") or f"Image {index}","source":item.get("src",""),"error":str(exc)})
        return saved

    @staticmethod
    def _make_anchor(prompt):
        """A short single-line snippet of the sent prompt, used to find OUR message in the page even
        when a site's markup changes. Whitespace-normalised; never logged."""
        lines = [re.sub(r"\s+", " ", ln).strip() for ln in str(prompt).splitlines()]
        lines = [ln for ln in lines if len(ln) >= 8]
        if not lines:
            return ""
        best = max(lines[-8:], key=len)
        return best[-50:]

    def _focus_composer(self, page, ai, selector, attempts=4):
        """Focus the composer with re-detection + a real click; returns (focused, selector_literal)."""
        for attempt in range(1, attempts + 1):
            focus_js = (
                "(() => { let el=document.querySelector(" + selector + "); "
                "if(!el||!el.isConnected)return {ok:false,why:'missing'}; "
                "el.focus({preventScroll:true}); "
                "try{ if(el.tagName==='TEXTAREA'||el.tagName==='INPUT'){const n=(el.value||'').length;el.setSelectionRange(n,n);} "
                "else {const sel=getSelection(),r=document.createRange(); r.selectNodeContents(el); r.collapse(false); sel.removeAllRanges(); sel.addRange(r);} }catch(e){} "
                "const a=document.activeElement; return {ok:(a===el||el.contains(a)),why:'active='+(a?a.tagName:'none')}; })()"
            )
            why = "error"
            try:
                state = page.evaluate(focus_js) or {}
                if state.get("ok"):
                    return True, selector
                why = state.get("why", "not active")
            except CDPError as exc:
                why = str(exc)[:80]
            self._diag(ai, "Composer focus attempt failed; re-detecting", attempt=attempt, reason=why)
            time.sleep(0.4)
            try:
                fresh = self._detect_composer(page, ai)
            except CDPError:
                continue
            selector = self._js_string(fresh["selector"])
            if fresh.get("x") is not None and fresh.get("y") is not None:
                for kind in ("mouseMoved", "mousePressed", "mouseReleased"):
                    try:
                        page.call("Input.dispatchMouseEvent", {
                            "type": kind, "x": fresh["x"], "y": fresh["y"],
                            "button": "none" if kind == "mouseMoved" else "left", "clickCount": 1,
                        })
                    except CDPError:
                        pass
                time.sleep(0.2)
        return False, selector

    def _fill_and_send(self, page, ai, prompt, fallback_prompt=None, attachments=None):
        """Attach selected non-code files, then always enter and attempt the actual prompt."""
        effective_prompt = fallback_prompt or prompt
        _t_fill = time.monotonic()
        if not effective_prompt.strip():
            raise CDPError("The prompt is empty. Enter a task before starting.")
        attachment_warning = None
        attached_names = []
        self._diag(ai, "Prompt preparation started", prompt_characters=len(effective_prompt),
                   attachment_count=len(attachments or []))
        if self._cancel_event.is_set():
            raise CDPError("Stopped by user before prompt preparation.")
        if attachments:
            try:
                attached = self._attach_non_code_files(page, ai, attachments)
                attached_names = [Path(p).name for p in attached]
                self._diag(ai, "Attachment processing finished", requested=len(attachments), confirmed=len(attached))
                effective_prompt += "\n\nReference files selected in the chat upload control: " + ", ".join(attached_names)
            except Exception as exc:
                attachment_warning = str(exc)
                self._diag(ai, "Attachment processing failed; prompt will continue", error_type=type(exc).__name__, error=str(exc))
                not_confirmed = ", ".join(Path(p).name for p in attachments)
                effective_prompt += (
                    "\n\nAttachment note: AI Bridge could not confirm these reference files: "
                    f"{not_confirmed}. Do not assume their contents are available. "
                    "Please ask me for any missing information."
                )
                self.callback("site_status", {
                    "ai": ai,
                    "status": f"Attachment issue; still sending prompt: {attachment_warning}",
                })

        # Resolve the editor AFTER file selection, because upload previews can rerender it.
        detected = self._detect_composer(page, ai)
        selector = self._js_string(detected["selector"])
        self._diag(ai, "Composer ready for prompt", tag=detected.get("tag"), element_id=detected.get("id"),
                   contenteditable=detected.get("contenteditable"), aria=detected.get("aria"))
        self._baseline[ai] = self._response_snapshot(page, ai)
        self._prompt_anchor[ai] = self._make_anchor(effective_prompt)
        self._diag(ai, "Response baseline captured", assistant_message_count=len(self._baseline[ai]),
                   anchor_available=bool(self._prompt_anchor[ai]))
        self._baseline_media[ai] = {
            item.get("src", "") for item in self._response_media_snapshot(page, ai)
            if item.get("src")
        }
        # A DOM focus() call alone does not reliably place the caret inside ChatGPT's
        # ProseMirror editor. Use an actual CDP pointer click, then set the caret at end.
        if detected.get("x") is not None and detected.get("y") is not None:
            page.call("Input.dispatchMouseEvent", {
                "type": "mouseMoved", "x": detected["x"], "y": detected["y"], "button": "none",
            })
            page.call("Input.dispatchMouseEvent", {
                "type": "mousePressed", "x": detected["x"], "y": detected["y"],
                "button": "left", "clickCount": 1,
            })
            page.call("Input.dispatchMouseEvent", {
                "type": "mouseReleased", "x": detected["x"], "y": detected["y"],
                "button": "left", "clickCount": 1,
            })
        focus_script = f"""(() => {{
          let el=document.querySelector({selector});
          if(el&&el.matches('p[data-placeholder]'))el=el.closest('[contenteditable="true"]')||el.parentElement;
          if(!el)return {{ok:false,text:''}};
          el.focus({{preventScroll:true}});
          const isField=el.tagName==='TEXTAREA'||el.tagName==='INPUT';
          const text=isField?el.value:(el.innerText||el.textContent||'');
          try {{
            if(isField) el.setSelectionRange(text.length,text.length);
            else {{
              const selection=window.getSelection(); const range=document.createRange();
              range.selectNodeContents(el); range.collapse(false);
              selection.removeAllRanges(); selection.addRange(range);
            }}
          }} catch(e) {{}}
          return {{ok:true,text,active:document.activeElement===el,isContentEditable:!!el.isContentEditable}};
        }})()"""
        editor = page.evaluate(focus_script)
        if not editor or not editor.get("ok"):
            # The page may have rerendered after a navigation/attachment. Reacquire once
            # and rebuild the selector-bound script against the fresh editor path.
            old_selector_literal = selector
            detected = self._detect_composer(page, ai)
            selector = self._js_string(detected["selector"])
            focus_script = focus_script.replace(old_selector_literal, selector)
            editor = page.evaluate(focus_script)
        if not editor or not editor.get("ok"):
            self._diag(ai, "Composer disappeared before typing")
            raise CDPError("The chat editor disappeared before prompt entry. Reopen the chat tab and retry.")
        self._diag(ai, "Composer focused", active=editor.get("active"), is_contenteditable=editor.get("isContentEditable"),
                   existing_draft_characters=len(editor.get("text") or ""))
        # Preserve any existing user draft. If it is already this exact prompt (for
        # example, from a prior manual-send fallback), reuse it instead of duplicating it.
        existing_text = (editor.get("text") or "").replace("\r\n", "\n").strip()
        normalized_prompt = effective_prompt.replace("\r\n", "\n").strip()
        already_entered = False
        if existing_text:
            first_check = normalized_prompt[:min(100, len(normalized_prompt))]
            last_check = normalized_prompt[-min(100, len(normalized_prompt)):]
            # Newline wrapper differences are harmless, but all nonblank characters
            # (including spaces, indentation, punctuation and code) must match exactly.
            existing_flat = "".join(line for line in existing_text.splitlines() if line.strip())
            expected_flat = "".join(line for line in normalized_prompt.splitlines() if line.strip())
            already_entered = bool(expected_flat) and existing_flat == expected_flat
            if not already_entered:
                # A previous failed run can leave its unsent prompt in the composer.
                # Back it up locally before replacing it with this explicitly requested
                # AI Bridge prompt, so no existing draft is silently destroyed.
                backup_dir = self.result_dir / "Unsent Draft Backups"
                backup_dir.mkdir(parents=True, exist_ok=True)
                backup_path = backup_dir / (
                    f"{ai.lower()}_draft_{datetime.now().strftime('%Y%m%d_%H%M%S_%f')}.txt"
                )
                try:
                    backup_path.write_text(existing_text, encoding="utf-8")
                except OSError as exc:
                    raise CDPError(
                        f"The {ai} composer contains an older draft and its backup could not be saved: {exc}. "
                        "The draft was left untouched; clear it manually and retry."
                    ) from None
                clear_script = f"""(() => {{
                  const el=document.querySelector({selector});
                  if(!el||!el.isConnected)return {{ok:false,reason:'Composer was replaced'}};
                  el.focus({{preventScroll:true}});
                  if(el.tagName==='TEXTAREA'||el.tagName==='INPUT') {{
                    const proto=el.tagName==='TEXTAREA'?HTMLTextAreaElement.prototype:HTMLInputElement.prototype;
                    const setter=Object.getOwnPropertyDescriptor(proto,'value')?.set;
                    if(setter)setter.call(el,''); else el.value='';
                    el.dispatchEvent(new InputEvent('input',{{bubbles:true,inputType:'deleteContentBackward'}}));
                    el.dispatchEvent(new Event('change',{{bubbles:true}}));
                  }} else {{
                    const selection=window.getSelection();
                    const range=document.createRange();
                    range.selectNodeContents(el);
                    selection.removeAllRanges();
                    selection.addRange(range);
                    document.execCommand('delete',false,null);
                    el.dispatchEvent(new InputEvent('input',{{bubbles:true,inputType:'deleteContentBackward'}}));
                  }}
                  const remaining=(el.tagName==='TEXTAREA'||el.tagName==='INPUT')?el.value:(el.innerText||el.textContent||'');
                  return {{ok:!String(remaining).trim(),remainingLength:String(remaining).length}};
                }})()"""
                cleared = page.evaluate(clear_script, timeout=12)
                if not cleared or not cleared.get("ok"):
                    raise CDPError(
                        f"The older {ai} draft was backed up to {backup_path.name}, but the composer could not be cleared. "
                        "Clear the composer manually and retry."
                    )
                self._diag(ai, "Previous unsent draft backed up and composer cleared",
                           previous_draft_characters=len(existing_text), backup_file=backup_path.name)
                self.callback("site_status", {
                    "ai": ai,
                    "status": f"An older unsent draft was backed up locally as {backup_path.name}; entering the new prompt…",
                })
                time.sleep(0.15)

        # Rich-text composers (ChatGPT ProseMirror and Gemini Quill) must receive
        # one atomic insertion. Re-focusing/repositioning the caret between chunks can
        # race framework rerenders and duplicate/drop text. DeepSeek's native textarea
        # remains chunked because its input state is reliable and large inserts are slower.
        if not already_entered:
            if self._cancel_event.is_set():
                raise CDPError("Stopped by user before text entry.")
            chunk_size = len(effective_prompt) if ai in ("ChatGPT", "Gemini") else 4000
            chunk_count = 1 if ai in ("ChatGPT", "Gemini") else (len(effective_prompt) + chunk_size - 1) // chunk_size
            self._diag(ai, "Prompt insertion started", method="CDP Input.insertText",
                       chunk_size=chunk_size, chunk_count=chunk_count,
                       expected_characters=len(effective_prompt), atomic_insert=ai in ("ChatGPT", "Gemini"))
            if ai in ("ChatGPT", "Gemini"):
                # Reconfirm the composer and caret immediately before the single insertion.
                # Rich editors (ChatGPT ProseMirror) can swap their DOM node after the draft is
                # cleared, so the old selector may be stale: re-detect, click, and refocus with retries.
                focused, selector = self._focus_composer(page, ai, selector)
                if not focused:
                    raise CDPError(f"{ai} composer lost focus before prompt insertion; nothing was sent.")
                try:
                    page.call("Input.insertText", {"text": effective_prompt}, timeout=60)
                except Exception as exc:
                    self._diag(ai, "Atomic prompt insertion failed", error_type=type(exc).__name__, error=str(exc))
                    raise
            else:
                for offset in range(0, len(effective_prompt), chunk_size):
                    if self._cancel_event.is_set():
                        raise CDPError("Stopped by user during text entry.")
                    page.evaluate(f"(() => {{ const el=document.querySelector({selector}); if(!el||!el.isConnected)return false; el.focus({{preventScroll:true}}); const n=(el.value||'').length; try{{el.setSelectionRange(n,n);}}catch(e){{}} return document.activeElement===el; }})()")
                    chunk = effective_prompt[offset:offset + chunk_size]
                    try:
                        page.call("Input.insertText", {"text": chunk}, timeout=45)
                    except Exception as exc:
                        self._diag(ai, "Prompt insertion chunk failed", chunk_index=offset // chunk_size + 1,
                                   chunk_characters=len(chunk), error_type=type(exc).__name__, error=str(exc))
                        raise
                    if len(effective_prompt) > chunk_size:
                        time.sleep(0.08)
            self._diag(ai, "Prompt insertion commands completed", chunk_count=chunk_count)
        else:
            self._diag(ai, "Existing editor draft matched prepared prompt; reusing draft", prompt_characters=len(effective_prompt))

        expected_prompt_for_verify = str(effective_prompt)
        verify_entry = f"""(() => {{
          const el=document.querySelector({selector});
          const expected={self._js_string(expected_prompt_for_verify)};
          if(!el||!el.isConnected) return {{ok:false,missing:true,length:0,expected:expected.length,source:'missing'}};
          const clean=s=>String(s||'').normalize('NFC').replace(/[\\u200B-\\u200D\\uFEFF]/g,'')
            .replace(/\\u00a0/g,' ').replace(/\\r\\n?/g,'\\n').trim();
          const wanted=clean(expected);
          const wantedParts=wanted.split('\\n').filter(line=>line.trim().length>0);
          const wantedFlat=wantedParts.join('');
          const candidates=[];
          const add=(source,value)=>{{
            const normalized=clean(value);
            const parts=normalized.split('\\n').filter(line=>line.trim().length>0);
            const flat=parts.join('');
            const exact=normalized===wanted;
            // Ignore empty editor paragraphs, but require every nonblank line to
            // match in order. This preserves Python/code line boundaries and indentation.
            const sameLines=parts.length===wantedParts.length && parts.every((line,index)=>line===wantedParts[index]);
            // Rich editors may trim trailing spaces or re-wrap whitespace; accept those as a loose (logged) match.
            const trimEnd=l=>l.replace(/[ \\t]+$/,'');
            const sameLinesLoose=parts.length===wantedParts.length && parts.every((line,index)=>trimEnd(line)===trimEnd(wantedParts[index]));
            const noWs=flat.replace(/\\s+/g,'')===wantedFlat.replace(/\\s+/g,'');
            let prefix=0; while(prefix<flat.length&&prefix<wantedFlat.length&&flat[prefix]===wantedFlat[prefix])prefix++;
            let suffix=0; while(suffix<flat.length-prefix&&suffix<wantedFlat.length-prefix&&flat[flat.length-1-suffix]===wantedFlat[wantedFlat.length-1-suffix])suffix++;
            candidates.push({{source,normalized,parts,flat,exact,sameLines,sameLinesLoose,noWs,prefix,suffix}});
          }};
          if(el.tagName==='TEXTAREA'||el.tagName==='INPUT') add('value',el.value);
          else {{
            add('innerText',typeof el.innerText==='string'?el.innerText:'');
            add('textContent',typeof el.textContent==='string'?el.textContent:'');
            const blocks=[...el.children].filter(child=>/^(P|DIV|LI)$/.test(child.tagName));
            if(blocks.length) add('block-children',blocks.map(child=>child.innerText||child.textContent||'').join('\\n'));
          }}
          candidates.sort((a,b)=>Number(b.exact||b.sameLines||b.sameLinesLoose||b.noWs)-Number(a.exact||a.sameLines||a.sameLinesLoose||a.noWs)
            ||Math.abs(a.flat.length-wantedFlat.length)-Math.abs(b.flat.length-wantedFlat.length)
            ||(b.prefix+b.suffix)-(a.prefix+a.suffix));
          const best=candidates[0]||{{source:'none',normalized:'',parts:[],flat:'',exact:false,sameLines:false,prefix:0,suffix:0}};
          return {{ok:!!(best.exact||best.sameLines||best.sameLinesLoose||best.noWs),looseMatch:!!(!best.exact&&!best.sameLines&&(best.sameLinesLoose||best.noWs)),length:best.normalized.length,expected:wanted.length,
            nonBlankLength:best.parts.join('\\n').length,nonBlankExpected:wantedParts.join('\\n').length,
            actualNonblankLineCount:best.parts.length,expectedNonblankLineCount:wantedParts.length,
            nonNewlineCharactersMatch:best.sameLines,nonBlankLinesMatch:best.sameLines,source:best.source,
            flatActualCharacters:best.flat.length,flatExpectedCharacters:wantedFlat.length,
            prefixMatchCharacters:best.prefix,suffixMatchCharacters:best.suffix}};
        }})()"""

        def read_entry_state():
            """Read one editor snapshot; tolerate a transient CDP undefined result."""
            nonlocal verify_entry, selector
            try:
                state = page.evaluate(verify_entry, timeout=20)
                if isinstance(state, dict) and state.get("missing"):
                    # The site re-rendered the editor: find the live one and read it again.
                    fresh_editor = self._detect_composer(page, ai)
                    new_selector = self._js_string(fresh_editor["selector"])
                    if new_selector != selector:
                        verify_entry = verify_entry.replace(selector, new_selector)
                        selector = new_selector
                        self._diag(ai, "Composer element was replaced by the page; selector refreshed")
                    state = page.evaluate(verify_entry, timeout=20)
            except Exception as exc:
                self._diag(ai, "Prompt verification probe failed", error_type=type(exc).__name__, error=str(exc))
                return None
            if isinstance(state, str):
                try:
                    state = json.loads(state)
                except (TypeError, json.JSONDecodeError):
                    return None
            return state if isinstance(state, dict) else None

        def wait_for_entry_state(timeout=4.0):
            deadline = time.monotonic() + timeout
            last = None
            last_signature = None
            stable_successes = 0
            while time.monotonic() < deadline:
                state = read_entry_state()
                if state is not None:
                    last = state
                    signature = (state.get('ok'), state.get('length'), state.get('flatActualCharacters'),
                                 state.get('prefixMatchCharacters'), state.get('suffixMatchCharacters'), state.get('source'))
                    if state.get('ok'):
                        stable_successes = stable_successes + 1 if signature == last_signature else 1
                        if stable_successes >= 2:
                            return state
                    else:
                        stable_successes = 0
                    last_signature = signature
                time.sleep(0.1)
            return last

        entry_state = wait_for_entry_state(timeout=20.0 if ai in ("ChatGPT", "Gemini") else 8.0)
        self._diag(ai, "Prompt editor verification", verified=bool(entry_state and entry_state.get("ok")),
                   loose_match=bool((entry_state or {}).get("looseMatch")),
                   actual_characters=(entry_state or {}).get("length", 0),
                   expected_characters=(entry_state or {}).get("expected", len(effective_prompt)),
                   actual_nonblank_characters=(entry_state or {}).get("nonBlankLength", 0),
                   expected_nonblank_characters=(entry_state or {}).get("nonBlankExpected", 0),
                   nonblank_lines_match=(entry_state or {}).get("nonBlankLinesMatch", False),
                   actual_nonblank_line_count=(entry_state or {}).get("actualNonblankLineCount", 0),
                   expected_nonblank_line_count=(entry_state or {}).get("expectedNonblankLineCount", 0),
                   chosen_text_source=(entry_state or {}).get("source", "no-state"),
                   matched_prefix_characters=(entry_state or {}).get("prefixMatchCharacters", 0),
                   matched_suffix_characters=(entry_state or {}).get("suffixMatchCharacters", 0))

        # One controlled rich-editor recovery: clear it, verify it is truly empty, and
        # reinsert the complete prompt once. Never retype into a composer unless the
        # clear was independently confirmed, which prevents appended duplicate tails.
        if (not entry_state or not entry_state.get("ok")) and ai in ("ChatGPT", "Gemini") and not self._cancel_event.is_set():
            fresh = self._detect_composer(page, ai)
            old_selector_literal = selector
            selector = self._js_string(fresh["selector"])
            verify_entry = verify_entry.replace(old_selector_literal, selector)
            clear_script = f"""(() => {{
              const el=document.querySelector({selector});
              if(!el||!el.isConnected)return {{ok:false,reason:'composer-missing'}};
              el.focus({{preventScroll:true}});
              if(el.tagName==='TEXTAREA'||el.tagName==='INPUT'){{
                const proto=el.tagName==='TEXTAREA'?HTMLTextAreaElement.prototype:HTMLInputElement.prototype;
                const setter=Object.getOwnPropertyDescriptor(proto,'value')?.set;
                if(setter)setter.call(el,'');else el.value='';
                el.dispatchEvent(new InputEvent('input',{{bubbles:true,inputType:'deleteContentBackward'}}));
                el.dispatchEvent(new Event('change',{{bubbles:true}}));
              }}else{{
                const sel=window.getSelection(),range=document.createRange();
                range.selectNodeContents(el);sel.removeAllRanges();sel.addRange(range);
                document.execCommand('delete',false,null);
                el.dispatchEvent(new InputEvent('input',{{bubbles:true,inputType:'deleteContentBackward'}}));
              }}
              const text=(el.tagName==='TEXTAREA'||el.tagName==='INPUT')?el.value:(el.innerText||el.textContent||'');
              return {{ok:!String(text).trim(),remainingCharacters:String(text).length}};
            }})()"""
            cleared = page.evaluate(clear_script, timeout=15)
            cleared_ok = isinstance(cleared, dict) and bool(cleared.get("ok"))
            self._diag(ai, "Rich composer recovery clear", cleared=cleared_ok,
                       remaining_characters=cleared.get("remainingCharacters", -1) if isinstance(cleared, dict) else -1)
            if cleared_ok:
                previous_selector = selector
                focus_end, selector = self._focus_composer(page, ai, selector)
                if selector != previous_selector:
                    verify_entry = verify_entry.replace(previous_selector, selector)
                if not focus_end:
                    raise CDPError(f"{ai} composer could not be focused for its one clean retry; prompt was not sent.")
                page.call("Input.insertText", {"text": effective_prompt}, timeout=60)
                self._diag(ai, "Rich composer recovery prompt reinserted atomically", characters=len(effective_prompt))
                entry_state = wait_for_entry_state(timeout=20.0)
                self._diag(ai, "Prompt editor verification after clean retry", verified=bool(entry_state and entry_state.get("ok")),
                           actual_characters=(entry_state or {}).get("length", 0),
                           expected_characters=(entry_state or {}).get("expected", len(effective_prompt)),
                           chosen_text_source=(entry_state or {}).get("source", "no-state"))
            else:
                raise CDPError(
                    f"{ai} editor content did not match the prompt and the editor could not be confirmed empty. "
                    "AI Bridge did not retry typing, to avoid duplicating or corrupting the draft. Clear the composer and retry."
                )

        if not entry_state or not entry_state.get("ok"):
            state = entry_state or {}
            self._diag(ai, "Prompt verification failed; prompt not sent",
                       actual_characters=state.get("length", 0), expected_characters=state.get("expected", len(effective_prompt)),
                       chosen_text_source=state.get("source", "no-state"),
                       prefix_match_characters=state.get("prefixMatchCharacters", 0),
                       suffix_match_characters=state.get("suffixMatchCharacters", 0))
            raise CDPError(
                f"The complete prompt could not be verified in the {ai} editor "
                f"({state.get('length',0)}/{state.get('expected',len(effective_prompt))} visible characters; "
                f"nonblank-line match: {bool(state.get('nonBlankLinesMatch', state.get('nonNewlineCharactersMatch', False)))}). "
                "The prompt was not sent. Check the browser composer before retrying."
            )
        self._prepared.add(ai)
        self._diag(ai, "Prompt fully verified in editor", prompt_characters=len(effective_prompt),
                   elapsed_ms_since_fill_start=int((time.monotonic() - _t_fill) * 1000))

        # Identify the actual Send button using explicit accessible labels / test IDs first.
        # Only use a nearby icon-only button when it is the sole plausible button by the composer.
        probe_source = " ".join(effective_prompt.split())
        probe = probe_source[:80]
        user_selectors = {
            "ChatGPT": ['[data-message-author-role="user"]', '[data-testid^="conversation-turn"] [data-message-author-role="user"]'],
            "Gemini": ['[data-message-author-role="user"]', 'user-query', '.user-query-container', '[data-testid*="user-query"]'],
            "DeepSeek": ['[data-message-author-role="user"]', '.ds-user-message', '[class*="user-message"]'],
        }[ai]

        def try_enter_send(expected_user_count=None, expected_busy=False):
            """Send Enter only while the verified prompt is still in the composer."""
            preflight_script = f"""(() => {{
              const el=document.querySelector({selector});
              if(!el||!el.isConnected)return {{ok:false,reason:'Composer is no longer present'}};
              const norm=v=>String(v||'').normalize('NFC').replace(/[\u200B-\u200D\uFEFF]/g,'').replace(/\\s+/g,' ').trim();
              el.focus({{preventScroll:true}});
              const value=(el.tagName==='TEXTAREA'||el.tagName==='INPUT')?el.value:(el.innerText||el.textContent||'');
              try{{if(el.tagName==='TEXTAREA'||el.tagName==='INPUT')el.setSelectionRange(value.length,value.length);else{{const sel=window.getSelection(),range=document.createRange();range.selectNodeContents(el);range.collapse(false);sel.removeAllRanges();sel.addRange(range);}}}}catch(e){{}}
              const probe=norm({self._js_string(probe)});
              const userSelectors={self._js_string(user_selectors)};const users=new Set();
              for(const sel of userSelectors){{try{{document.querySelectorAll(sel).forEach(n=>users.add(n));}}catch(e){{}}}}
              const stop=['button[data-testid=\"stop-button\"]','button[aria-label*=\"Stop\" i]','button[title*=\"Stop\" i]','[data-testid*=\"stop\" i]','button[aria-label*=\"Cancel\" i]'];
              const busy=stop.some(sel=>[...document.querySelectorAll(sel)].some(n=>{{const r=n.getBoundingClientRect(),st=getComputedStyle(n);return r.width>0&&r.height>0&&st.display!=='none'&&st.visibility!=='hidden';}}));
              const hasProbe=!!probe&&norm(value).includes(probe.slice(0,Math.min(48,probe.length)));
              const expectedCount=__EXPECTED_COUNT__;
              const expectedBusy=__EXPECTED_BUSY__;
              const countUnchanged=expectedCount===null||users.size===expectedCount;
              const busyUnchanged=!busy&&!expectedBusy;
              return {{ok:hasProbe&&countUnchanged&&busyUnchanged,hasProbe,userCount:users.size,busy,
                reason:!hasProbe?'Verified prompt is no longer in the composer':!countUnchanged?'A new user turn appeared after the click':!busyUnchanged?'Generation is already active':'ready'}};
            }})()""".replace('__EXPECTED_COUNT__', 'null' if expected_user_count is None else str(int(expected_user_count))).replace('__EXPECTED_BUSY__', str(bool(expected_busy)).lower())
            preflight = page.evaluate(preflight_script, timeout=10) or {}
            if not preflight.get("ok"):
                self._diag(ai, "Enter fallback skipped by submission guard",
                           reason=preflight.get("reason", "preflight failed"),
                           user_count=preflight.get("userCount", 0), busy=preflight.get("busy", False))
                return False, preflight

            key = {"key": "Enter", "code": "Enter", "windowsVirtualKeyCode": 13}
            page.call("Input.dispatchKeyEvent", {"type": "keyDown", **key}, timeout=6)
            page.call("Input.dispatchKeyEvent", {"type": "char", "text": "\r", "unmodifiedText": "\r", **key}, timeout=6)
            page.call("Input.dispatchKeyEvent", {"type": "keyUp", **key}, timeout=6)
            self._diag(ai, "CDP Enter key dispatched as guarded send fallback")

            verify_script = f"""(() => {{
              const el=document.querySelector({selector});
              const norm=v=>String(v||'').normalize('NFC').replace(/[\u200B-\u200D\uFEFF]/g,'').replace(/\\s+/g,' ').trim();
              const value=el?((el.tagName==='TEXTAREA'||el.tagName==='INPUT')?el.value:(el.innerText||el.textContent||'')):'';
              const body=norm(document.body.innerText||'');
              const probe=norm({self._js_string(probe)}),prefix=probe.slice(0,Math.min(48,probe.length));
              const userSelectors={self._js_string(user_selectors)};const users=new Set();
              for(const sel of userSelectors){{try{{document.querySelectorAll(sel).forEach(n=>users.add(n));}}catch(e){{}}}}
              const matchingUser=[...users].some(n=>norm(n.innerText||n.textContent||'').includes(probe));
              const stops=['button[data-testid=\"stop-button\"]','button[aria-label*=\"Stop\" i]','button[title*=\"Stop\" i]','[data-testid*=\"stop\" i]','button[aria-label*=\"Cancel\" i]'];
              const busy=stops.some(sel=>[...document.querySelectorAll(sel)].some(n=>{{const r=n.getBoundingClientRect(),st=getComputedStyle(n);return r.width>0&&r.height>0&&st.display!=='none'&&st.visibility!=='hidden';}}));
              const composerText=norm(value),composerCleared=!composerText;
              const newUserTurn=matchingUser&&users.size>__BASE_USER_COUNT__;
              const moved=!!prefix&&body.includes(prefix)&&!composerText.includes(prefix);
              const newlyBusy=busy&& !__BASE_BUSY__;
              const confirmed=moved||newUserTurn||newlyBusy||(composerCleared&&__PROBE_WAS_PRESENT__);
              return {{confirmed,movedToTranscript:moved,newUserTurn,newlyBusy,composerCleared,
                composerStillHasPrompt:composerText.includes(prefix),userCount:users.size,busy}};
            }})()""".replace('__BASE_USER_COUNT__', str(int(preflight.get("userCount", 0)))).replace('__BASE_BUSY__', str(bool(preflight.get("busy", False))).lower()).replace('__PROBE_WAS_PRESENT__', str(bool(preflight.get("hasProbe", False))).lower())
            deadline = time.monotonic() + 8.0
            last = {}
            while time.monotonic() < deadline:
                if self._cancel_event.is_set():
                    raise CDPError("Stopped by user while confirming Enter-key submission.")
                last = page.evaluate(verify_script, timeout=10) or {}
                if last.get("confirmed"):
                    self._diag(ai, "Enter fallback submission confirmed",
                               moved_to_transcript=last.get("movedToTranscript"),
                               new_user_turn=last.get("newUserTurn"), generation_started=last.get("newlyBusy"),
                               composer_cleared=last.get("composerCleared"))
                    return True, last
                if not last.get("composerStillHasPrompt"):
                    break
                time.sleep(0.1)
            self._diag(ai, "Enter fallback acceptance not confirmed",
                       composer_still_has_prompt=last.get("composerStillHasPrompt", False),
                       generation_busy=last.get("busy", False), user_count=last.get("userCount", 0))
            return False, last
        send_script = f"""(() => {{
          const ai={self._js_string(ai)};
          const composer=document.querySelector({selector});
          if(!composer)return {{ok:false,reason:'Composer disappeared after prompt entry'}};
          const cr=composer.getBoundingClientRect();
          const visible=el=>{{
            if(!el||!el.isConnected)return false;
            const r=el.getBoundingClientRect(),st=getComputedStyle(el);
            return r.width>=12&&r.height>=12&&st.display!=='none'&&st.visibility!=='hidden'
              &&Number(st.opacity)!==0&&el.getAttribute('aria-hidden')!=='true';
          }};
          const disabled=el=>!!(el.disabled||el.getAttribute('disabled')!==null
            ||el.getAttribute('aria-disabled')==='true'
            ||/(^|\\s)(ds-button--disabled|disabled)(\\s|$)/i.test(typeof el.className==='string'?el.className:''));
          const clickTarget=el=>{{
            if(!el)return null;
            if(el.matches('button,[role="button"]'))return el;
            return el.closest('button,[role="button"]');
          }};
          const labelOf=el=>{{
            const nested=[...el.querySelectorAll('svg,mat-icon,[data-testid],[aria-label],[title]')].flatMap(node=>[
              node.getAttribute('aria-label'),node.getAttribute('title'),node.getAttribute('data-testid'),
              node.getAttribute('data-mat-icon-name'),node.getAttribute('fonticon'),
              typeof node.className==='string'?node.className:'']);
            return [el.innerText,el.getAttribute('aria-label'),el.getAttribute('title'),
              el.getAttribute('data-testid'),el.getAttribute('data-test-id'),
              typeof el.className==='string'?el.className:'',...nested].filter(Boolean).join(' ').toLowerCase();
          }};
          const near=el=>{{
            const r=el.getBoundingClientRect();
            return Math.abs((r.top+r.height/2)-(cr.top+cr.height/2))<Math.max(190,cr.height*2.2)
              &&r.left>=cr.left-100&&r.left<=cr.right+300&&r.top<=cr.bottom+160;
          }};
          const candidates=[]; const add=(el,source,priority)=>{{
            el=clickTarget(el);
            if(!el||candidates.some(item=>item.el===el)||!visible(el)||disabled(el)||!near(el))return;
            const label=labelOf(el);
            if(/stop|cancel|voice|microphone|dictat|record|attach|upload|menu|more options|search/.test(label))return;
            const r=el.getBoundingClientRect();
            const distance=Math.abs((r.left+r.width/2)-cr.right)+Math.abs((r.top+r.height/2)-(cr.bottom-8));
            candidates.push({{el,label,source,score:priority-distance*.08,x:r.left+r.width/2,y:r.top+r.height/2}});
          }};

          // Site-specific send controls. DeepSeek uses a div[role=button], not a native button.
          if(ai==='DeepSeek'){{
            document.querySelectorAll('div[role="button"].ds-button.ds-button--primary.ds-button--filled,' +
              '[role="button"].ds-button.ds-button--primary.ds-button--filled').forEach(el=>add(el,'DeepSeek ds-button',280));
            try {{
              document.querySelectorAll('svg path[d^="M8.3125 0.980206"]').forEach(path=>add(path.closest('[role="button"]'),'DeepSeek send SVG path',300));
            }} catch(e) {{}}
          }} else if(ai==='Gemini'){{
            document.querySelectorAll(
              'mat-icon[data-mat-icon-name="arrow_upward"],mat-icon[fonticon="arrow_upward"],' +
              'mat-icon[data-mat-icon-name="send"],mat-icon[fonticon="send"]'
            ).forEach(icon=>{{
              let target=icon.closest('button,[role="button"]');
              if(!target){{for(let p=icon.parentElement,depth=0;p&&depth<4;p=p.parentElement,depth++){{
                if(p.matches('button,[role="button"]')){{target=p;break;}}
              }}}}
              add(target||icon,'Gemini arrow_upward',260);
            }});
          }} else if(ai==='ChatGPT'){{
            // Current ChatGPT composer send icon supplied by the user's live DOM:
            // <svg class="icon-primary-action text-composer-primary">…</svg>
            // Resolve its containing button/role=button, then click the container via CDP.
            // Primary identifier from the user's live ChatGPT DOM:
            // <svg class="icon-primary-action text-composer-primary">…</svg>
            // The icon is not itself clickable; click its nearest button/role=button.
            document.querySelectorAll(
              'svg.icon-primary-action.text-composer-primary,' +
              'svg[class~="icon-primary-action"][class~="text-composer-primary"],' +
              'svg.icon-primary-action'
            ).forEach(icon=>add(icon,'ChatGPT composer SVG class signature',330));
            // Precise path signature fallback in case ChatGPT renames the SVG classes.
            // Keep the same safety checks: visible, enabled, and adjacent to this composer.
            try {{
              document.querySelectorAll('svg:has(path[d^="M9.33467 16.6663V4.93978"])')
                .forEach(icon=>add(icon,'ChatGPT composer SVG path signature',310));
            }} catch(e) {{}}
            // Stable fallbacks for other ChatGPT layouts/builds.
            document.querySelectorAll(
              'button[data-testid="send-button"],[role="button"][data-testid="send-button"],' +
              'button[aria-label="Send prompt" i],button[aria-label="Send message" i],' +
              'button[aria-label="Send" i],[role="button"][aria-label="Send" i]'
            ).forEach(el=>add(el,'ChatGPT send-button fallback',280));
          }}

          // Accessible-label fallback when a site changes its markup.
          const all=[...document.querySelectorAll('button,[role="button"]')];
          for(const el of all){{
            if(!visible(el)||disabled(el))continue;
            const label=labelOf(el);
            const exact=/send|submit|paper.?plane/.test(label);
            const up=/arrow_upward/.test(label)&&(ai==='Gemini');
            if(exact||up)add(el,'accessible label',150);
          }}
          if(!candidates.length)return {{ok:false,reason:'No enabled Send control was found beside the editor. The prompt remains in the composer.'}};
          candidates.sort((a,b)=>b.score-a.score);
          if(candidates.length>1&&Math.abs(candidates[0].score-candidates[1].score)<2)
            return {{ok:false,reason:'More than one Send control matched; refusing to click an ambiguous button.'}};
          const chosen=candidates[0];
          chosen.el.scrollIntoView({{block:'nearest',inline:'nearest'}});
          const r=chosen.el.getBoundingClientRect();
          const probe={self._js_string(probe)};
          const norm=v=>String(v||'').normalize('NFC').replace(/[\u200B-\u200D\uFEFF]/g,'').replace(/\\s+/g,' ').trim();
          const composerText=(composer.tagName==='TEXTAREA'||composer.tagName==='INPUT')?composer.value:(composer.innerText||composer.textContent||'');
          const userSelectors={self._js_string(user_selectors)};
          const userNodes=new Set();
          for(const sel of userSelectors){{try{{document.querySelectorAll(sel).forEach(node=>userNodes.add(node));}}catch(e){{}}}}
          const stopSelectors=['button[data-testid="stop-button"]','button[aria-label*="Stop" i]','button[title*="Stop" i]','[data-testid*="stop" i]','button[aria-label*="Cancel" i]'];
          const busyBefore=stopSelectors.some(sel=>[...document.querySelectorAll(sel)].some(visible));
          return {{ok:true,x:r.left+r.width/2,y:r.top+r.height/2,label:chosen.label||chosen.source,
            source:chosen.source,userCount:userNodes.size,busyBefore,
            probeInComposer:norm(composerText).includes(norm(probe)),
            probeInBodyBefore:norm(document.body.innerText||'').replace(norm(composerText),'').includes(norm(probe))}};
        }})()"""
        sent = None
        send_deadline = time.monotonic() + 7.0
        while time.monotonic() < send_deadline:
            sent = page.evaluate(send_script, timeout=18)
            if sent and sent.get("ok"):
                break
            reason = (sent or {}).get("reason", "")
            if "No enabled Send control" not in reason:
                break
            # DeepSeek enables the ds-button asynchronously after its textarea input event.
            time.sleep(0.12)
        if not sent or not sent.get("ok"):
            reason = (sent or {}).get("reason", "Send control could not be verified")
            self._diag(ai, "Send control not resolved; trying guarded Enter fallback", reason=reason)
            enter_confirmed, enter_state = try_enter_send()
            if enter_confirmed:
                self._submitted.add(ai)
                self.callback("site_status", {
                    "ai": ai, "status": "Send confirmed via Enter key; waiting for response…",
                })
                return {
                    "manual_send_required": False,
                    "confirmation_uncertain": False,
                    "send_method": "Enter key",
                    "attachment_warning": attachment_warning,
                    "attached_names": attached_names,
                }
            result = {
                "manual_send_required": True,
                "reason": reason,
                "attachment_warning": attachment_warning,
                "attached_names": attached_names,
            }
            self.callback("site_status", {
                "ai": ai,
                "status": "Prompt is verified in the editor, but neither a safe Send button nor a confirmed Enter-key submission was found. Click Send manually in this tab; collection is monitoring.",
            })
            return result

        # One physical Send click is attempted per site/run. If that click is not
        # accepted and the prompt remains in the composer, the guarded Enter fallback
        # may send it once. The guard prevents an Enter press after a confirmed send.
        max_send_attempts = 1
        confirmation = None
        confirmed = False
        send_method = "Send button click"
        for attempt in range(1, max_send_attempts + 1):
            if self._cancel_event.is_set():
                raise CDPError("Stopped by user before sending.")
            if attempt > 1:
                # Re-resolve the live send button after React/Angular updates.
                refreshed = page.evaluate(send_script, timeout=12)
                if not refreshed or not refreshed.get("ok"):
                    self._diag(ai, "Send retry stopped; control no longer safely available",
                               attempt=attempt, reason=(refreshed or {}).get("reason", "no match"))
                    break
                # Never click again if the draft has left the editor or generation began.
                retry_guard = f"""(() => {{
                  const el=document.querySelector({selector});
                  const value=el?((el.tagName==='TEXTAREA'||el.tagName==='INPUT')?el.value:(el.innerText||el.textContent||'')):'';
                  const norm=v=>String(v||'').normalize('NFC').replace(/[\u200B-\u200D\uFEFF]/g,'').replace(/\\s+/g,' ').trim();
                  const probe=norm({self._js_string(probe)});
                  const selectors={self._js_string(user_selectors)};const users=new Set();
                  for(const sel of selectors){{try{{document.querySelectorAll(sel).forEach(n=>users.add(n));}}catch(e){{}}}}
                  const stop=['button[data-testid="stop-button"]','button[aria-label*="Stop" i]','button[title*="Stop" i]','[data-testid*="stop" i]','button[aria-label*="Cancel" i]'];
                  const busy=stop.some(sel=>[...document.querySelectorAll(sel)].some(n=>{{const r=n.getBoundingClientRect(),s=getComputedStyle(n);return r.width>0&&r.height>0&&s.display!=='none'&&s.visibility!=='hidden';}}));
                  return {{draftStillPresent:norm(value).includes(probe),busy,userCount:users.size}};
                }})()"""
                guard = page.evaluate(retry_guard, timeout=10) or {}
                if not guard.get("draftStillPresent") or guard.get("busy") or guard.get("userCount", 0) > sent.get("userCount", 0):
                    self._diag(ai, "Send retry skipped to avoid duplicate submission", attempt=attempt,
                               draft_still_present=guard.get("draftStillPresent"), generation_busy=guard.get("busy"),
                               user_turn_count=guard.get("userCount"))
                    break
                sent = refreshed
            self._diag(ai, "CDP Send attempt", attempt=attempt, max_attempts=max_send_attempts,
                       source=sent.get("source"), label=sent.get("label"))
            page.call("Input.dispatchMouseEvent", {
                "type": "mouseMoved", "x": sent["x"], "y": sent["y"], "button": "none",
            })
            page.call("Input.dispatchMouseEvent", {
                "type": "mousePressed", "x": sent["x"], "y": sent["y"],
                "button": "left", "clickCount": 1,
            })
            page.call("Input.dispatchMouseEvent", {
                "type": "mouseReleased", "x": sent["x"], "y": sent["y"],
                "button": "left", "clickCount": 1,
            })
            self._diag(ai, "CDP Send click dispatched", attempt=attempt, x=round(sent["x"], 1),
                       y=round(sent["y"], 1), source=sent.get("source"))

            # Probe acceptance quickly after each attempt. For Gemini, retain its
            # original longer confirmation window and single-click behavior.
            verify_deadline = time.monotonic() + (14.0 if ai == "Gemini" else 10.0)
            verify_script = f"""(() => {{
              const el=document.querySelector({selector});
              const probe={self._js_string(probe)};
              const norm=v=>String(v||'').normalize('NFC').replace(/[\u200B-\u200D\uFEFF]/g,'').replace(/\\s+/g,' ').trim();
              const value=el?((el.tagName==='TEXTAREA'||el.tagName==='INPUT')?el.value:(el.innerText||el.textContent||'')):'';
              const body=norm(document.body.innerText||'');const probeText=norm(probe);
              const userSelectors={self._js_string(user_selectors)};const userNodes=new Set();
              for(const sel of userSelectors){{try{{document.querySelectorAll(sel).forEach(node=>userNodes.add(node));}}catch(e){{}}}}
              const matchingUser=[...userNodes].some(node=>norm(node.innerText||node.textContent||'').includes(probeText));
              const stopSelectors=['button[data-testid="stop-button"]','button[aria-label*="Stop" i]','button[title*="Stop" i]','[data-testid*="stop" i]','button[aria-label*="Cancel" i]'];
              const busyNow=stopSelectors.some(sel=>[...document.querySelectorAll(sel)].some(node=>{{const r=node.getBoundingClientRect(),st=getComputedStyle(node);return r.width>0&&r.height>0&&st.display!=='none'&&st.visibility!=='hidden';}}));
              const newUserTurn=matchingUser&&userNodes.size>{int(sent.get('userCount', 0))};
              const composerCleared=!norm(value);
              const newlyBusy=busyNow&&!{str(bool(sent.get('busyBefore'))).lower()};
              const probePrefix=probeText.slice(0, Math.min(48, probeText.length));
              const probeAppeared=!!probeText&&(body.includes(probeText)||(probePrefix.length>=24&&body.includes(probePrefix)));
              const moved=probeAppeared&&!norm(value).includes(probePrefix)&&!{str(bool(sent.get('probeInBodyBefore'))).lower()};
              const clearedVerifiedDraft=composerCleared&&{str(bool(sent.get('probeInComposer'))).lower()};
              return {{confirmed:moved||newUserTurn||newlyBusy||clearedVerifiedDraft,
                clearedVerifiedDraft,movedToTranscript:moved,newUserTurn,newlyBusy,composerCleared,
                composerStillHasPrompt:norm(value).includes(probeText),userCount:userNodes.size}};
            }})()"""
            while time.monotonic() < verify_deadline:
                if self._cancel_event.is_set():
                    raise CDPError("Stopped by user while confirming submission.")
                confirmation = page.evaluate(verify_script, timeout=12)
                if confirmation and confirmation.get("confirmed"):
                    confirmed = True
                    break
                if ai != "Gemini" and confirmation and not confirmation.get("composerStillHasPrompt"):
                    # The composer changed, but transcript/generation evidence is not
                    # conclusive. Do not repeat a click when it might already be accepted.
                    break
                time.sleep(0.1)
            if confirmed:
                break
            if ai == "Gemini":
                break
            # Before another click, the composer must still hold the prompt. The next
            # iteration re-detects the active, enabled control and its current position.
            if not confirmation or not confirmation.get("composerStillHasPrompt"):
                break
            if attempt < max_send_attempts:
                time.sleep(0.45)

        if not confirmed and confirmation and confirmation.get("composerStillHasPrompt"):
            # The button click did not appear to submit. Enter is allowed only if the
            # original user-turn count is unchanged, no generation is active, and the
            # verified prompt is still in the composer. This prevents a duplicate send.
            enter_confirmed, enter_state = try_enter_send(
                expected_user_count=sent.get("userCount"),
                expected_busy=bool(sent.get("busyBefore")),
            )
            if enter_confirmed:
                confirmed = True
                confirmation = enter_state
                send_method = "Enter key fallback"

        self._diag(ai, "Submission confirmation result", confirmed=confirmed,
                   total_fill_and_send_ms=int((time.monotonic() - _t_fill) * 1000),
                   attempts=attempt, moved_to_transcript=(confirmation or {}).get("movedToTranscript"),
                   new_user_turn=(confirmation or {}).get("newUserTurn"),
                   generation_started=(confirmation or {}).get("newlyBusy"),
                   composer_cleared=(confirmation or {}).get("composerCleared"),
                   composer_still_has_prompt=(confirmation or {}).get("composerStillHasPrompt"))
        if confirmed:
            self.callback("site_status", {
                "ai": ai,
                "status": f"Send confirmed via {send_method}; waiting for response…",
            })
        else:
            self.callback("site_status", {
                "ai": ai,
                "status": "Send click and guarded Enter fallback were unable to confirm acceptance. Check the tab; collection will monitor without risking another submission.",
            })

        self._submitted.add(ai)
        result = {
            "manual_send_required": False,
            "confirmation_uncertain": not confirmed,
            "attachment_warning": attachment_warning,
            "attached_names": attached_names,
            "send_method": send_method if confirmed else "Send button click (acceptance uncertain)",
        }
        if not confirmed:
            self.callback("site_status", {
                "ai": ai,
                "status": "Submission acceptance is uncertain. Check the tab while AI Bridge monitors for a reply."
            })
        return result

    def _bring_tab_to_front(self, ai, page=None):
        """Activate the site's Chrome tab so it is foregrounded (background tabs are throttled)."""
        try:
            page = page or self._page(ai)
            page.call("Page.bringToFront", timeout=6)
            try:  # also ask Chrome itself to raise the window/tab so you actually see the site
                target_id = (self._targets.get(ai) or {}).get("id")
                if target_id:
                    urllib.request.urlopen(f"http://127.0.0.1:{self.PORT}/json/activate/{target_id}", timeout=2).read()
            except Exception:
                pass
            return True
        except Exception as exc:
            self._diag(ai, "Bring tab to front failed", error_type=type(exc).__name__, error=str(exc))
            return False

    def _visit_all_sites(self):
        """Show each website for exactly SITE_VISIT_SECONDS, then ask the UI to return to AI Bridge."""
        dwell = float(self.SITE_VISIT_SECONDS)
        self._diag("SYSTEM", "Site visit pass started", seconds_per_site=dwell, sites=", ".join(AIS))
        for ai in AIS:
            if self._cancel_event.is_set():
                break
            self.callback("site_status", {"ai": ai, "status": f"Showing this website for {dwell:g} seconds…"})
            try:
                shown = self._bring_tab_to_front(ai)
            except Exception:
                shown = False
            started_at = time.monotonic()          # the 2 seconds start once the tab is in front
            self._cancel_event.wait(dwell)
            self._diag(ai, "Site visit", brought_to_front=shown, requested_seconds=dwell,
                       actual_seconds=round(time.monotonic() - started_at, 2))
        self.callback("focus_app", {})
        self._diag("SYSTEM", "Site visit pass finished; returning to AI Bridge")
        self._cancel_event.wait(0.3)

    def prepare(self, prompt, fallback_prompt=None, attachments=None):
        if self._collecting:
            self.callback("error", "A response collection is still running. Wait for it to finish or press Stop before starting another prompt.")
            return
        self._cancel_event.clear()
        self._collecting = True
        def worker():
            submitted = []
            failures = {}
            self._diag("SYSTEM", "Submission run started", sites=", ".join(AIS), prompt_characters=len(prompt),
                       attachment_count=len(attachments or []))
            self._baseline = {}
            self._baseline_media = {}
            self._response_media = {ai: [] for ai in AIS}
            self._submitted = set()
            self._prepared = set()
            # Give all three already-open website tabs a full settling period before
            # touching any composer. The countdown is visible in the Tk interface and
            # Stop can cancel it immediately. No composer detection, typing, or Send
            # clicks occur until this countdown completes.
            cooldown = self.PRE_SEND_COOLDOWN_SECONDS
            self._diag("SYSTEM", "Pre-send cooldown started", seconds=cooldown,
                       sites="ChatGPT, Gemini, DeepSeek")
            for remaining in range(cooldown, 0, -1):
                if self._cancel_event.is_set():
                    self._diag("SYSTEM", "Pre-send cooldown cancelled", remaining_seconds=remaining)
                    for ai in AIS:
                        failures[ai] = "Stopped during the 10-second pre-send cooldown; nothing was entered or sent."
                        self.callback("site_status", {"ai": ai, "status": failures[ai]})
                    self.callback("countdown", {"remaining": 0, "total": cooldown, "message": "Cancelled"})
                    self._collecting = False
                    self.callback("collected", {"_errors": failures, "_media": dict(self._response_media)})
                    return
                self.callback("countdown", {
                    "remaining": remaining,
                    "total": cooldown,
                    "message": f"Websites are open — sending starts in {remaining}s",
                })
                if self._cancel_event.wait(1.0):
                    continue
            if self._cancel_event.is_set():
                self._diag("SYSTEM", "Pre-send cooldown cancelled at completion")
                for ai in AIS:
                    failures[ai] = "Stopped during the 10-second pre-send cooldown; nothing was entered or sent."
                    self.callback("site_status", {"ai": ai, "status": failures[ai]})
                self.callback("countdown", {"remaining": 0, "total": cooldown, "message": "Cancelled"})
                self._collecting = False
                self.callback("collected", {"_errors": failures, "_media": dict(self._response_media)})
                return
            self._diag("SYSTEM", "Pre-send cooldown completed", seconds=cooldown)
            self.callback("phase", f"Cooldown complete. Showing each website for exactly {self.SITE_VISIT_SECONDS:g} seconds, then returning to AI Bridge…")
            self._visit_all_sites()
            self.callback("countdown", {"remaining": 0, "total": cooldown, "message": "Cooldown complete — sending now"})
            self.callback("phase", "Cooldown complete. Phase A: entering the prompt and submitting to ChatGPT, Gemini and DeepSeek.")
            # Each site starts being monitored the moment ITS prompt is submitted, so reply
            # collection overlaps with submitting to the remaining sites (no idle waiting).
            results = {}
            collection_errors = {}
            active_collectors = set()
            lock = threading.Lock()
            state = {"phase_a_done": False, "final": False}

            def finalize_locked():
                if state["final"] or not state["phase_a_done"] or active_collectors:
                    return
                state["final"] = True
                payload = dict(results)
                errors = dict(failures)
                errors.update(collection_errors)
                payload["_errors"] = errors
                payload["_media"] = dict(self._response_media)
                self.callback("collected", payload)
                self._collecting = False

            def collect_one(ai):
                try:
                    results[ai] = self._collect_one(ai)
                except Exception as exc:
                    self._diag(ai, "Response collection failed", error_type=type(exc).__name__, error=str(exc))
                    collection_errors[ai] = str(exc)
                finally:
                    if results.get(ai):
                        self._diag(ai, "Response collection returned", response_characters=len(results[ai]))
                    self.callback("site_status", {
                        "ai": ai,
                        "status": "Response retrieved" if results.get(ai)
                                  else f"Collection failed: {collection_errors.get(ai, 'No response')}"
                    })
                    with lock:
                        active_collectors.discard(ai)
                        finalize_locked()

            def start_collector(ai):
                with lock:
                    active_collectors.add(ai)
                threading.Thread(
                    target=collect_one, args=(ai,), daemon=True,
                    name=f"ai-bridge-collect-{ai.lower()}",
                ).start()

            # Phase A completes for every site before any response wait begins.
            for ai in AIS:
                if self._cancel_event.is_set():
                    failures[ai] = "Stopped by user before this site was submitted."
                    self.callback("site_status", {"ai": ai, "status": failures[ai]})
                    continue
                self._diag(ai, "Site submission phase started")
                self.callback("site_status", {"ai": ai, "status": "Preparing prompt…"})
                try:
                    page = self._page(ai)
                    # Rich editors only accept focus/typing reliably in the active tab.
                    self._bring_tab_to_front(ai, page)
                    time.sleep(0.15)
                    result = self._fill_and_send(
                        page, ai, prompt, fallback_prompt=fallback_prompt,
                        attachments=list(attachments or []),
                    )
                    submitted.append(ai)
                    attached_count = len(result.get("attached_names", [])) if isinstance(result, dict) else 0
                    mode = (f"prompt sent; {attached_count} reference file(s) selected" if attached_count
                            else "prompt sent; code/text kept in the prompt")
                    warning = result.get("attachment_warning") if isinstance(result, dict) else None
                    if result.get("manual_send_required"):
                        status = "Prompt ready — click Send manually in this tab; collection is monitoring."
                    elif result.get("confirmation_uncertain"):
                        status = "Send clicked — acceptance uncertain; monitoring for the reply."
                    else:
                        status = f"Submitted — {mode}"
                    if warning:
                        status += f" — attachment issue: {warning}"
                    self.callback("site_status", {"ai": ai, "status": status})
                    self._diag(ai, "Site preparation finished", prepared=True,
                               manual_send_required=result.get("manual_send_required"),
                               confirmation_uncertain=result.get("confirmation_uncertain"),
                               attached_count=attached_count)
                except Exception as exc:
                    self._diag(ai, "Site preparation failed", error_type=type(exc).__name__, error=str(exc))
                    failures[ai] = str(exc)
                    self.callback("site_status", {"ai": ai, "status": f"Not submitted: {exc}"})
                if ai in self._prepared and not self._cancel_event.is_set():
                    start_collector(ai)
            self.callback("focus_app", {})
            self.callback("phase", "All sites submitted; each reply is already being monitored independently. No site is clicked twice.")
            self._diag("SYSTEM", "Collection phase started", prepared_sites=", ".join(a for a in AIS if a in self._prepared),
                       submission_failures=len(failures))
            if failures:
                self.callback("site_errors", failures)
            with lock:
                state["phase_a_done"] = True
                finalize_locked()
        threading.Thread(target=worker, daemon=True, name="ai-bridge-submit-all").start()

    def _response_dom_probe(self, page, ai, anchor=""):
        """Return selector/visibility counts only; never read prompt or response text."""
        selectors = self._js_string(self.RESPONSES[ai])
        script = f"""(() => {{
          const selectors={selectors};
          const queryDeep=sel=>{{const out=[],visited=new Set(),q=[document];while(q.length){{const r=q.shift();if(!r||visited.has(r))continue;visited.add(r);try{{out.push(...r.querySelectorAll(sel));}}catch(e){{}}try{{r.querySelectorAll('*').forEach(el=>{{if(el.shadowRoot)q.push(el.shadowRoot);}});}}catch(e){{}}}}return [...new Set(out)];}};
          const visible=el=>{{const r=el.getBoundingClientRect(),s=getComputedStyle(el);return el.isConnected&&r.width>2&&r.height>2&&s.display!=='none'&&s.visibility!=='hidden'&&Number(s.opacity)!==0;}};
          const counts={{}};
          selectors.forEach(sel=>{{const nodes=queryDeep(sel);counts[sel]={{matches:nodes.length,visible:nodes.filter(visible).length}};}});
          const assistant=queryDeep('[data-message-author-role="assistant"]');
          const user=queryDeep('[data-message-author-role="user"]');
          const models=queryDeep('model-response,[data-testid*="model-response"]');
          const deepseek=queryDeep('.ds-markdown,[class*="ds-markdown"]');
          const turns=queryDeep('[data-testid*="conversation-turn"]');
          return {{host:location.hostname,ready_state:document.readyState,selector_counts:counts,
            assistant_role_matches:assistant.length,assistant_role_visible:assistant.filter(visible).length,
            user_role_matches:user.length,model_response_matches:models.length,
            deepseek_markdown_matches:deepseek.length,conversation_turn_matches:turns.length,
            iframe_count:document.querySelectorAll('iframe').length,
            visibility_state:document.visibilityState,has_focus:document.hasFocus(),
            structure:(()=>{{
              try {{
                const main=document.querySelector('main')||document.body;
                const attrs={{}}, ids={{}};
                [...main.querySelectorAll('*')].slice(0,5000).forEach(el=>{{
                  for (const a of el.attributes) if (a.name.startsWith('data-')) attrs[a.name]=(attrs[a.name]||0)+1;
                  const t=el.getAttribute('data-testid'); if (t) {{ const k=t.replace(/[0-9]+/g,'#').slice(0,40); ids[k]=(ids[k]||0)+1; }}
                }});
                const top=o=>Object.entries(o).sort((a,b)=>b[1]-a[1]).slice(0,14).map(e=>e[0]+':'+e[1]).join(' ');
                const anchor={self._js_string(anchor)};
                let chain='';
                if (anchor) {{
                  const norm=t=>String(t||'').replace(/\\s+/g,' ').trim();
                  const tw=document.createTreeWalker(main,NodeFilter.SHOW_TEXT); let hit=null,n,count=0;
                  while((n=tw.nextNode())){{ if(n.nodeValue&&norm(n.nodeValue).includes(anchor)){{hit=n;count++;}} }}
                  if (hit) {{
                    const parts=[]; let el=hit.parentElement;
                    for (let i=0;el&&i<9;i++,el=el.parentElement) {{
                      const names=[...el.attributes].filter(a=>a.name.startsWith('data-')||a.name==='role').map(a=>a.name+(a.name==='data-testid'||a.name==='role'?'='+a.value.slice(0,30):'')).join(',');
                      let after=0; for (let s=el.nextElementSibling;s;s=s.nextElementSibling) after++;
                      parts.push(el.tagName.toLowerCase()+'['+names+']+'+after);
                    }}
                    chain=count+' match(es): '+parts.join(' < ');
                  }} else chain='anchor text not found in <main>';
                }}
                return {{data_attrs:top(attrs),testids:top(ids),articles:main.querySelectorAll('article').length,
                  sections:main.querySelectorAll('section').length,pres:main.querySelectorAll('pre').length,
                  markdown:main.querySelectorAll('.markdown,[class*="markdown"],[class*="prose"]').length,anchor_chain:chain}};
              }} catch(e) {{ return {{error:String(e).slice(0,100)}}; }}
            }})()}};
        }})()"""
        try:
            return page.evaluate(script, timeout=12) or {}
        except Exception as exc:
            return {"probe_error_type": type(exc).__name__, "probe_error": str(exc)[:180]}

    def _collect_one(self, ai, timeout=None):
        """Collect the complete new assistant turn, preserving all code blocks and images."""
        timeout = timeout or self.RESPONSE_TIMEOUT_SECONDS
        page = self._page(ai)
        baseline = list(self._baseline.get(ai, []))
        baseline_media = self._baseline_media.get(ai, set())
        deadline = time.monotonic() + timeout
        started = time.monotonic()
        last_progress_log = 0
        self._diag(ai, "Response monitoring started", timeout_seconds=timeout,
                   baseline_assistant_messages=len(baseline), baseline_images=len(baseline_media))
        previous_signature = None
        stable = 0
        stable_since = None  # monotonic time the reply text last changed
        relaxed_logged = False
        baseline_for_compare = None
        last_items = []
        new_media = []
        media_signature = ()
        media_now_cache = None
        loop_index = 0
        response_first_seen_at = None
        previous_media_signature = None
        media_stable = 0
        last_media = []

        if ai == "ChatGPT":
            # Strict: broad [data-testid*="stop"] / "Cancel" matches can stay on the page forever
            # and make the reply look "still generating" until the 300s timeout.
            stop_selectors = self._js_string([
                'button[data-testid="stop-button"]', 'button[aria-label="Stop streaming"]',
                'button[aria-label="Stop generating"]', 'form button[aria-label*="Stop" i]',
                'form [data-testid*="stop" i]', '#composer-submit-button[aria-label*="Stop" i]',
            ])
        else:
            stop_selectors = self._js_string([
                'button[data-testid="stop-button"]', 'button[aria-label*="Stop" i]', 'button[title*="Stop" i]',
                '[data-testid*="stop" i]', 'button[aria-label*="Cancel" i]',
            ])
        busy_script = f"""(() => {{
          const selectors={stop_selectors};
          return selectors.some(sel=>[...document.querySelectorAll(sel)].some(el=>{{
            const r=el.getBoundingClientRect(),st=getComputedStyle(el);
            return r.width>0&&r.height>0&&st.display!=='none'&&st.visibility!=='hidden'&&Number(st.opacity)!==0;
          }}));
        }})()"""

        while time.monotonic() < deadline:
            if self._cancel_event.is_set():
                self._diag(ai, "Response monitoring cancelled by user", elapsed_seconds=int(time.monotonic()-started))
                raise CDPError("Stopped by user.")
            _t_snap = time.monotonic()
            items = self._response_snapshot(page, ai)
            if not items and (time.monotonic() - started) >= 1.5:
                fallback_items = []
                anchor_text = self._prompt_anchor.get(ai, "")
                try:
                    if anchor_text:
                        fallback_items = self._response_snapshot(page, ai, relaxed=True, anchor=anchor_text)
                        mode = "prompt-anchored"
                    if not fallback_items:
                        fallback_items = self._response_snapshot(page, ai, relaxed=True)
                        mode = "relaxed-selector"
                except Exception:
                    fallback_items = []
                # Only the newest assistant turn, and never one that was already on the page.
                if fallback_items and fallback_items[-1] not in baseline:
                    if not relaxed_logged:
                        relaxed_logged = True
                        self._diag(ai, "Precise selectors found no reply; using fallback extraction",
                                   mode=mode, fallback_messages=len(fallback_items))
                    items = fallback_items[-1:]
                    baseline_for_compare = []
            snapshot_ms = int((time.monotonic() - _t_snap) * 1000)
            loop_index += 1
            if media_now_cache is None or loop_index % 3 == 1:
                media_now_cache = self._response_media_snapshot(page, ai)
                media_now = media_now_cache
                new_media = [item for item in media_now if item.get("src") not in baseline_media]
                media_signature = tuple(item.get("src", "") for item in new_media)
                if media_signature:
                    media_stable = media_stable + 1 if media_signature == previous_media_signature else 0
                else:
                    media_stable = 0
                previous_media_signature = media_signature
                last_media = new_media

            cmp_baseline = baseline if baseline_for_compare is None else baseline_for_compare
            baseline_for_compare = None
            common = 0
            while common < min(len(cmp_baseline), len(items)) and cmp_baseline[common] == items[common]:
                common += 1
            if common == len(cmp_baseline):
                new_items = items[common:]
            elif items and cmp_baseline and items[:-1] == cmp_baseline[:-1] and items[-1] != cmp_baseline[-1]:
                # A site may stream into the last assistant node rather than append a new one.
                new_items = [items[-1]]
            elif items and not cmp_baseline:
                new_items = items
            else:
                new_items = []

            if (ai == "ChatGPT" and new_items and sum(len(x) for x in new_items) < 200
                    and re.search(r"(^|\n)\s*(thinking|thought for|reasoning|searching|researching|browsing|analy[sz]ing)\b",
                                  "\n".join(new_items), re.I)):
                new_items = []  # a "Thinking…" status line is not the answer yet
            if new_items:
                if response_first_seen_at is None:
                    response_first_seen_at = time.monotonic()
                signature = tuple(new_items)
                if signature == previous_signature:
                    stable += 1
                else:
                    stable = 0
                    stable_since = time.monotonic()
                previous_signature = signature
                last_items = list(new_items)
            else:
                previous_signature = None
                stable = 0
                stable_since = None

            busy = bool(page.evaluate(busy_script))
            elapsed = int(time.monotonic() - started)
            if elapsed - last_progress_log >= 15:
                self._diag(ai, "Response monitoring progress", elapsed_seconds=elapsed,
                           assistant_nodes_seen=len(items), new_assistant_messages=len(new_items),
                           new_response_characters=sum(len(x) for x in new_items),
                           generation_busy=busy, stable_snapshots=stable, snapshot_ms=snapshot_ms,
                           generated_images_detected=len(new_media))
                if not items:
                    probe = self._response_dom_probe(page, ai, self._prompt_anchor.get(ai, ""))
                    self._diag(ai, "Response DOM probe (metadata only)", **probe)
                last_progress_log = elapsed
            if not busy and media_signature and media_stable >= 3 and not new_items:
                saved = self._download_response_media(page, ai, new_media)
                self._response_media[ai] = saved
                image_count = len([item for item in saved if item.get("path")])
                self._diag(ai, "Generated image response captured", detected_images=len(new_media), saved_images=image_count)
                if image_count:
                    return f"[Image response captured: {image_count} actual image file(s) saved. Use Open images in the Responses tab, or Upload generated images to GitHub.]"
                problems = "; ".join(item.get("error", "image download failed") for item in saved if item.get("error"))
                raise CDPError("The site rendered an image, but AI Bridge could not download it as a file. " + (problems or "The image element did not expose downloadable bytes."))

            # A short response needs extra settling time: otherwise a transient first
            # sentence can be mistaken for the completed answer when a site's busy/Stop
            # indicator is temporarily absent. Longer answers use a slightly lower floor.
            media_ready = not media_signature or media_stable >= 2
            current_text_length = sum(len(item.strip()) for item in new_items if item.strip())
            short_response = current_text_length < 160
            # Time-based settling (was: 4-5 polls x 1.25s + 5-8s minimum age). The site's
            # Stop/busy indicator must also be gone, so these windows can be short.
            stable_for = (time.monotonic() - stable_since) if stable_since is not None else 0.0
            stable_needed = 2.0 if short_response else 1.2
            minimum_age = 1.5 if short_response else 0.5
            response_age = (time.monotonic() - response_first_seen_at) if response_first_seen_at is not None else 0.0
            # If ChatGPT's "busy" flag never clears but the text has not changed for 15s, accept the
            # reply instead of waiting for the 300s timeout and then reporting nothing.
            busy_stuck = bool(busy and ai == "ChatGPT" and stable_for >= 15.0 and current_text_length >= 40)
            if busy_stuck and not locals().get("_busy_stuck_logged"):
                _busy_stuck_logged = True
                self._diag(ai, "Busy indicator still present but reply unchanged for 15s; accepting reply",
                           response_characters=current_text_length)
            if (new_items and stable_for >= stable_needed and response_age >= minimum_age
                    and (not busy or busy_stuck) and media_ready):
                saved = self._download_response_media(page, ai, new_media)
                self._response_media[ai] = saved
                # Keep every new assistant message; code can be split across messages by a site.
                combined = "\n\n".join(item.strip() for item in new_items if item.strip()).strip()
                self._diag(ai, "Response completed and stabilized", elapsed_seconds=elapsed,
                           assistant_messages=len(new_items), response_characters=len(combined),
                           generated_images_detected=len(new_media), saved_images=len([x for x in saved if x.get("path")]))
                return combined

            time.sleep(0.25)

        if last_items:
            partial = "\n\n".join(item.strip() for item in last_items if item.strip()).strip()
            self._diag(ai, "Response timeout with partial content", elapsed_seconds=int(time.monotonic()-started),
                       partial_response_characters=len(partial), stable_snapshots=stable)
            raise CDPError(
                "A partial response was captured but the site did not reach a confirmed stable completion. "
                "Use the Responses tab to inspect the current page and retry collection.\n\n" + partial[:1200]
            )
        if last_media:
            self._diag(ai, "Image response timeout", elapsed_seconds=int(time.monotonic()-started), detected_images=len(last_media))
            raise CDPError("Generated image content was detected, but the website did not finish rendering before timeout.")
        self._diag(ai, "Response timeout with no new assistant content", elapsed_seconds=int(time.monotonic()-started),
                   baseline_assistant_messages=len(baseline))
        raise CDPError(f"No new assistant text, code, or image response was detected before the site timeout ({timeout} seconds).")

    def collect(self):
        # Retry collection only; never re-submit the prompt.
        if self._collecting:
            self.callback("phase", "Collection is already running.")
            return
        submitted = [ai for ai in AIS if ai in self._prepared]
        if not submitted:
            self.callback("error", "No prepared browser composers are recorded. Prepare a prompt first.")
            return
        self._cancel_event.clear()
        self._collecting = True

        def worker():
            payload = {}
            errors = {}
            threads = []
            lock = threading.Lock()

            def one(ai):
                try:
                    payload[ai] = self._collect_one(ai)
                except Exception as exc:
                    errors[ai] = str(exc)
                finally:
                    with lock:
                        if len(payload) + len(errors) == len(submitted):
                            result = dict(payload)
                            result["_errors"] = dict(errors)
                            result["_media"] = dict(self._response_media)
                            self.callback("collected", result)
                            self._collecting = False

            for ai in submitted:
                thread = threading.Thread(target=one, args=(ai,), daemon=True)
                thread.start()
                threads.append(thread)
        threading.Thread(target=worker, daemon=True, name="ai-bridge-recollect").start()

    def close(self):
        for page in self._pages.values():
            page.close()
        self._pages.clear()
        self.callback("closed", {})


class App(tk.Tk):
    REPLY_RULES = (
        "For every file you change, reply with a line `File: <name>` (the name exactly as shown above) "
        "followed by that file's COMPLETE new content in its own code block. No omitted sections or "
        "placeholder comments. Do not include files you did not change. Add a short explanation at the end."
    )

    def __init__(self):
        super().__init__()
        # Tk widgets must only be touched by the thread running Tk's mainloop.
        # Browser/CDP workers communicate through this queue; they never call
        # self.after(), StringVar.set(), widget.config(), or other Tcl APIs.
        self._ui_event_queue = queue.Queue()
        self._ui_shutdown = False
        self._ui_poll_after_id = None
        self.title("AI Bridge — Browser + Local/GitHub")
        self.geometry("1180x940")
        self.minsize(920, 720)

        self.repo = ""
        self.branch = ""
        self.local_root = None  # Path to the currently opened local VS Code workspace
        self.token = ""
        self.all_paths = []
        self.files = []        # repo paths currently loaded
        self.texts = {}        # path -> text from GitHub
        self.previous = {}     # path -> text before last save
        self.replies = {a: "" for a in AIS}
        self.proposals = {a: {} for a in AIS}
        self.shown_ai = "ChatGPT"
        self.analysis = {}
        self.pending = 0
        self.api_errors = {}
        self._ssl_repair_running = False
        self._image_upload_running = False

        self.repo_var = tk.StringVar()
        self.branch_var = tk.StringVar(value="ai-bridge")
        self.token_var = tk.StringVar()
        self.filter_var = tk.StringVar()
        self.ai_var = tk.StringVar(value="ChatGPT")
        self.status_var = tk.StringVar(value="Open a local VS Code folder or connect a GitHub repository. Browser mode needs no AI API keys.")
        self.browser = None
        self._pending_run_kind = None
        self.browser_prompt_kind = "ask"
        self.attachments = []  # binary/non-code files to attach through the AI website
        self.prompt_code_files = {}  # local path -> UTF-8 text, embedded in the prompt (never uploaded)
        self.attach_noncode_var = tk.BooleanVar(value=True)
        self.diagnostics_var = tk.BooleanVar(value=True)
        self.diagnostics_path_var = tk.StringVar(value="Diagnostics: will be created when browser sessions start (metadata only)")
        self.countdown_var = tk.StringVar(value="Ready — open browser sessions, then press Start.")
        self.timer_var = tk.StringVar(value="⏱ 00:00  |  each site gets up to 60s to reply")
        self._run_t0 = None
        self._run_timer_active = False
        self._site_done = {}
        self.response_media = {a: [] for a in AIS}
        self.result_dir = None
        self.filter_var.trace_add("write", lambda *a: self.apply_filter())
        self.build_ui()
        self.refresh_attachment_view()
        self.protocol("WM_DELETE_WINDOW", self.close_app)
        # Start queue polling from the main thread only, after the widgets exist.
        self._schedule_ui_event_drain()

    # ---------- GitHub ----------
    def gh(self, method, path, body=None):
        data = json.dumps(body).encode() if body is not None else None
        req = urllib.request.Request(API + path, data=data, method=method)
        req.add_header("Authorization", f"Bearer {self.token}")
        req.add_header("Accept", "application/vnd.github+json")
        req.add_header("X-GitHub-Api-Version", "2022-11-28")
        req.add_header("User-Agent", "ai-bridge")
        if data is not None:
            req.add_header("Content-Type", "application/json")
        try:
            with urllib.request.urlopen(req, timeout=30, context=SSL_CONTEXT) as r:
                raw = r.read().decode()
                return json.loads(raw) if raw else None
        except urllib.error.HTTPError as e:
            try:
                msg = json.loads(e.read().decode()).get("message", "")
            except Exception:  # noqa: BLE001
                msg = ""
            raise GitHubError(f"GitHub replied {e.code}: {msg}") from None
        except urllib.error.URLError as e:
            reason = e.reason
            reason_text = str(reason)
            if isinstance(reason, ssl.SSLCertVerificationError) or "CERTIFICATE_VERIFY_FAILED" in reason_text:
                raise GitHubError(
                    "GitHub's TLS certificate could not be verified. Certificate checks are still enabled.\n\n"
                    "Click 'Repair SSL certificates' beside Connect GitHub, then try Connect GitHub again.\n"
                    "If repair cannot reach the certificate service, run this in the same Terminal/venv:\n"
                    f'  "{sys.executable}" -m pip install --upgrade certifi\n\n'
                    f"Python: {sys.executable}\nTrusted CA sources: {SSL_CA_DESCRIPTION}\n"
                    f"Original error: {reason_text}"
                ) from None
            raise GitHubError(f"Could not reach GitHub: {reason}") from None

    def fetch_file(self, path):
        q = urllib.parse.quote(path)
        ref = urllib.parse.quote(self.branch, safe="")
        d = self.gh("GET", f"/repos/{self.repo}/contents/{q}?ref={ref}")
        if isinstance(d, list) or d.get("encoding") != "base64":
            raise GitHubError(f"{path} is not a regular file that can be read.")
        return base64.b64decode(d["content"]).decode("utf-8", errors="replace"), d["sha"]

    def put_file(self, path, text, sha, message):
        body = {
            "message": message,
            "content": base64.b64encode(text.encode("utf-8")).decode(),
            "sha": sha,
            "branch": self.branch,
        }
        self.gh("PUT", f"/repos/{self.repo}/contents/{urllib.parse.quote(path)}", body)

    def put_binary_file(self, path, data, message):
        """Create/update a binary GitHub Contents file from raw bytes."""
        if not self.repo or not self.branch or not self.token:
            raise GitHubError("Connect GitHub before uploading generated images.")
        if not isinstance(data, (bytes, bytearray)) or not data:
            raise GitHubError(f"{path} is empty or is not binary data.")
        if len(data) > MAX_GITHUB_MEDIA_BYTES:
            raise GitHubError(f"{path} exceeds the {MAX_GITHUB_MEDIA_BYTES // (1024 * 1024)} MB image upload limit.")
        encoded_path = urllib.parse.quote(path, safe="/")
        body = {
            "message": message,
            "content": base64.b64encode(bytes(data)).decode("ascii"),
            "branch": self.branch,
        }
        # Contents API requires the current SHA only when replacing an existing file.
        branch_ref = urllib.parse.quote(self.branch, safe="")
        try:
            current = self.gh("GET", f"/repos/{self.repo}/contents/{encoded_path}?ref={branch_ref}")
            if isinstance(current, dict) and current.get("sha"):
                body["sha"] = current["sha"]
        except GitHubError as exc:
            if "404" not in str(exc):
                raise
        self.gh("PUT", f"/repos/{self.repo}/contents/{encoded_path}", body)

    def busy(self, msg):
        self.status(msg)
        self.config(cursor="watch")
        self.update_idletasks()

    def idle(self):
        self.config(cursor="")

    # ---------- UI ----------
    def build_ui(self):
        pad = {"padx": 10, "pady": 6}

        top = ttk.Frame(self)
        top.pack(fill="x", **pad)
        ttk.Label(top, text="Repository").grid(row=0, column=0, sticky="w")
        ttk.Label(top, text="Working branch").grid(row=0, column=1, sticky="w", padx=8)
        ttk.Label(top, text="GitHub token").grid(row=0, column=2, sticky="w", padx=8)
        ttk.Entry(top, textvariable=self.repo_var, width=30).grid(row=1, column=0, sticky="we")
        ttk.Entry(top, textvariable=self.branch_var, width=18).grid(row=1, column=1, sticky="we", padx=8)
        ttk.Entry(top, textvariable=self.token_var, width=30, show="*").grid(row=1, column=2, sticky="we", padx=8)
        ttk.Button(top, text="Connect GitHub", command=self.connect).grid(row=1, column=3, padx=(8, 0))
        ttk.Button(top, text="Open local VS Code folder", command=self.open_local_workspace).grid(row=1, column=4, padx=(8, 0))
        ttk.Button(top, text="Repair SSL certificates", command=self.repair_github_ssl).grid(row=1, column=5, padx=(8, 0))
        top.columnconfigure(0, weight=2)
        top.columnconfigure(2, weight=2)
        ttk.Label(
            top,
            text="Changes are committed to the working branch (created for you if missing), never straight to your main branch. "
            "GitHub mode keeps using branches. Local mode edits files in your selected VS Code folder and creates backups.",
        ).grid(row=2, column=0, columnspan=6, sticky="w", pady=(4, 0))

        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, **pad)

        # Tab: files
        t0 = ttk.Frame(self.nb)
        self.nb.add(t0, text="Files")
        row = ttk.Frame(t0)
        row.pack(fill="x", padx=10, pady=(10, 4))
        ttk.Label(row, text="Filter:").pack(side="left")
        ttk.Entry(row, textvariable=self.filter_var).pack(side="left", fill="x", expand=True, padx=8)
        ttk.Button(row, text="Select all files", command=self.select_all).pack(side="left")
        ttk.Button(row, text="Select none", command=self.select_none).pack(side="left", padx=(6, 0))
        box = ttk.Frame(t0)
        box.pack(fill="both", expand=True, padx=10)
        self.listbox = tk.Listbox(box, selectmode="extended", exportselection=False)
        sb = ttk.Scrollbar(box, command=self.listbox.yview)
        self.listbox.config(yscrollcommand=sb.set)
        for combo in ("<Command-a>", "<Control-a>"):
            self.listbox.bind(combo, lambda e: (self.select_all(), "break")[1])
        self.listbox.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        row = ttk.Frame(t0)
        row.pack(fill="x", padx=10, pady=10)
        ttk.Button(row, text="Load selected files", command=self.load_selected).pack(side="left")
        ttk.Button(row, text="Reload loaded files", command=self.reload).pack(side="left", padx=8)
        ttk.Button(row, text="Open branch in VS Code for the web", command=self.open_web_editor).pack(side="left")
        self.file_label = ttk.Label(row, text="")
        self.file_label.pack(side="left", padx=12)

        # Tab: ask — scrollable so the controls/status remain reachable on shorter displays.
        ask_tab = ttk.Frame(self.nb)
        self.nb.add(ask_tab, text="Ask")
        ask_canvas = tk.Canvas(ask_tab, highlightthickness=0, borderwidth=0)
        ask_scrollbar = ttk.Scrollbar(ask_tab, orient="vertical", command=ask_canvas.yview)
        ask_canvas.configure(yscrollcommand=ask_scrollbar.set)
        ask_canvas.pack(side="left", fill="both", expand=True)
        ask_scrollbar.pack(side="right", fill="y")
        t1 = ttk.Frame(ask_canvas)
        ask_window = ask_canvas.create_window((0, 0), window=t1, anchor="nw")
        t1.bind("<Configure>", lambda _e: ask_canvas.configure(scrollregion=ask_canvas.bbox("all")))
        ask_canvas.bind("<Configure>", lambda e: ask_canvas.itemconfigure(ask_window, width=e.width))
        def ask_mousewheel(event):
            # macOS sends small +/- deltas; Windows/Linux usually send multiples of 120.
            delta = -1 if event.delta > 0 else 1
            if abs(event.delta) >= 120:
                delta = int(-event.delta / 120)
            ask_canvas.yview_scroll(delta, "units")
            return "break"
        ask_canvas.bind("<MouseWheel>", ask_mousewheel)
        t1.bind("<MouseWheel>", ask_mousewheel)
        nav_row = ttk.Frame(t1)
        nav_row.pack(fill="x", padx=10, pady=(6, 0))
        ttk.Button(nav_row, text="↑ Scroll to top", command=lambda: ask_canvas.yview_moveto(0)).pack(side="left")
        ttk.Button(nav_row, text="↓ Scroll to bottom", command=lambda: ask_canvas.yview_moveto(1)).pack(side="left", padx=6)
        ttk.Label(t1, text="1. Describe the task").pack(anchor="w", padx=10, pady=(10, 4))
        self.question = scrolledtext.ScrolledText(t1, height=12, wrap="word", font="TkFixedFont")
        self.question.pack(fill="x", padx=10)

        # Non-code attachment picker: visible queue, type/size, remove individual files.
        attach_box = ttk.LabelFrame(t1, text="2. Reference files (optional)")
        attach_box.pack(fill="x", padx=10, pady=(6, 2))
        attach_top = ttk.Frame(attach_box)
        attach_top.pack(fill="x", padx=8, pady=(6, 3))
        ttk.Checkbutton(
            attach_top,
            text="Attach selected non-code files to each AI chat",
            variable=self.attach_noncode_var,
        ).pack(side="left", anchor="w")
        ttk.Button(attach_top, text="＋ Add files…", command=self.choose_noncode_attachments).pack(side="right")
        attach_body = ttk.Frame(attach_box)
        attach_body.pack(fill="x", padx=8, pady=(2, 4))
        self.attachment_tree = ttk.Treeview(
            attach_body, columns=("name", "kind", "size", "mode"), show="headings", height=5,
            selectmode="extended",
        )
        self.attachment_tree.heading("name", text="Selected file")
        self.attachment_tree.heading("kind", text="Type")
        self.attachment_tree.heading("size", text="Size")
        self.attachment_tree.heading("mode", text="How it will be sent")
        self.attachment_tree.column("name", width=280, stretch=True)
        self.attachment_tree.column("kind", width=105, stretch=False)
        self.attachment_tree.column("size", width=85, anchor="e", stretch=False)
        self.attachment_tree.column("mode", width=160, stretch=False)
        attach_scroll = ttk.Scrollbar(attach_body, orient="vertical", command=self.attachment_tree.yview)
        self.attachment_tree.configure(yscrollcommand=attach_scroll.set)
        self.attachment_tree.pack(side="left", fill="x", expand=True)
        attach_scroll.pack(side="right", fill="y")
        attach_controls = ttk.Frame(attach_box)
        attach_controls.pack(fill="x", padx=8, pady=(0, 6))
        self.attachment_label = ttk.Label(attach_controls, text="No files selected")
        self.attachment_label.pack(side="left")
        ttk.Button(attach_controls, text="Remove selected", command=self.remove_selected_attachments).pack(side="right")
        ttk.Button(attach_controls, text="Clear all files", command=self.clear_noncode_attachments).pack(side="right", padx=(0, 6))
        ttk.Label(
            attach_box,
            text="Code and text files are inserted into the prompt. Images, PDFs and other binary files use the website attachment control. Select rows above to remove individual files.",
            wraplength=900, justify="left",
        ).pack(anchor="w", padx=8, pady=(0, 7))

        row = ttk.Frame(t1)
        row.pack(fill="x", padx=10, pady=(10, 4))
        ttk.Button(row, text="▶ Run everything (open → send → collect)", command=lambda: self.prepare_browser_prompt("ask")).pack(side="left")
        ttk.Button(row, text="■ Cancel run", command=self.stop_browser_run).pack(side="left", padx=(6, 0))
        ttk.Button(row, text="Collect replies", command=self.collect_browser_replies).pack(side="left", padx=(8, 0))
        ttk.Button(row, text="Copy prompt", command=self.copy_ask).pack(side="left", padx=(8, 0))
        ttk.Checkbutton(row, text="Diagnostic log (metadata only)", variable=self.diagnostics_var,
                        command=self.toggle_diagnostics).pack(side="left", padx=(10, 0))
        ttk.Button(row, text="Export diagnostic .txt…", command=self.export_diagnostic_log).pack(side="left", padx=(6, 0))
        self.countdown_label = ttk.Label(
            t1, textvariable=self.countdown_var, anchor="w",
            font=("TkDefaultFont", 10, "bold"),
        )
        self.countdown_label.pack(fill="x", padx=10, pady=(4, 2))
        ttk.Label(t1, textvariable=self.timer_var, anchor="w").pack(fill="x", padx=10, pady=(0, 2))
        ttk.Label(
            t1,
            text="How it works: sign in once in the opened Chrome profile. After you press Start, AI Bridge waits 10 seconds with a visible countdown, then enters the prompt and submits it to ChatGPT, Gemini and DeepSeek. It collects text, code blocks and generated pictures when available. Attachment failures are reported separately and do not silently replace the prompt.",
            wraplength=900, justify="left",
        ).pack(anchor="w", padx=10, pady=(0, 2))
        ttk.Label(t1, textvariable=self.diagnostics_path_var, wraplength=900, justify="left").pack(
            anchor="w", padx=10, pady=(0, 6)
        )
        self.browser_site_vars = {ai: tk.StringVar(value="Not started") for ai in AIS}
        site_frame = ttk.LabelFrame(t1, text="Browser / website status")
        site_frame.pack(fill="x", padx=10, pady=(0, 10))
        status_tools = ttk.Frame(site_frame)
        status_tools.grid(row=0, column=0, columnspan=6, sticky="ew", padx=7, pady=(6, 3))
        ttk.Button(
            status_tools, text="Copy all website statuses", command=self.copy_website_statuses
        ).pack(side="left")
        ttk.Label(
            status_tools, text="Copies the full status text (including errors) so you can paste it into ChatGPT."
        ).pack(side="left", padx=9)
        for index, ai in enumerate(AIS):
            base_col = (index % 2) * 3
            grid_row = index // 2 + 1
            ttk.Label(site_frame, text=ai + ":").grid(
                row=grid_row, column=base_col, sticky="w", padx=(8, 3), pady=4
            )
            ttk.Label(site_frame, textvariable=self.browser_site_vars[ai], wraplength=340).grid(
                row=grid_row, column=base_col + 1, sticky="w", padx=(0, 5), pady=4
            )
            ttk.Button(
                site_frame, text="Copy", command=lambda name=ai: self.copy_website_status(name)
            ).grid(row=grid_row, column=base_col + 2, sticky="w", padx=(0, 12), pady=3)
        site_frame.columnconfigure(1, weight=1)
        site_frame.columnconfigure(4, weight=1)

        # Tab: compare and apply
        t2 = ttk.Frame(self.nb)
        self.nb.add(t2, text="Compare and apply")
        row = ttk.Frame(t2)
        row.pack(fill="x", padx=10, pady=(10, 4))
        ttk.Label(row, text="Reply from:").pack(side="left")
        self.radios = {}
        for ai in AIS:
            rb = ttk.Radiobutton(row, text=ai, value=ai, variable=self.ai_var, command=self.switch_ai)
            rb.pack(side="left", padx=8)
            self.radios[ai] = rb
        ttk.Button(row, text="Paste from clipboard", command=self.paste_reply).pack(side="left", padx=(16, 0))
        self.reply = scrolledtext.ScrolledText(t2, height=6, wrap="word", font="TkFixedFont")
        self.reply.pack(fill="x", padx=10, pady=(4, 0))
        self.reply.bind("<KeyRelease>", lambda e: self.process_reply())
        self.summary = ttk.Label(t2, text="")
        self.summary.pack(anchor="w", padx=10, pady=(8, 2))
        self.diff = scrolledtext.ScrolledText(t2, height=14, wrap="none", font="TkFixedFont", state="disabled")
        self.diff.pack(fill="both", expand=True, padx=10)
        self.diff.tag_config("add", background="#d9f2df", foreground="#12351c")
        self.diff.tag_config("del", background="#f7dcdc", foreground="#4a1414")
        self.diff.tag_config("hunk", foreground="#6b7280")
        self.diff.tag_config("head", font=("TkFixedFont", 10, "bold"))
        verify_row = ttk.Frame(t2)
        verify_row.pack(fill="x", padx=10, pady=(6, 2))
        ttk.Button(verify_row, text="Verify all & recommend best", command=self.verify_and_recommend).pack(side="left")
        self.verify_summary = ttk.Label(verify_row, text="Verification has not been run yet.")
        self.verify_summary.pack(side="left", padx=10)
        self.verify_details = scrolledtext.ScrolledText(t2, height=7, wrap="word", font="TkFixedFont")
        self.verify_details.pack(fill="x", padx=10, pady=(2, 4))
        self.verify_details.insert("1.0", "Collect replies from ChatGPT, Gemini and DeepSeek, then click Verify all & recommend best.\nStatic checks do not replace running your app's tests.")
        self.verify_details.configure(state="disabled")
        row = ttk.Frame(t2)
        row.pack(fill="x", padx=10, pady=10)
        self.save_btn = ttk.Button(row, text="Apply approved changes", command=self.save, state="disabled")
        self.save_btn.pack(side="left")
        self.undo_btn = ttk.Button(row, text="Undo last commit", command=self.undo, state="disabled")
        self.undo_btn.pack(side="left", padx=8)
        ttk.Button(row, text="Open branch in VS Code for the web", command=self.open_web_editor).pack(side="left", padx=8)

        # Tab: fix
        t3 = ttk.Frame(self.nb)
        self.nb.add(t3, text="Fix")
        ttk.Label(
            t3,
            text="Ran the code somewhere (for example a GitHub Codespace) and it failed? Paste the error or describe what is wrong:",
        ).pack(anchor="w", padx=10, pady=(10, 4))
        self.problem = scrolledtext.ScrolledText(t3, height=14, wrap="word", font="TkFixedFont")
        self.problem.pack(fill="both", expand=True, padx=10)
        row = ttk.Frame(t3)
        row.pack(fill="x", padx=10, pady=10)
        ttk.Button(row, text="▶ Run fix (open → send → collect)", command=lambda: self.prepare_browser_prompt("fix")).pack(side="left")
        ttk.Button(row, text="■ Cancel run", command=self.stop_browser_run).pack(side="left", padx=(8, 0))
        ttk.Button(row, text="Collect replies", command=self.collect_browser_replies).pack(side="left", padx=(8, 0))
        ttk.Button(row, text="Copy fix prompt", command=self.copy_fix).pack(side="left", padx=(8, 0))

        # Tab: independent browser responses.
        t4 = ttk.Frame(self.nb)
        self.nb.add(t4, text="Responses")
        self.response_panels = {}
        self.media_vars = {ai: tk.StringVar(value="No generated images captured yet") for ai in AIS}
        response_tools = ttk.Frame(t4)
        response_tools.grid(row=0, column=0, columnspan=2, sticky="ew", padx=7, pady=(7, 0))
        ttk.Button(response_tools, text="Copy all replies", command=self.copy_all_responses).pack(side="left")
        ttk.Button(response_tools, text="Save replies to .txt…", command=self.save_all_responses).pack(side="left", padx=7)
        ttk.Button(response_tools, text="Load selected reply into Compare", command=self.load_selected_response).pack(side="left")
        ttk.Button(response_tools, text="Export detected code files…", command=self.export_selected_code).pack(side="left", padx=7)
        ttk.Button(response_tools, text="Open results folder", command=self.open_results_folder).pack(side="left")
        self.image_upload_btn = ttk.Button(
            response_tools, text="Upload generated images to GitHub…",
            command=self.upload_generated_images_to_github,
        )
        self.image_upload_btn.pack(side="left", padx=7)
        ttk.Label(response_tools, text="Text/code can be copied or exported; real generated image files are saved separately.").pack(side="left", padx=8)
        for index, ai in enumerate(AIS):
            panel = ttk.LabelFrame(t4, text=ai)
            panel.grid(row=index // 2 + 1, column=index % 2, sticky="nsew", padx=7, pady=7)
            t4.rowconfigure(index // 2 + 1, weight=1)
            t4.columnconfigure(index % 2, weight=1)
            text_widget = scrolledtext.ScrolledText(panel, height=13, wrap="word", font="TkFixedFont")
            text_widget.pack(fill="both", expand=True, padx=5, pady=5)
            tools_row=ttk.Frame(panel)
            tools_row.pack(fill="x", padx=5, pady=(0,5))
            ttk.Button(tools_row, text=f"Copy {ai}",
                       command=lambda name=ai: self.copy_response(name)).pack(side="left")
            ttk.Label(tools_row, textvariable=self.media_vars[ai]).pack(side="left", padx=8)
            ttk.Button(tools_row, text="Open images", command=lambda name=ai: self.open_response_images(name)).pack(side="right")
            self.response_panels[ai] = text_widget

        # Browser mode is the default; no AI API keys are requested or stored.

        ttk.Label(self, textvariable=self.status_var, anchor="w").pack(fill="x", padx=10, pady=(0, 8))

    def ai_buttons(self, row):
        ttk.Label(row, text="then open:").pack(side="left", padx=(14, 4))
        for ai, url in AIS.items():
            ttk.Button(row, text=ai, command=lambda u=url: webbrowser.open(u)).pack(side="left", padx=2)
        ttk.Button(row, text="Open all 3 AI sites", command=self.open_all).pack(side="left", padx=(8, 0))

    def status(self, msg):
        self.status_var.set(msg)

    def website_status_text(self, ai=None):
        """Build a paste-ready status report without including prompts or file contents."""
        names = [ai] if ai else list(AIS)
        captured = datetime.now().astimezone().isoformat(timespec="seconds")
        lines = [
            "AI Bridge — Browser / Website status",
            f"Copied: {captured}",
            f"Application: {self.status_var.get().strip() or 'No application status'}",
        ]
        countdown = getattr(self, "countdown_var", None)
        if countdown is not None:
            lines.append(f"Countdown: {countdown.get().strip() or 'Not available'}")
        lines.append("")
        lines.append("Website statuses:")
        for name in names:
            value = self.browser_site_vars[name].get().strip() if name in self.browser_site_vars else ""
            lines.append(f"{name}: {value or 'No status yet'}")
        return "\n".join(lines)

    def copy_website_status(self, ai=None):
        """Copy one site's complete status text, even when its label is visually wrapped."""
        if ai is not None and ai not in AIS:
            return
        text = self.website_status_text(ai)
        try:
            self.clipboard_clear()
            self.clipboard_append(text)
            self.update_idletasks()
            label = f"{ai} website status" if ai else "all website statuses"
            self.status(f"Copied {label} to clipboard. Paste it into your message here.")
        except tk.TclError as exc:
            messagebox.showerror("Clipboard unavailable", f"Could not copy the website status: {exc}")

    def copy_website_statuses(self):
        """Copy ChatGPT, Gemini and DeepSeek status text in one paste-ready block."""
        self.copy_website_status(None)

    def close_app(self):
        self._ui_shutdown = True
        if self._ui_poll_after_id is not None:
            try:
                self.after_cancel(self._ui_poll_after_id)
            except tk.TclError:
                pass
            self._ui_poll_after_id = None
        if self.browser is not None:
            self.browser.close()
        self.destroy()

    def _browser_callback(self, event, payload):
        """Thread-safe bridge from CDP workers to the Tk main thread.

        Do not call any Tk/Tcl method here: this callback runs on whichever
        browser worker emitted the event. Calling ``after`` from that thread
        can crash some macOS Tcl/Tk builds with a segmentation fault.
        """
        if self._ui_shutdown:
            return
        try:
            self._ui_event_queue.put((event, payload))
        except Exception:
            # A closing window must never take down a browser worker.
            pass

    def _schedule_ui_event_drain(self):
        """Schedule queue polling. This method is called only on Tk's thread."""
        if self._ui_shutdown:
            return
        try:
            self._ui_poll_after_id = self.after(40, self._drain_ui_events)
        except tk.TclError:
            self._ui_poll_after_id = None

    def _drain_ui_events(self):
        """Apply queued browser events on the Tk main thread."""
        self._ui_poll_after_id = None
        if self._ui_shutdown:
            return
        processed = 0
        while processed < 200:
            try:
                event, payload = self._ui_event_queue.get_nowait()
            except queue.Empty:
                break
            try:
                self._handle_browser_event(event, payload)
            except tk.TclError:
                # The UI may be in the process of closing.
                if self._ui_shutdown:
                    return
            except Exception as exc:
                try:
                    self.status(f"UI event error ({event}): {type(exc).__name__}: {exc}")
                except tk.TclError:
                    return
            processed += 1
        self._schedule_ui_event_drain()

    @staticmethod
    def _format_size(size):
        size = float(size)
        for unit in ("B", "KB", "MB", "GB"):
            if size < 1024 or unit == "GB":
                return f"{size:.0f} {unit}" if unit == "B" else f"{size:.1f} {unit}"
            size /= 1024
        return f"{size:.1f} GB"

    @staticmethod
    def _attachment_kind(path):
        suffix = Path(path).suffix.lower().lstrip(".")
        mime = mimetypes.guess_type(str(path))[0] or "file"
        if mime.startswith("image/"):
            return "Image"
        if mime == "application/pdf":
            return "PDF"
        if mime.startswith("audio/"):
            return "Audio"
        if mime.startswith("video/"):
            return "Video"
        if "word" in mime or "document" in mime or suffix in {"doc", "docx", "odt"}:
            return "Document"
        if "spreadsheet" in mime or suffix in {"xls", "xlsx", "ods", "csv"}:
            return "Spreadsheet"
        if "presentation" in mime or suffix in {"ppt", "pptx", "odp"}:
            return "Presentation"
        return suffix.upper() if suffix else "File"

    def refresh_attachment_view(self):
        """Show every file queued for this request, including project files and uploads."""
        if not hasattr(self, "attachment_tree"):
            return
        for item in self.attachment_tree.get_children():
            self.attachment_tree.delete(item)

        queued = []
        for project_path in self.files:
            content = self.texts.get(project_path, "")
            size = self._format_size(len(content.encode("utf-8")))
            queued.append((f"project::{project_path}", Path(project_path).name,
                           "Project code", size, "Prompt text"))
        for path_text in self.prompt_code_files:
            path = Path(path_text)
            try:
                size = self._format_size(path.stat().st_size)
            except OSError:
                size = "Missing"
            queued.append((f"prompt::{path_text}", path.name, "Code / text", size, "Prompt text"))
        for path_text in self.attachments:
            path = Path(path_text)
            try:
                size = self._format_size(path.stat().st_size)
            except OSError:
                size = "Missing"
            queued.append((f"upload::{path_text}", path.name, self._attachment_kind(path_text), size, "Website upload"))

        for iid, name, kind, size, mode in queued:
            self.attachment_tree.insert("", "end", iid=iid, values=(name, kind, size, mode))
        project_count = len(self.files)
        prompt_count = len(self.prompt_code_files)
        upload_count = len(self.attachments)
        count = len(queued)
        if count:
            self.attachment_label.config(
                text=(f"{count} selected  ·  {project_count + prompt_count} in prompt  ·  "
                      f"{upload_count} website upload(s)")
            )
        else:
            self.attachment_label.config(text="No files selected — add files or load project files from the Files tab")

    def choose_noncode_attachments(self):
        filetypes = list(NON_CODE_FILETYPES) + [("All files (code/text goes in prompt)", "*.*")]
        chosen = filedialog.askopenfilenames(
            title="Add code, pictures, PDFs and other reference files",
            filetypes=filetypes,
        )
        if not chosen:
            return
        added_code, added_upload, rejected = [], [], []
        for value in chosen:
            path = Path(value).expanduser().resolve()
            if not path.is_file():
                rejected.append(path.name + " (not a regular file)")
                continue
            path_text = str(path)
            if is_code_or_text_file(path):
                try:
                    if path.stat().st_size > MAX_FILE_BYTES:
                        rejected.append(path.name + f" (text file exceeds {MAX_FILE_BYTES:,} byte prompt limit)")
                        continue
                    content = path.read_text(encoding="utf-8-sig")
                except (OSError, UnicodeError) as exc:
                    rejected.append(path.name + f" (could not read as UTF-8 text: {exc})")
                    continue
                self.prompt_code_files[path_text] = content
                # Never also upload the same file as binary.
                self.attachments = [item for item in self.attachments if item != path_text]
                added_code.append(path.name)
            else:
                if path_text not in self.attachments:
                    self.attachments.append(path_text)
                self.prompt_code_files.pop(path_text, None)
                added_upload.append(path.name)
        self.attach_noncode_var.set(True)
        self.refresh_attachment_view()
        notes = []
        if added_code:
            notes.append("Included in prompt as code/text:\n" + "\n".join(added_code))
        if added_upload:
            notes.append("Queued for website file upload:\n" + "\n".join(added_upload))
        if rejected:
            notes.append("Not added:\n" + "\n".join(rejected))
        if notes:
            messagebox.showinfo("Selected files", "\n\n".join(notes))

    def remove_selected_attachments(self):
        selected = set(self.attachment_tree.selection()) if hasattr(self, "attachment_tree") else set()
        if not selected:
            self.status("Select one or more rows in the file list, then click Remove selected.")
            return
        removed = 0
        for item in selected:
            if item.startswith("project::"):
                project_path = item[len("project::"):]
                if project_path in self.files:
                    self.files.remove(project_path)
                    self.texts.pop(project_path, None)
                    self.previous.pop(project_path, None)
                    removed += 1
            elif item.startswith("prompt::"):
                path = item[len("prompt::"):]
                if self.prompt_code_files.pop(path, None) is not None:
                    removed += 1
            elif item.startswith("upload::"):
                path = item[len("upload::"):]
                before = len(self.attachments)
                self.attachments = [value for value in self.attachments if value != path]
                removed += before - len(self.attachments)
        self.refresh_attachment_view()
        if hasattr(self, "file_label"):
            self.file_label.config(text=f"{len(self.files)} project file(s) loaded")
        self.status(f"Removed {removed} selected file(s) from this request. Your original files were not deleted.")

    def clear_noncode_attachments(self):
        count = len(self.files) + len(self.prompt_code_files) + len(self.attachments)
        self.attachments = []
        self.prompt_code_files = {}
        self.files = []
        self.texts = {}
        self.previous = {}
        self.refresh_attachment_view()
        if hasattr(self, "file_label"):
            self.file_label.config(text="")
        self.status(f"Cleared {count} file(s) from the current request. Files on disk/GitHub were not deleted.")

    def start_browser(self):
        if self.browser is None:
            self.browser = BrowserIntegration(self._browser_callback)
        self.browser.configure_diagnostics(self.diagnostics_var.get())
        self.status("Starting dedicated Chrome profile with CDP…")
        self.browser.start()

    def toggle_diagnostics(self):
        if self.browser is None:
            state = "enabled" if self.diagnostics_var.get() else "disabled"
            self.diagnostics_path_var.set(f"Diagnostics {state}; start browser sessions to create the log (metadata only).")
            return
        path = self.browser.configure_diagnostics(self.diagnostics_var.get())
        if path:
            self.diagnostics_path_var.set(f"Diagnostic log: {path} (prompt and file contents are not recorded)")
        else:
            self.diagnostics_path_var.set("Diagnostic logging is disabled.")

    def export_diagnostic_log(self):
        path = self.browser.diagnostic_path if self.browser is not None else None
        if not path or not Path(path).is_file():
            messagebox.showinfo("Diagnostic log", "Start browser sessions with Diagnostic log enabled, then reproduce the issue.")
            return
        destination = filedialog.asksaveasfilename(
            title="Export AI Bridge diagnostic log",
            defaultextension=".txt",
            initialfile=Path(path).name,
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
        )
        if not destination:
            return
        try:
            shutil.copy2(path, destination)
            self.status(f"Diagnostic log exported: {destination}")
            messagebox.showinfo(
                "Diagnostic log exported",
                "Attach the exported .txt file here so I can inspect the failure steps. "
                "The log excludes prompt text, source-file contents, passwords and browser cookies."
            )
        except OSError as exc:
            messagebox.showerror("Could not export diagnostic log", str(exc))

    def prepare_browser_prompt(self, kind):
        if self.browser is None or not getattr(self.browser, "started", False):
            # One-button flow: open the browser sessions first; the run continues
            # automatically from the "ready" event.
            self._pending_run_kind = kind
            self.status("Opening the browser sessions; the prompt will be sent automatically once the tabs are ready…")
            self.start_browser()
            return
        if self.attachments and not self.attach_noncode_var.get() and not self.files and not self.prompt_code_files:
            messagebox.showwarning(
                "Attachments are turned off",
                "You selected image/document files, but website attachment mode is disabled. "
                "Turn on the attachment option or remove those files before sending."
            )
            return
        fallback_prompt = self.build_prompt(kind)
        if not fallback_prompt:
            return
        # Keep the loaded source in fenced code blocks inside the prompt. This avoids
        # browser attachment-size/type limits and ensures every model sees identical text.
        prompt = fallback_prompt
        prompt_chars = len(prompt)
        if prompt_chars > 120_000:
            proceed = messagebox.askyesno(
                "Large prompt",
                f"This request contains {prompt_chars:,} characters of source code and instructions. "
                "Some AI websites may reject very long prompts. Send it anyway?",
            )
            if not proceed:
                return
        self.browser.configure_diagnostics(self.diagnostics_var.get())
        self.countdown_var.set("⏳ 10s  |  Websites are open — preparing to send")
        self.browser_prompt_kind = kind
        self.replies = {ai: "" for ai in AIS}
        self.proposals = {ai: {} for ai in AIS}
        self.analysis = {}
        self.api_errors = {}
        self.save_btn.config(state="disabled")
        for ai in AIS:
            self.radios[ai].config(text=ai)
        if hasattr(self, "response_panels"):
            for panel in self.response_panels.values():
                panel.delete("1.0", "end")
        for ai in AIS:
            if hasattr(self, "browser_site_vars"):
                self.browser_site_vars[ai].set("Waiting for submission…")
        active_attachments = list(self.attachments) if self.attach_noncode_var.get() else []
        self.response_media = {ai: [] for ai in AIS}
        self.result_dir = Path.home() / "Downloads" / "AI Bridge Results" / datetime.now().strftime("%Y%m%d_%H%M%S")
        if self.browser is not None:
            self.browser.set_result_dir(self.result_dir)
        if hasattr(self, "media_vars"):
            for ai in AIS:
                self.media_vars[ai].set("No generated images captured yet")
        if active_attachments:
            self.status(
                f"Phase A: sending project code in the prompt and attaching {len(active_attachments)} "
                "selected non-code file(s) through each site's upload control…"
            )
        else:
            self.status("Phase A: sending project files as code in the prompt to ChatGPT, Gemini and DeepSeek…")
        self._start_run_timer()
        self.browser.prepare(
            prompt, fallback_prompt=fallback_prompt, attachments=active_attachments,
        )

    # ---- built-in run timer -------------------------------------------------
    def _start_run_timer(self):
        self._run_t0 = time.monotonic()
        self._site_done = {}
        self._run_timer_active = True
        self._tick_run_timer()

    def _tick_run_timer(self):
        if not self._run_timer_active or self._run_t0 is None:
            return
        elapsed = int(time.monotonic() - self._run_t0)
        parts = []
        for ai in AIS:
            done = self._site_done.get(ai)
            parts.append(f"{ai} {done}" if done else f"{ai} …")
        self.timer_var.set(f"⏱ {elapsed // 60:02d}:{elapsed % 60:02d}  |  limit {BrowserIntegration.RESPONSE_TIMEOUT_SECONDS}s per site  |  " + "  ·  ".join(parts))
        self.after(250, self._tick_run_timer)

    def _stop_run_timer(self, label="finished"):
        if self._run_t0 is not None:
            elapsed = int(time.monotonic() - self._run_t0)
            self.timer_var.set(f"⏱ {elapsed // 60:02d}:{elapsed % 60:02d} total ({label})  |  " + "  ·  ".join(
                f"{ai} {self._site_done.get(ai, 'no reply')}" for ai in AIS))
        self._run_timer_active = False

    def stop_browser_run(self):
        self._stop_run_timer("stopped")
        if self.browser is None:
            self.status("No browser automation is running.")
            return
        self.browser.stop()
        self.status("AI Bridge cancelled. Website generations are still running; use Collect replies when they finish. To stop a model, use that website's own Stop button.")

    def collect_browser_replies(self):
        if self.browser is None:
            messagebox.showinfo("Start browser first", "Click Start browser sessions first.")
            return
        if getattr(self.browser, "_collecting", False):
            self.status("Replies are already being collected — please wait (timer above shows progress).")
            return
        self.status("Retrying response collection for previously submitted sites; prompts will not be submitted again.")
        self.browser._diag("SYSTEM", "User requested response collection retry")
        self._start_run_timer()
        self.browser.collect()

    def _bring_app_to_front(self):
        """Return focus to the AI Bridge window (runs on the Tk thread only)."""
        try:
            self.deiconify()
            self.lift()
            self.attributes("-topmost", True)
            self.after(300, lambda: self.attributes("-topmost", False))
            self.focus_force()
        except tk.TclError:
            pass

    def _handle_browser_event(self, event, payload):
        if event == "site_status" and isinstance(payload, dict) and self._run_t0 is not None:
            status_text = str(payload.get("status", ""))
            if status_text.startswith("Response retrieved") or status_text.startswith("Collection failed"):
                done_at = int(time.monotonic() - self._run_t0)
                mark = "✓" if status_text.startswith("Response retrieved") else "✗"
                self._site_done[payload.get("ai")] = f"{mark} {done_at}s"
        if event == "focus_app":
            self._bring_app_to_front()
        elif event == "ssl_repaired":
            self._ssl_repair_running = False
            message = str(payload.get("message", "SSL certificate repair finished."))
            self.status(message)
            if payload.get("ok"):
                messagebox.showinfo("GitHub SSL", message + "\n\nYou can now click Connect GitHub.")
            else:
                messagebox.showerror("GitHub SSL", message)
        elif event == "diagnostics":
            path = payload.get("path") or ""
            if payload.get("enabled") and path:
                self.diagnostics_path_var.set(f"Diagnostic log: {path} (prompt and file contents are not recorded)")
            elif path:
                self.diagnostics_path_var.set(f"Diagnostic logging disabled. Existing log: {path}")
            else:
                self.diagnostics_path_var.set("Diagnostic logging is disabled.")
        elif event == "ready":
            self.status(
                "Dedicated Google Chrome profile opened. Sign in manually to ChatGPT, Gemini and DeepSeek if needed. "
                f"Profile: {payload.get('profile', '')}"
            )
            pending_kind = getattr(self, "_pending_run_kind", None)
            if pending_kind:
                self._pending_run_kind = None
                self.after(800, lambda k=pending_kind: self.prepare_browser_prompt(k))
        elif event == "prepared":
            self.status("Prompt submitted to the browser tabs.")
        elif event == "phase":
            self.status(str(payload))
        elif event == "countdown":
            if isinstance(payload, dict):
                remaining = int(payload.get("remaining", 0) or 0)
                message = str(payload.get("message", ""))
                if remaining > 0:
                    self.countdown_var.set(f"⏳ {remaining:02d}s  |  {message}")
                    self.status(f"Pre-send cooldown: {remaining} seconds remaining. No text has been entered yet.")
                else:
                    self.countdown_var.set(message or "Ready")
                    self.status(message or "Cooldown complete.")
            else:
                self.countdown_var.set(str(payload))
        elif event == "site_status":
            ai = payload.get("ai")
            if ai in getattr(self, "browser_site_vars", {}):
                self.browser_site_vars[ai].set(payload.get("status", ""))
        elif event == "manual_collect":
            self.status("Manual collection requested.")
        elif event == "site_errors":
            for ai, detail in payload.items():
                self.api_errors[ai] = detail
        elif event == "collected":
            self._stop_run_timer("finished")
            self.response_media = payload.get("_media", self.response_media) if isinstance(payload, dict) else self.response_media
            if hasattr(self, "media_vars"):
                for ai in AIS:
                    media = self.response_media.get(ai, [])
                    saved = [item for item in media if item.get("path")]
                    failed = [item for item in media if item.get("error")]
                    label = f"{len(saved)} image(s) saved" if saved else "No generated images captured"
                    if failed:
                        label += f"; {len(failed)} could not be exported"
                    self.media_vars[ai].set(label)
            received = []
            missing = []
            errors = payload.get("_errors", {}) if isinstance(payload, dict) else {}
            for ai, reply in payload.items():
                if ai not in AIS:
                    continue
                if isinstance(reply, str) and reply.strip():
                    self.replies[ai] = reply
                    self.api_errors.pop(ai, None)
                    if hasattr(self, "response_panels") and ai in self.response_panels:
                        panel = self.response_panels[ai]
                        panel.delete("1.0", "end")
                        panel.insert("1.0", reply)
                    self.analyze(ai)
                    received.append(ai)
                else:
                    missing.append(ai)
            self.api_errors.update(errors)
            missing = [ai for ai in AIS if ai not in received]
            if hasattr(self, "response_panels"):
                for ai in missing:
                    panel = self.response_panels[ai]
                    panel.delete("1.0", "end")
                    panel.insert("1.0", "Not retrieved. " + errors.get(ai, "No successful submission/response was received."))
            if received:
                chosen = next((ai for ai in AIS if ai in received), received[0])
                self.shown_ai = chosen
                self.ai_var.set(chosen)
                self.reply.delete("1.0", "end")
                self.reply.insert("1.0", self.replies[chosen])
                self.render(chosen)
                self.nb.select(4)
            note = "Collected: " + (", ".join(received) if received else "none")
            if missing:
                details = "; ".join(f"{ai}: {errors.get(ai, 'no response')}" for ai in missing)
                note += ". Missing: " + details + ". You can submit manually if needed, then click Collect replies."
            self.status(note)
            if missing:
                messagebox.showinfo("Response collection", note)
        elif event == "error":
            self._pending_run_kind = None
            self.status(str(payload))
            messagebox.showerror("Browser integration", str(payload))
        elif event == "images_uploaded":
            self._image_upload_running = False
            if hasattr(self, "image_upload_btn"):
                self.image_upload_btn.config(state="normal")
            uploaded = payload.get("uploaded", []) if isinstance(payload, dict) else []
            errors = payload.get("errors", []) if isinstance(payload, dict) else []
            if uploaded:
                self.status(f"Uploaded {len(uploaded)} generated image(s) to GitHub branch {self.branch}.")
            else:
                self.status("No generated images were uploaded.")
            details = []
            if uploaded:
                details.append("Uploaded:\n" + "\n".join(uploaded))
            if errors:
                details.append("Could not upload:\n" + "\n".join(errors))
            if details:
                messagebox.showinfo("GitHub image upload", "\n\n".join(details))
        elif event == "stopped":
            self.status("AI Bridge automation cancelled. Website generations were left running so replies are not cut short. Use Collect replies when they finish.")
        elif event == "closed":
            self.status("Browser sessions closed.")

    def _response_text(self, ai):
        widget = self.response_panels.get(ai)
        if widget is not None:
            text = widget.get("1.0", "end-1c").strip()
            if text and not text.startswith("Not retrieved."):
                return text
        return self.replies.get(ai, "").strip()

    def copy_response(self, ai):
        text = self._response_text(ai)
        if text:
            self.to_clipboard(text, f"{ai} response copied to clipboard. Paste it wherever you need it.")
        else:
            self.status(f"No response is available from {ai} yet.")

    def copy_all_responses(self):
        sections = []
        for ai in AIS:
            text = self._response_text(ai)
            if text:
                sections.append(f"===== {ai} =====\n{text}")
        if not sections:
            self.status("No AI replies are available to copy yet.")
            return
        combined = "\n\n".join(sections)
        self.to_clipboard(combined, "All available AI replies copied. Paste them into a message to send them back here.")

    def save_all_responses(self):
        sections = []
        for ai in AIS:
            text = self._response_text(ai)
            if text:
                sections.append(f"===== {ai} =====\n{text}")
        if not sections:
            self.status("No AI replies are available to save yet.")
            return
        path = filedialog.asksaveasfilename(
            title="Save collected AI replies", defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("Markdown files", "*.md"), ("All files", "*.*")],
            initialfile=f"ai_bridge_replies_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt",
        )
        if not path:
            return
        try:
            Path(path).write_text("\n\n".join(sections) + "\n", encoding="utf-8")
            self.status(f"Saved collected replies to {path}")
            messagebox.showinfo("Replies saved", f"Your collected AI replies were saved to:\n{path}")
        except OSError as exc:
            messagebox.showerror("Could not save replies", str(exc))

    def open_response_images(self, ai=None):
        ai = ai or self.ai_var.get()
        items = self.response_media.get(ai, [])
        paths = [Path(item["path"]) for item in items if item.get("path")]
        if not paths:
            self.status(f"No downloadable generated images were captured for {ai}.")
            return
        folder = paths[0].parent
        try:
            if sys.platform == "darwin":
                subprocess.Popen(["open", str(folder)])
            elif os.name == "nt":
                os.startfile(str(folder))
            else:
                subprocess.Popen(["xdg-open", str(folder)])
            self.status(f"Opened {ai} image results: {folder}")
        except Exception as exc:
            messagebox.showerror("Could not open image folder", str(exc))

    def upload_generated_images_to_github(self):
        """Upload saved generated image binaries to the currently connected GitHub branch."""
        if self._image_upload_running:
            self.status("Generated image upload is already running.")
            return
        if not self.repo or not self.branch or not self.token:
            messagebox.showinfo(
                "Connect GitHub first",
                "Connect to a GitHub repository with write access before uploading generated images."
            )
            return
        items = []
        for ai in AIS:
            for item in self.response_media.get(ai, []):
                raw_path = item.get("path")
                if raw_path:
                    path = Path(raw_path).expanduser()
                    if path.is_file():
                        items.append((ai, path))
        if not items:
            messagebox.showinfo(
                "No generated images",
                "No downloaded generated image files are available yet. Collect an AI image response first."
            )
            return
        oversized = [path.name for _, path in items if path.stat().st_size > MAX_GITHUB_MEDIA_BYTES]
        valid = [(ai, path) for ai, path in items if path.stat().st_size <= MAX_GITHUB_MEDIA_BYTES]
        if not valid:
            messagebox.showwarning(
                "Images too large",
                f"GitHub image uploads are limited to {MAX_GITHUB_MEDIA_BYTES // (1024 * 1024)} MB per file.\n"
                + "\n".join(oversized)
            )
            return
        estimate = sum(path.stat().st_size for _, path in valid)
        names = "\n".join(f"{ai}: {path.name}" for ai, path in valid)
        warning = ("\n\nSkipped files over the size limit: " + ", ".join(oversized)) if oversized else ""
        confirmed = messagebox.askyesno(
            "Upload generated images to GitHub?",
            f"Upload {len(valid)} real image file(s) ({self._format_size(estimate)}) to\n"
            f"{self.repo} / {self.branch}\n\n"
            f"Destination: AI_Bridge_Images/<AI>/\n\n{names}{warning}\n\nContinue?"
        )
        if not confirmed:
            return
        self._image_upload_running = True
        if hasattr(self, "image_upload_btn"):
            self.image_upload_btn.config(state="disabled")
        self.status(f"Uploading {len(valid)} generated image(s) to GitHub branch {self.branch}…")

        def worker():
            uploaded, errors = [], []
            for ai, path in valid:
                try:
                    data = path.read_bytes()
                    if not data:
                        raise GitHubError("Image file is empty.")
                    relative = f"AI_Bridge_Images/{ai}/{path.name}"
                    self.put_binary_file(
                        relative, data,
                        f"AI Bridge: add generated image from {ai} ({path.name})"
                    )
                    uploaded.append(relative)
                except Exception as exc:
                    errors.append(f"{ai} / {path.name}: {type(exc).__name__}: {exc}")
            if oversized:
                errors.append("Skipped oversized image(s): " + ", ".join(oversized))
            self._browser_callback("images_uploaded", {"uploaded": uploaded, "errors": errors})

        threading.Thread(target=worker, daemon=True, name="ai-bridge-github-image-upload").start()

    def export_selected_code(self):
        ai = self.ai_var.get()
        proposal = self.proposals.get(ai, {})
        if not proposal:
            self.status(f"No complete file blocks were detected in {ai}'s response. Save the full reply as text instead.")
            return
        folder = filedialog.askdirectory(title=f"Choose where to export {ai}'s proposed code files")
        if not folder:
            return
        root = Path(folder).resolve()
        written = []
        try:
            for relative, content in proposal.items():
                target = (root / relative).resolve()
                if target != root and root not in target.parents:
                    raise ValueError(f"Unsafe output path in model reply: {relative}")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(content, encoding="utf-8")
                written.append(str(target))
        except Exception as exc:
            messagebox.showerror("Code export failed", str(exc))
            return
        self.status(f"Exported {len(written)} proposed code file(s) to {root}")
        messagebox.showinfo("Code exported", "\n".join(written))

    def open_results_folder(self):
        folder = Path(self.result_dir) if self.result_dir else None
        if folder is None or not folder.exists():
            self.status("No AI Bridge result folder exists yet. Collect a reply first.")
            return
        try:
            if sys.platform == "darwin":
                subprocess.Popen(["open", str(folder)])
            elif os.name == "nt":
                os.startfile(str(folder))
            else:
                subprocess.Popen(["xdg-open", str(folder)])
        except Exception as exc:
            messagebox.showerror("Could not open results folder", str(exc))

    def load_selected_response(self):
        ai = self.ai_var.get() if hasattr(self, "ai_var") else self.shown_ai
        text = self._response_text(ai)
        if not text:
            self.status(f"No collected reply from {ai} is available yet.")
            return
        self.shown_ai = ai
        self.replies[ai] = text
        self.reply.delete("1.0", "end")
        self.reply.insert("1.0", text)
        self.nb.select(2)
        self.render(ai)
        self.status(f"Loaded {ai}'s reply into Compare and apply. Review it before applying any changes.")

    def open_all(self):
        if self.browser is not None:
            self.browser.start()
        else:
            self.start_browser()

    def open_web_editor(self):
        if not self.repo:
            messagebox.showinfo("GitHub not connected", "Connect to GitHub first to open a remote branch editor.")
            return
        webbrowser.open(f"https://github.dev/{self.repo}/tree/{urllib.parse.quote(self.branch, safe='/')}")

    # ---------- Local VS Code workspace ----------
    IGNORED_DIRS = {
        ".git", ".hg", ".svn", "node_modules", "__pycache__", ".venv", "venv",
        "env", ".mypy_cache", ".pytest_cache", ".next", ".nuxt", "dist",
        "build", ".idea", ".vscode-server", ".ai_bridge_backups",
    }

    def open_local_workspace(self):
        folder = filedialog.askdirectory(title="Select your local VS Code project folder")
        if not folder:
            return
        root = Path(folder).expanduser().resolve()
        if not root.is_dir():
            messagebox.showerror("Invalid folder", "Please select an existing project folder.")
            return
        self.local_root = root
        self.repo = ""
        self.branch = ""
        self.token = ""
        self.repo_var.set("")
        self.branch_var.set("")
        self.token_var.set("")
        self.files = []
        self.texts = {}
        self.previous = {}
        self.proposals = {a: {} for a in AIS}
        self.refresh_attachment_view()
        self.undo_btn.config(state="disabled")
        self.all_paths = self.scan_local_workspace()
        self.apply_filter()
        self.status(f"Local workspace opened: {root} — select files and click Load selected files.")
        self.nb.select(0)

    def scan_local_workspace(self):
        paths = []
        root = self.local_root
        if not root:
            return paths
        for current, dirs, files in os.walk(root, followlinks=False):
            dirs[:] = [
                d for d in dirs
                if d not in self.IGNORED_DIRS
                and not (Path(current) / d).is_symlink()
            ]
            for filename in files:
                path = Path(current) / filename
                if path.is_symlink() or filename.lower().endswith(BINARY_EXT):
                    continue
                try:
                    if path.stat().st_size > MAX_FILE_BYTES:
                        continue
                    rel = path.relative_to(root).as_posix()
                    paths.append(rel)
                except (OSError, ValueError):
                    continue
        return sorted(paths)

    def local_path(self, relative_path):
        if not self.local_root:
            raise GitHubError("No local workspace is open.")
        root = self.local_root.resolve()
        target = (root / relative_path).resolve()
        if target != root and root not in target.parents:
            raise GitHubError("Blocked an unsafe path outside the selected workspace.")
        return target

    def read_local_file(self, relative_path):
        target = self.local_path(relative_path)
        if not target.is_file() or target.is_symlink():
            raise GitHubError(f"{relative_path} is not a regular local file.")
        if target.stat().st_size > MAX_FILE_BYTES:
            raise GitHubError(f"{relative_path} is larger than the supported file size.")
        try:
            return target.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            raise GitHubError(f"{relative_path} is not a UTF-8 text file.") from None
        except OSError as e:
            raise GitHubError(f"Could not read {relative_path}: {e}") from None

    def write_local_file(self, relative_path, content):
        target = self.local_path(relative_path)
        if target.is_symlink():
            raise GitHubError(f"Refusing to overwrite a symbolic link: {relative_path}")
        target.parent.mkdir(parents=True, exist_ok=True)
        backup_root = self.local_root / ".ai_bridge_backups"
        backup_root.mkdir(exist_ok=True)
        stamp = datetime.now().strftime("%Y%m%d-%H%M%S-%f")
        backup = backup_root / (relative_path.replace("/", "__") + "." + stamp + ".bak")
        if target.exists():
            shutil.copy2(target, backup)
        # Atomic replacement helps avoid leaving a half-written source file.
        fd, temp_name = tempfile.mkstemp(prefix=".ai-bridge-", dir=str(target.parent))
        try:
            with os.fdopen(fd, "w", encoding="utf-8", newline="") as handle:
                handle.write(content)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp_name, target)
        except Exception:
            try:
                os.unlink(temp_name)
            except OSError:
                pass
            raise

    # ---------- Connect and load ----------
    def repair_github_ssl(self):
        """Update certifi for this exact Python interpreter and verify GitHub TLS."""
        if self._ssl_repair_running:
            self.status("SSL certificate repair is already running...")
            return
        self._ssl_repair_running = True
        self.status("Updating certifi for this Python environment and checking GitHub TLS...")

        def worker():
            try:
                proc = subprocess.run(
                    [sys.executable, "-m", "pip", "install", "--upgrade", "certifi"],
                    capture_output=True, text=True, timeout=180,
                )
                if proc.returncode != 0:
                    detail = (proc.stderr or proc.stdout or "pip did not provide details").strip()
                    raise RuntimeError(
                        "Could not update certifi using the active Python.\n"
                        f"Command: {sys.executable} -m pip install --upgrade certifi\n"
                        f"Details: {detail[-1800:]}"
                    )
                # Reload certifi after pip has updated the package in this venv.
                import importlib
                try:
                    import certifi
                    importlib.reload(certifi)
                except ImportError as exc:
                    raise RuntimeError("certifi is still unavailable after installation.") from exc
                context, sources = build_ssl_context()
                # Test the public API root (no token needed) to confirm the TLS
                # chain is trusted before telling the user the repair succeeded.
                test_req = urllib.request.Request(API + "/", headers={"User-Agent": "ai-bridge"})
                with urllib.request.urlopen(test_req, timeout=25, context=context) as response:
                    status_code = getattr(response, "status", 200)
                    response.read(128)
                if status_code < 200 or status_code >= 500:
                    raise RuntimeError(f"GitHub TLS test returned HTTP {status_code}.")
                global SSL_CONTEXT, SSL_CA_DESCRIPTION
                SSL_CONTEXT = context
                SSL_CA_DESCRIPTION = sources
                self._browser_callback("ssl_repaired", {
                    "ok": True,
                    "message": f"GitHub TLS verified successfully. Trusted CA sources: {sources}",
                })
            except Exception as exc:  # noqa: BLE001
                self._browser_callback("ssl_repaired", {
                    "ok": False,
                    "message": f"SSL repair failed: {type(exc).__name__}: {exc}",
                })

        threading.Thread(target=worker, daemon=True, name="ai-bridge-ssl-repair").start()

    def connect(self):
        try:
            self.local_root = None  # Switching to GitHub mode must not keep the local-workspace target.
            self.repo = normalize_repo(self.repo_var.get())
            self.branch = self.branch_var.get().strip() or "ai-bridge"
            self.token = self.token_var.get().strip()
            if not self.token:
                raise GitHubError("Paste a GitHub token first.")
            self.busy("Connecting...")
            info = self.gh("GET", f"/repos/{self.repo}")
            if info.get("permissions") and not info["permissions"].get("push"):
                raise GitHubError("This token cannot write to that repository.")
            default = info["default_branch"]
            bref = urllib.parse.quote(self.branch, safe="/")
            try:
                ref = self.gh("GET", f"/repos/{self.repo}/git/ref/heads/{bref}")
            except GitHubError as e:
                if "404" not in str(e):
                    raise
                if not messagebox.askyesno(
                    "Create branch?",
                    f"The branch '{self.branch}' does not exist.\nCreate it from '{default}'? "
                    "Your changes will be committed there, not to your main branch.",
                ):
                    self.status("Cancelled.")
                    return
                base = self.gh("GET", f"/repos/{self.repo}/git/ref/heads/{urllib.parse.quote(default, safe='/')}")
                ref = self.gh(
                    "POST", f"/repos/{self.repo}/git/refs",
                    {"ref": f"refs/heads/{self.branch}", "sha": base["object"]["sha"]},
                )
            tree = self.gh("GET", f"/repos/{self.repo}/git/trees/{ref['object']['sha']}?recursive=1")
            self.all_paths = sorted(
                t["path"] for t in tree["tree"] if t["type"] == "blob"
                and t.get("size", 0) < MAX_FILE_BYTES
                and not t["path"].lower().endswith(BINARY_EXT)
            )
            self.apply_filter()
            note = " (very large repo: the list is incomplete)" if tree.get("truncated") else ""
            self.status(f"Connected to {self.repo} on branch {self.branch}. Select files and click Load.{note}")
            self.nb.select(0)
        except GitHubError as e:
            self.status(str(e))
            messagebox.showerror("Could not connect", str(e))
        finally:
            self.idle()

    def apply_filter(self):
        needle = self.filter_var.get().strip().lower()
        self.listbox.delete(0, "end")
        for p in self.all_paths:
            if needle in p.lower():
                self.listbox.insert("end", p)

    def select_all(self):
        self.listbox.select_set(0, "end")
        self.status(f"Selected {self.listbox.size()} file(s). Click 'Load selected files'.")

    def select_none(self):
        self.listbox.select_clear(0, "end")

    def copy_and_open(self, kind):
        prompt = self.build_prompt(kind)
        if prompt:
            self.to_clipboard(prompt, "Prompt copied and the chats are opening. Click into each chat's message box and press Ctrl+V (Cmd+V on Mac).")
            self.open_all()

    def load_selected(self):
        if not self.repo and not self.local_root:
            messagebox.showinfo("No workspace", "Open a local folder or connect to GitHub first.")
            return
        picked = [self.listbox.get(i) for i in self.listbox.curselection()]
        if not picked:
            self.status("Select one or more files in the list first.")
            return
        try:
            self.busy("Loading files...")
            self.texts = ({p: self.read_local_file(p) for p in picked} if self.local_root
                          else {p: self.fetch_file(p)[0] for p in picked})
        except GitHubError as e:
            self.status(str(e))
            messagebox.showerror("Could not load files", str(e))
            return
        finally:
            self.idle()
        self.files = picked
        self.refresh_attachment_view()
        self.previous = {}
        self.undo_btn.config(state="disabled")
        total = sum(len(normalize(t).splitlines()) for t in self.texts.values())
        self.file_label.config(text=f"{len(picked)} file(s), {total} lines loaded")
        self.status(f"Loaded {len(picked)} file(s) from {'local workspace' if self.local_root else 'GitHub'}.")
        chars = sum(len(t) for t in self.texts.values())
        if chars > WARN_CHARS:
            messagebox.showwarning(
                "Large selection",
                f"These files add up to about {chars:,} characters. Some chat services may refuse or cut off a prompt this big. "
                "Consider loading fewer files at a time.",
            )
        self.process_reply()
        self.nb.select(1)

    def reload(self):
        if not self.files:
            self.status("Load some files first.")
            return
        try:
            self.busy("Reloading...")
            self.texts = ({p: self.read_local_file(p) for p in self.files} if self.local_root
                          else {p: self.fetch_file(p)[0] for p in self.files})
        except GitHubError as e:
            self.status(str(e))
            return
        finally:
            self.idle()
        self.process_reply()
        self.refresh_attachment_view()
        self.status("Reloaded the selected files.")

    # ---------- Prompts ----------
    def to_clipboard(self, text, msg):
        self.clipboard_clear()
        self.clipboard_append(text)
        self.update()
        self.status(msg)

    def files_block(self):
        return "\n\n".join(f"File: {p}\n{code_block(self.texts[p])}" for p in self.files)

    def refresh_texts(self):
        try:
            self.busy("Refreshing selected files...")
            self.texts = ({p: self.read_local_file(p) for p in self.files} if self.local_root
                          else {p: self.fetch_file(p)[0] for p in self.files})
            return True
        except GitHubError as e:
            self.status(str(e))
            return False
        finally:
            self.idle()

    def build_prompt(self, kind):
        """kind is 'ask' or 'fix'. Returns the prompt text, or None if something is missing."""
        if not self.files and not self.prompt_code_files and not self.attachments:
            messagebox.showinfo(
                "No reference files",
                "Load project files, add source/text files, or attach a picture/document first."
            )
            return None
        if kind == "ask":
            q = self.question.get("1.0", "end").strip()
            if not q:
                self.status("Type your question first.")
                return None
        else:
            q = self.problem.get("1.0", "end").strip()
            if not q:
                self.status("Paste the error or describe the problem first.")
                return None
        if not self.refresh_texts():
            return None
        # Re-read queued prompt-code files so the prompt uses the latest saved contents.
        extra_blocks = []
        for path_text in list(self.prompt_code_files):
            path = Path(path_text)
            try:
                if not path.is_file():
                    raise OSError("file no longer exists")
                if path.stat().st_size > MAX_FILE_BYTES:
                    raise OSError(f"file exceeds {MAX_FILE_BYTES:,} byte limit")
                content = path.read_text(encoding="utf-8-sig")
                self.prompt_code_files[path_text] = content
                extra_blocks.append(f"File: reference/{path.name}\n{code_block(content)}")
            except (OSError, UnicodeError) as exc:
                messagebox.showerror("Could not include selected source file", f"{path.name}: {exc}")
                return None
        project_block = self.files_block()
        if not project_block:
            project_block = "(No project source files selected.)"
        if extra_blocks:
            project_block = (project_block + "\n\n" if project_block else "") + (
                "Additional source/text files selected in the Ask tab (included as text, not uploaded):\n\n"
                + "\n\n".join(extra_blocks)
            )
        image_request = bool(re.search(
            r"\b(?:generate|create|draw|render|make|design)\b.{0,55}\b(?:image|picture|illustration|artwork|photo|graphic)\b|"
            r"\b(?:image|picture|illustration|artwork|photo|graphic)\b.{0,45}\b(?:generate|create|draw|render|make)\b",
            q, re.I | re.S,
        ))
        image_rules = (
            "\n\nIMAGE OUTPUT REQUIREMENT: If this website has a native image-generation feature, "
            "use it and return a real generated image attachment/output. Do NOT substitute ASCII art, "
            "pixel arrays, base64 text, HTML/CSS, SVG markup, or source code for the image. "
            "If this website cannot create images in the current chat, say so plainly; do not pretend "
            "that code or a textual description is an image."
        ) if image_request else ""
        if kind == "ask":
            return f"Here are my files:\n\n{project_block}\n\nMy question or task:\n{q}\n\n{self.REPLY_RULES}{image_rules}"
        return (
            f"That did not work. Here are the current files:\n\n{project_block}\n\n"
            f"The problem:\n{q}\n\nFind the cause and fix it. {self.REPLY_RULES}{image_rules}"
        )

    def copy_prompt(self, kind):
        prompt = self.build_prompt(kind)
        if prompt:
            self.to_clipboard(prompt, "Prompt copied. Paste it into the chat(s), then copy each reply.")

    def copy_ask(self):
        self.copy_prompt("ask")

    def copy_fix(self):
        self.copy_prompt("fix")

    # ---------- Replies ----------
    def paste_reply(self):
        try:
            text = self.clipboard_get()
        except tk.TclError:
            self.status("The clipboard is empty.")
            return
        self.reply.delete("1.0", "end")
        self.reply.insert("1.0", text)
        self.process_reply()

    def switch_ai(self):
        self.replies[self.shown_ai] = self.reply.get("1.0", "end-1c")
        self.shown_ai = self.ai_var.get()
        self.reply.delete("1.0", "end")
        self.reply.insert("1.0", self.replies[self.shown_ai])
        self.process_reply()

    def analyze(self, ai):
        found, unknown = parse_reply(self.replies[ai], self.files) if self.files else ({}, [])
        self.proposals[ai] = found
        added = removed = 0
        shown = []
        for p, code in found.items():
            before = normalize(self.texts[p]).rstrip("\n").split("\n")
            after = normalize(code).rstrip("\n").split("\n")
            lines = list(difflib.unified_diff(before, after, "current", "proposed", lineterm="", n=3))[2:]
            shown.append((p, lines))
            added += sum(1 for l in lines if l.startswith("+"))
            removed += sum(1 for l in lines if l.startswith("-"))
        self.analysis[ai] = (added, removed, unknown, shown)
        self.radios[ai].config(text=f"{ai} (+{added} -{removed})" if found else ai)

    def verify_and_recommend(self):
        """Run local static checks on each parsed proposal and rank the candidates."""
        reports = []
        ranked = []
        for ai in AIS:
            proposal = self.proposals.get(ai, {})
            if not proposal:
                reports.append(f"{ai}: no parseable full-file proposal received.")
                continue
            checks = []
            passed = 0
            for path, code in proposal.items():
                suffix = Path(path).suffix.lower()
                ok, detail = True, "basic text checks passed"
                if not code.strip():
                    ok, detail = False, "empty proposed file"
                elif suffix == ".py":
                    try:
                        ast.parse(code, filename=path)
                        detail = "Python syntax OK (parsed; not executed)"
                    except SyntaxError as exc:
                        ok, detail = False, f"Python syntax error at line {exc.lineno}: {exc.msg}"
                elif suffix == ".json":
                    try:
                        json.loads(code)
                        detail = "JSON syntax OK"
                    except json.JSONDecodeError as exc:
                        ok, detail = False, f"JSON error at line {exc.lineno}: {exc.msg}"
                elif suffix in (".js", ".jsx", ".ts", ".tsx", ".html", ".css"):
                    # No project-specific compiler is assumed; report this honestly.
                    detail = "non-empty; project-specific compiler/tests not run"
                if ok:
                    passed += 1
                checks.append(f"  {'PASS' if ok else 'FAIL'} {path}: {detail}")
            total = len(proposal)
            score = (passed / total) * 70 + (min(total, max(1, len(self.files))) / max(1, len(self.files))) * 30
            ranked.append((score, passed == total, ai, total, passed))
            reports.append(f"{ai}: static score {score:.1f}/100; {passed}/{total} files passed")
            reports.extend(checks)
        if ranked:
            ranked.sort(key=lambda item: (item[1], item[0], item[4], item[3]), reverse=True)
            best = ranked[0]
            # Only recommend when at least one candidate passed every check.
            if best[1]:
                self.shown_ai = best[2]
                self.ai_var.set(best[2])
                self.reply.delete("1.0", "end")
                self.reply.insert("1.0", self.replies[best[2]])
                self.render(best[2])
                reports.insert(0, f"RECOMMENDATION: {best[2]} ({best[0]:.1f}/100). Highest static-check score and complete checks.")
                self.verify_summary.config(text=f"Recommended: {best[2]} — {best[0]:.1f}/100")
            else:
                reports.insert(0, "NO SAFE AUTOMATIC PICK: every proposal has at least one failed static check. Review errors before applying.")
                self.verify_summary.config(text="No proposal passed all static checks.")
                self.save_btn.config(state="disabled")
        else:
            reports.insert(0, "No proposals to verify. Collect replies or paste each AI response first.")
            self.verify_summary.config(text="No proposals found.")
        self.verify_details.configure(state="normal")
        self.verify_details.delete("1.0", "end")
        self.verify_details.insert("1.0", "\n".join(reports))
        self.verify_details.configure(state="disabled")
        self.status("Verification complete. Recommendation is based on static checks and file coverage; review the diff and run project tests before applying.")

    def render(self, ai):
        added, removed, unknown, shown = self.analysis.get(ai, (0, 0, [], []))
        self.diff.config(state="normal")
        self.diff.delete("1.0", "end")
        for p, lines in shown:
            self.diff.insert("end", f"=== {p} ===\n", "head")
            if not lines:
                self.diff.insert("end", "No differences from the file on GitHub.\n")
            for l in lines:
                if l.startswith("+"):
                    tag = "add"
                elif l.startswith("-"):
                    tag = "del"
                else:
                    tag = "hunk" if l.startswith("@@") else ""
                self.diff.insert("end", l + "\n", tag)
            self.diff.insert("end", "\n")
        self.diff.config(state="disabled")

        n = len(shown)
        if n:
            note = f"{ai}: {n} file(s) changed, {added} lines added, {removed} removed."
        elif ai in self.api_errors:
            note = f"{ai} could not answer: {self.api_errors[ai]}"
        elif self.replies[ai].strip():
            note = f"{ai}: no code for your loaded files found in this reply."
        else:
            note = ""
        if unknown:
            note += f"  Ignored files that are not loaded: {', '.join(unknown)}"
        self.summary.config(text=note)
        self.save_btn.config(state="normal" if n else "disabled")

    def process_reply(self):
        self.replies[self.shown_ai] = self.reply.get("1.0", "end-1c")
        self.analyze(self.shown_ai)
        self.render(self.shown_ai)

    # ---------- Commit / undo ----------
    @staticmethod
    def with_endings(text, original):
        t = normalize(text)
        if normalize(original).endswith("\n") and not t.endswith("\n"):
            t += "\n"
        if "\r\n" in original:
            t = t.replace("\n", "\r\n")
        return t

    def save(self):
        proposal = self.proposals.get(self.shown_ai, {})
        if not proposal:
            return
        ai = self.shown_ai
        done = {}
        try:
            self.busy("Committing to GitHub...")
            for path, code in proposal.items():
                if self.local_root:
                    current = self.read_local_file(path)
                    self.write_local_file(path, self.with_endings(code, current))
                else:
                    current, sha = self.fetch_file(path)
                    self.put_file(path, self.with_endings(code, current), sha, f"AI Bridge: update {path} ({ai})")
                done[path] = current
        except GitHubError as e:
            self.status(str(e))
            messagebox.showerror("Could not commit", str(e))
        finally:
            self.idle()
        if not done:
            return
        self.previous = done
        self.undo_btn.config(state="normal")
        try:
            self.texts = ({p: self.read_local_file(p) for p in self.files} if self.local_root
                          else {p: self.fetch_file(p)[0] for p in self.files})
        except GitHubError:
            pass
        self.process_reply()
        if self.local_root:
            self.status(f"Applied {ai}'s approved changes to {len(done)} local file(s). Backups are in .ai_bridge_backups.")
        else:
            self.status(f"Committed {ai}'s answer to {len(done)} file(s) on branch {self.branch}. Refresh the VS Code for the web tab to see it.")

    def undo(self):
        if not self.previous:
            return
        try:
            self.busy("Undoing...")
            for path, text in self.previous.items():
                if self.local_root:
                    self.write_local_file(path, text)
                else:
                    _, sha = self.fetch_file(path)
                    self.put_file(path, text, sha, f"AI Bridge: undo changes to {path}")
            self.previous = {}
            self.texts = ({p: self.read_local_file(p) for p in self.files} if self.local_root
                          else {p: self.fetch_file(p)[0] for p in self.files})
        except GitHubError as e:
            self.status(str(e))
            messagebox.showerror("Could not undo", str(e))
            return
        finally:
            self.idle()
        self.undo_btn.config(state="disabled")
        self.process_reply()
        self.status("Restored the previous versions with a new commit.")


if __name__ == "__main__":
    App().mainloop()
