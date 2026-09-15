import importlib.abc
import importlib.util
import sys
import types

_BUNDLED_MODULES = {
    'config': r'''import json
import sys
from colorama import Fore, Style

# ── Valid providers ───────────────────────────────────────────────
VALID_PROVIDERS = {"bitsolver", "bit_solver", "captchasonic", "anysolver", "custom"}

# ── Config loader ─────────────────────────────────────────────────
def load_config():
    config = {}
    try:
        with open("input/config.json", "r", encoding="utf-8") as f:
            config = json.load(f)
    except FileNotFoundError:
        print(f"{Fore.RED}[config] input/config.json not found.{Style.RESET_ALL}")
    except json.JSONDecodeError as e:
        print(f"{Fore.RED}[config] JSON parse error in config.json: {e}{Style.RESET_ALL}")
        sys.exit(1)
    return config


def get_solver_config(config: dict) -> dict:
    """
    Returns a ready-to-use solver config dict:
        {
            "enabled":  bool,
            "provider": "bitsolver" | "anysolver" | "custom",
            "api_key":  str,
            "base_url": str,
        }
    """
    solver_cfg = config.get("solver", {})

    enabled = solver_cfg.get("enabled", True)
    if not enabled:
        return {"enabled": False, "provider": None, "api_key": "", "base_url": ""}

    raw_provider = solver_cfg.get("provider", "bitsolver").lower().strip()

    alias_map = {
        "bit_solver":          "bitsolver",
        "captchasonic":        "bitsolver",
        "captchasonic_solver": "bitsolver",
    }
    provider = alias_map.get(raw_provider, raw_provider)

    if provider not in VALID_PROVIDERS:
        print(
            f"{Fore.RED}[config] Unknown solver provider '{raw_provider}'. "
            f"Valid options: {sorted(VALID_PROVIDERS)}{Style.RESET_ALL}"
        )
        sys.exit(1)

    provider_cfg = solver_cfg.get(provider, {})

    api_key  = provider_cfg.get("api_key",  "")
    base_url = provider_cfg.get("base_url", "")

    if provider != "bitsolver" and (not api_key or "YOUR_" in api_key):
        print(
            f"{Fore.YELLOW}[config] solver.{provider}.api_key is not set. "
            f"Captcha solving may fail.{Style.RESET_ALL}"
        )

    return {
        "enabled":  True,
        "provider": provider,
        "api_key":  api_key,
        "base_url": base_url,
    }
''',
    'utils.account': r'''import os, time, random, string, json, requests, threading, re, base64, functools
from colorama import Fore, Style
from stealth_requests import StealthSession

from utils.core import STATS, format_status, format_token_id, setup_logger, write_json_atomic, default_request_timeout
from utils.build import (
    get_build_number,
    build_super_properties,
    fetch_cookies,
    get_fingerprint,
    build_headers,
    USER_AGENT,
    CHROME_VERSION,
    get_random_profile,
    load_cached_edge_state,
    save_cached_edge_state,
    refresh_session_launch_identifiers,
    repair_cached_profile,
    pick_invite_attribution,
    build_attributed_super_properties,
    BODY_ORIGIN,
    apply_tls_profile,
)
from utils.proxy import format_proxy_url, detect_timezone

from utils.telemetry import ScienceTelemetry
from config import load_config

log = setup_logger(__name__)

class DisabledChallengeClient:
    def __init__(self, *args, **kwargs):
        self._solver_type = args[0] if len(args) > 0 else None
        self._website_url = args[1] if len(args) > 1 else "https://discord.com/"
        self._api_key     = args[2] if len(args) > 2 else None

    def solve(self, *args, **kwargs):
        try:
            import nopecha
        except ImportError:
            log.warning("nopecha not installed - pip install nopecha")
            return None
        if not self._api_key:
            log.warning("No NopeCHA API key configured")
            return None

        sitekey      = kwargs.get("sitekey")
        rqdata       = kwargs.get("rqdata") or None
        user_agent   = kwargs.get("user_agent")
        proxy        = kwargs.get("proxy")
        task_type    = kwargs.get("task_type", "HCaptcha")
        url          = self._website_url or "https://discord.com/"

        if not sitekey:
            return None

        # NopeCHA types: "hcaptcha", "turnstile", "recaptcha2", "recaptcha3"
        ntype = "turnstile" if "Turnstile" in str(task_type) else "hcaptcha"

        try:
            nopecha.api_key = self._api_key
            params = {"type": ntype, "sitekey": sitekey, "url": url}
            if rqdata:
                params["data"] = rqdata
            if user_agent:
                params["useragent"] = user_agent
            if proxy:
                # NopeCHA wants scheme://user:pass@host:port — format_proxy_url
                # in utils/proxy already produces this.
                params["proxy"] = proxy
            result = nopecha.Token.solve(**params)
            if isinstance(result, str) and result:
                return result
            log.warning(f"NopeCHA returned {type(result).__name__}, not a token")
            return None
        except Exception as exc:
            log.warning(f"NopeCHA solve failed: {type(exc).__name__}: {exc}")
            return None

API = "https://discord.com/api/v9"
# Upper bound on a server-supplied retry_after, in seconds.
MAX_RETRY_AFTER = 300.0
db_lock = threading.Lock()
DB_FILE = "output/joined_guilds.json"

token_sessions = {}
token_captcha_count = {}
# The set of DISTINCT invites that have challenged each token with a captcha.
# It is a set, not a counter, so a token that retries the same invite several
# times still counts as one: max_captcha_before_skip is "how many different
# servers captcha'd this token", not "how many captcha attempts". A token that
# is challenged on that many separate invites is low-trust and is retired to
# captchaed.txt instead of being fed more invites. Counts even with the solver
# off, since nothing solves then.
token_captcha_invites = {}
# Per-token retirement threshold, drawn once from [min_captcha_before_skip,
# max_captcha_before_skip]. Randomised per token so there is no single fixed
# number of captchas that always triggers a skip.
token_captcha_limit = {}

# Consecutive captcha solves that FAILED while the solver was enabled. This is a
# health signal for the Bit Solver itself, not a token problem: if it climbs, the
# solver service is not returning usable tokens and the operator should check it.
_solver_fail_streak = {"count": 0}
SOLVER_FAIL_WARN_AT = 5
warmed_up_tokens = set()
_consecutive_invalid_counts = {}
INVALID_RETIRE_THRESHOLD = 3


def mark_token_invalid_attempt(token):
    """Increment the consecutive-invalid counter for a token and return the new count.

    A single transient 401/429/5xx must not retire a token. Only after this many
    consecutive failures is the token treated as genuinely dead. Call
    `clear_token_invalid_attempts(token)` on any clean join to reset it.
    """
    with sessions_lock:
        _consecutive_invalid_counts[token] = _consecutive_invalid_counts.get(token, 0) + 1
        return _consecutive_invalid_counts[token]


def clear_token_invalid_attempts(token):
    """Reset the consecutive-invalid counter for a token after a successful join."""
    with sessions_lock:
        _consecutive_invalid_counts.pop(token, None)
sessions_lock = threading.Lock()
file_write_lock = threading.Lock()

# User flag bits Discord sets on accounts it has decided not to trust. A
# quarantined/spammer account can still log in and browse, but every guild
# join is refused with 403/10008 ("Unknown Message") -- after the captcha has
# been solved. /users/@me already tells us, so check before spending a solve.
USER_FLAG_QUARANTINED = 1 << 44
PUBLIC_FLAG_SPAMMER = 1 << 20


def is_quarantined_user(me: dict) -> bool:
    try:
        return bool(int(me.get("flags") or 0) & USER_FLAG_QUARANTINED) or \
               bool(int(me.get("public_flags") or 0) & PUBLIC_FLAG_SPAMMER)
    except (TypeError, ValueError):
        return False


def check_token_status(session):
    try:
        r = session.get(f"{API}/users/@me")
    except Exception:
        return "transient_error"
    if r.status_code == 429:
        return "rate_limited"
    if r.status_code >= 500:
        return "transient_error"
    if r.status_code == 401:
        return "invalid"
    if r.status_code == 403:
        return "locked"
    if r.status_code != 200:
        return "transient_error"
    try:
        if is_quarantined_user(r.json() or {}):
            return "quarantined"
    except Exception:
        pass
    try:
        r2 = session.get(f"{API}/users/@me/settings-proto/2")
    except Exception:
        return "transient_error"
    if r2.status_code == 200:
        return "Valid"
    if r2.status_code == 403:
        return "locked"
    if r2.status_code == 429:
        return "rate_limited"
    if r2.status_code >= 500:
        return "transient_error"
    return "transient_error"

def get_token_joined_guild_ids(session):
    try:
        r = session.get(f"{API}/users/@me/guilds")
        if r.status_code == 200:
            guilds = r.json()
            return {guild.get("id") for guild in guilds if guild.get("id")}
    except Exception:
        pass
    return set()

def is_guild_joined(session, guild_id):
    if not guild_id:
        return False
    return guild_id in get_token_joined_guild_ids(session)

def save_joined_guild(token, guild_id):
    save_guild_to_db(token, guild_id)

# The joined-guild DB is held in memory and written through on change.
# Previously every join reparsed the whole file (it grows to megabytes) and then
# every caller re-flattened it into a set of all joined guild ids, so each join
# attempt cost O(total_guilds) twice. `account.py` is the only writer; the
# dashboard and stats bot read the file, which the write-through keeps current.
_guilds_db = None
_global_joined_guild_ids = set()


def _ensure_guilds_db_loaded():
    """Populate the in-memory DB from disk once. Caller must hold db_lock."""
    global _guilds_db
    if _guilds_db is not None:
        return
    db = {}
    if os.path.exists(DB_FILE):
        try:
            with open(DB_FILE, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                db = loaded
        except Exception as e:
            # A corrupt DB reads as empty, which makes the bot re-join
            # everything. That is worth a warning, not silence.
            log.warning(f"Could not read {DB_FILE}, treating as empty: {e}")
    _guilds_db = db
    _global_joined_guild_ids.clear()
    for gids in db.values():
        if isinstance(gids, list):
            _global_joined_guild_ids.update(gids)


def load_guilds_db():
    """Return the joined-guild DB. Treat the result as read-only."""
    with db_lock:
        _ensure_guilds_db_loaded()
        return _guilds_db


def is_guild_globally_joined(guild_id):
    """True if any token has already joined this guild. O(1)."""
    if not guild_id:
        return False
    with db_lock:
        _ensure_guilds_db_loaded()
        return guild_id in _global_joined_guild_ids


# A guild claimed by a token but not yet recorded as joined. Between the
# "has anyone joined this server?" check and save_guild_to_db() there is a full
# join round trip -- invite fetch, POST, possibly a captcha solve. With one
# dispatcher that window is safe because nothing else runs during it. With a
# dispatcher per thread two threads can both look, both see the server as free,
# and both join it, which breaks the one-token-per-server rule. Reserving the
# guild id closes that window, and because it keys on the guild rather than the
# invite it also catches two different invite codes pointing at one server.
#
# Entries carry a timestamp and expire: a join can fail on any of a dozen paths,
# and a reservation that leaked would lock a server out for the rest of the run.
_guild_reservations = {}
# @releases_guild_claims drops a claim on every return, so the TTL only guards a
# hung thread. 600s could expire mid-join: warmup + a 429 backoff (up to 301s) +
# captcha rounds (120s each, up to four) exceed it, and a second thread could
# then claim the same guild while the first was still joining it.
GUILD_RESERVATION_TTL = 3600.0

# join_server has a dozen return paths and can raise, so releasing a claim at
# each one by hand would miss some. Claims are instead tracked per worker thread
# and cleared by the @releases_guild_claims wrapper when the call returns,
# whatever it returns. A successful join has already dropped its claim in
# save_guild_to_db, so the sweep is a no-op there.
_claim_tls = threading.local()


def releases_guild_claims(fn):
    """Release any guild this call claimed but did not end up joining."""
    @functools.wraps(fn)
    def wrapper(*args, **kwargs):
        previous = getattr(_claim_tls, "claimed", None)
        _claim_tls.claimed = set()
        try:
            return fn(*args, **kwargs)
        finally:
            for gid in _claim_tls.claimed:
                release_guild(gid)
            _claim_tls.claimed = previous

    return wrapper


def reserve_guild(guild_id):
    """Claim a guild for the caller. False if it is already joined or in flight."""
    if not guild_id:
        return True
    guild_id = str(guild_id)
    now = time.time()
    with db_lock:
        _ensure_guilds_db_loaded()
        if guild_id in _global_joined_guild_ids:
            return False
        for gid, claimed_at in list(_guild_reservations.items()):
            if now - claimed_at > GUILD_RESERVATION_TTL:
                del _guild_reservations[gid]
        if guild_id in _guild_reservations:
            return False
        _guild_reservations[guild_id] = now
    claimed = getattr(_claim_tls, "claimed", None)
    if claimed is not None:
        claimed.add(guild_id)
    return True


def release_guild(guild_id):
    """Give up a claim, so another token may try this server."""
    if not guild_id:
        return
    with db_lock:
        _guild_reservations.pop(str(guild_id), None)


def save_guild_to_db(token, guild_id):
    with db_lock:
        _ensure_guilds_db_loaded()
        entry = _guilds_db.setdefault(token, [])
        if guild_id in entry:
            return
        entry.append(guild_id)
        _global_joined_guild_ids.add(guild_id)
        # Permanently recorded now, so the in-flight claim is no longer needed.
        _guild_reservations.pop(str(guild_id), None)

        try:
            write_json_atomic(DB_FILE, _guilds_db)
        except Exception as e:
            # Roll the in-memory state back so it keeps matching disk, otherwise
            # the guild is treated as joined forever without ever being recorded.
            entry.remove(guild_id)
            _global_joined_guild_ids.discard(guild_id)
            log.warning(f"Failed to write {DB_FILE}: {e}")

def get_realistic_invite_referer(invite_code, provider=None):
    """Return (referer_url, attribution) for an invite.

    Both halves must be used together. In the captures the Referer and
    x-super-properties always tell the same story: a disboard referral carries
    utm params in the Referer query *and* utm_*_current inside super-properties
    with referrer_current pointing at disboard.org, while a direct arrival has a
    plain Referer and referrer_current pointing at the invite page itself.
    Returning only the URL is what previously let the two headers disagree.
    """
    clean_code = invite_code
    query_part = None
    if "?" in invite_code:
        clean_code, query_part = invite_code.split("?", 1)

    if query_part:
        # Invite already carries its own tags; keep them and mirror them.
        attribution = pick_invite_attribution("disboard") if "disboard" in query_part else pick_invite_attribution()
        return f"https://discord.com/invite/{clean_code}?{query_part}", attribution

    attribution = pick_invite_attribution(provider)
    q = attribution.get("referer_query")
    referer = f"https://discord.com/invite/{clean_code}" + (f"?{q}" if q else "")
    return referer, attribution


def get_launch_attribution(profile, invite_code):
    """Return (referer, attribution) for this request, deciding attribution once
    per page load.

    The attribution and the invite that seeded `referrer_current` are stored on
    the profile, which lives for as long as the client_launch_id does. Later
    invites on the same launch reuse them, so `x-super-properties` stays byte
    identical while only the Referer moves -- exactly what the captures show.
    """
    if profile is None:
        return get_realistic_invite_referer(invite_code)

    attribution = profile.get("_launch_attribution")
    if attribution is None:
        _, attribution = get_realistic_invite_referer(invite_code)
        profile["_launch_attribution"] = attribution
        profile["_launch_invite"] = str(invite_code).split("?", 1)[0]

    clean_code = str(invite_code).split("?", 1)[0]
    q = attribution.get("referer_query")
    referer = f"https://discord.com/invite/{clean_code}" + (f"?{q}" if q else "")
    return referer, attribution


def fetch_invite_metadata(session, invite_code):
    try:
        r = session.get(f"{API}/invites/{invite_code}?with_counts=true&with_expiration=true&with_permissions=true&with_games=true")
        if r.status_code == 200:
            return r.json()
    except Exception as e:
        log.debug(f"Failed to fetch metadata for invite {invite_code}: {e}")
    return {}

def _drop_session(token):
    """Discard a token's cached session, close its gateway, and stop telemetry.

    Used whenever we abandon an attempt: the next try then starts from a clean
    session rather than reusing one Discord has already challenged.
    """
    with sessions_lock:
        cached = token_sessions.pop(token, None)
    if cached:
        _cleanup_session(cached)

def _invite_is_dead(session, invite_code):
    """True only when Discord confirms the invite no longer works.

    Solving a captcha takes 30-60s, and invites get deleted or revoked in that
    window — the join then fails with 403/10008 and the solve is wasted. Checking
    first costs one cheap GET.

    Returns False on any network/transport error: uncertainty must not throw away
    a good invite.
    """
    try:
        r = session.get(f"{API}/invites/{invite_code}?with_counts=true&with_expiration=true&with_permissions=true&with_games=true")
    except Exception as e:
        log.debug(f"Invite liveness check failed for {invite_code}: {e}")
        return False

    if r.status_code == 404:
        return True
    if r.status_code == 200:
        return False
    try:
        code = r.json().get("code")
    except Exception:
        return False
    # 10006 = Unknown Invite
    return code == 10006

_file_unique_cache = {}
_file_cache_initialized = False

def seed_output_file_caches():
    """Pre-seed file deduplication sets into memory to prevent synchronous disk I/O under concurrent workers."""
    global _file_cache_initialized
    if _file_cache_initialized:
        return
    _file_cache_initialized = True
    
    known_files = [
        "output/joined.txt",
        "output/locked.txt",
        "output/invalid.txt",
        "output/rate.txt",
        "output/error.txt",
        "output/hcaptcha_tokens.txt",
        "output/turnstile_tokens.txt",
        "output/verified_tokens.txt",
        "output/dm_verified.txt",
    ]
    for fn in known_files:
        lines_set = set()
        if os.path.exists(fn):
            try:
                with open(fn, "r", encoding="utf-8", errors="ignore") as f:
                    for l in f:
                        stripped = l.strip()
                        if stripped:
                            lines_set.add(stripped)
            except Exception:
                pass
        with file_write_lock:
            if fn not in _file_unique_cache:
                _file_unique_cache[fn] = lines_set
            else:
                _file_unique_cache[fn].update(lines_set)


def write_unique_line(filename, line):
    """Write a unique line to file using non-blocking in-memory set cache for zero redundant disk I/O."""
    line = line.strip()
    if not line:
        return

    # Lock-free fast path check
    cached = _file_unique_cache.get(filename)
    if cached is not None and line in cached:
        return

    with file_write_lock:
        if filename not in _file_unique_cache:
            lines_set = set()
            if os.path.exists(filename):
                try:
                    with open(filename, "r", encoding="utf-8", errors="ignore") as f:
                        for l in f:
                            stripped = l.strip()
                            if stripped:
                                lines_set.add(stripped)
                except Exception:
                    pass
            _file_unique_cache[filename] = lines_set

        if line not in _file_unique_cache[filename]:
            try:
                os.makedirs(os.path.dirname(filename) or ".", exist_ok=True)
                with open(filename, "a", encoding="utf-8") as f:
                    f.write(f"{line}\n")
            except Exception as e:
                # Only mark the line as written once it actually is. Adding to the
                # dedup set first meant a failed append was never retried: the
                # cache claimed the record existed, so a joined or verified token
                # went unrecorded for the rest of the run.
                log.warning(f"Failed to write to {filename}: {e}")
            else:
                _file_unique_cache[filename].add(line)


def simulate_human_warmup(session, token, gateway=None):
    """Stealthy lightweight startup sequence.
    Makes only the critical initial requests with healthy human-like pauses,
    and automatically populates missing/default profile pictures, bios, and custom statuses."""
    try:
        short = format_token_id(token)
        log.debug(f"Human warm-up starting for token {short}...")

        # 1. Own profile
        session.get(f"{API}/users/@me")
        time.sleep(random.uniform(2.0, 4.0))        # 3. User settings (modern proto endpoints)
        session.get(f"{API}/users/@me/settings-proto/1")
        time.sleep(random.uniform(2.0, 4.0))
        session.get(f"{API}/users/@me/settings-proto/2")
        time.sleep(random.uniform(1.5, 3.5))

        # 4. Guild list
        r_guilds = session.get(f"{API}/users/@me/guilds?with_counts=true")
        time.sleep(random.uniform(2.0, 5.0))

        if r_guilds.status_code == 200:
            guilds = r_guilds.json()
            if guilds and isinstance(guilds, list):
                # Pick 1 random guild to inspect channels and messages
                sample_guild = random.choice(guilds[:5])
                guild_id = sample_guild.get("id")
                if guild_id:
                    r_ch = session.get(f"{API}/guilds/{guild_id}/channels")
                    time.sleep(random.uniform(1.5, 3.5))
                    if r_ch.status_code == 200:
                        channels = r_ch.json()
                        text_channels = [c for c in channels if c.get("type") == 0]
                        if text_channels:
                            chosen_ch = random.choice(text_channels)["id"]
                            # view channel messages matching desktop viewport default (14)
                            session.get(f"{API}/channels/{chosen_ch}/application-command-index")
                            time.sleep(random.uniform(0.5, 1.2))
                            session.get(f"{API}/channels/{chosen_ch}/messages?limit=14")
                            time.sleep(random.uniform(3.0, 8.0))
        
        # Final human-like pause before action
        pause = random.uniform(6.0, 12.0)
        log.debug(f"Warm-up completed for {short}. Pausing {pause:.1f}s before join.")
        time.sleep(pause)
    except Exception as e:
        log.debug(f"Human warm-up error: {e}")


# Vaultcord-owned domains used in the OAuth2 redirect_uri
_VAULTCORD_DOMAINS = ("vaultcord.win", "vaultcord.com")

# Keywords in embed titles / descriptions that signal a verification message
_VERIFY_EMBED_KEYWORDS = (
    "verification required", "verify now", "prove you are a human",
    "complete verification", "gain access", "click the button below",
)


def is_verification_enabled(cfg=None):
    """Return True if verification bypass is enabled in config.json.
    Supports config formats:
      - "verification": {"enabled": true/false}
      - "verification": true/false
      - "enable_verification": true/false
      - "verification_enabled": true/false
    Defaults to True if not configured.
    """
    if cfg is None:
        cfg = load_config()
    verif = cfg.get("verification")
    if verif is None:
        verif = cfg.get("enable_verification", cfg.get("verification_enabled", True))
    if isinstance(verif, dict):
        return bool(verif.get("enabled", True))
    return bool(verif)



def _is_vaultcord_msg(msg):
    """Return True if this message is a Vaultcord verification prompt.

    Since Vaultcord allows server owners to use their OWN custom bot,
    we cannot match by bot ID or username. The only reliable fingerprint
    is the OAuth2 URL's redirect_uri pointing to vaultcord.win or vaultcord.com.

    We check:
      1. Any Link Button (style=5) whose URL is a discord.com/oauth2/authorize
         link AND whose redirect_uri parameter contains a Vaultcord domain.
      2. Fallback: embed/content keywords for older direct-link style.
    """
    from urllib.parse import urlparse, parse_qs

    # --- Check 1: Link Button with Vaultcord redirect_uri ---
    for row in msg.get("components", []):
        if row.get("type") != 1:
            continue
        for btn in row.get("components", []):
            if btn.get("type") == 2 and btn.get("style") == 5:
                url = btn.get("url", "")
                if "discord.com/oauth2/authorize" in url:
                    try:
                        qs = parse_qs(urlparse(url).query)
                        redirect = qs.get("redirect_uri", [""])[0].lower()
                        if any(d in redirect for d in _VAULTCORD_DOMAINS):
                            return True
                    except Exception:
                        pass
                # Direct vaultcord.com link in button (older style)
                if any(d in url.lower() for d in _VAULTCORD_DOMAINS):
                    return True

    # --- Check 2: Vaultcord domain in text / embeds ---
    all_text = (msg.get("content") or "").lower()
    for embed in msg.get("embeds", []):
        all_text += " " + (embed.get("title") or "").lower()
        all_text += " " + (embed.get("description") or "").lower()

    if any(d in all_text for d in _VAULTCORD_DOMAINS):
        return True

    return False

def _extract_verify_url_from_msg(msg):
    """Extract the verification URL from a message already confirmed as Vaultcord.
    Checks in priority order:
      1. Link Button (style=5) with an OAuth2 discord.com/oauth2/authorize URL
      2. Link Button with a direct vaultcord domain URL
      3. Text / embed regex fallback
    """
    from urllib.parse import urlparse, parse_qs

    # --- Priority 1 & 2: Link Button ---
    for row in msg.get("components", []):
        if row.get("type") != 1:
            continue
        for btn in row.get("components", []):
            if btn.get("type") == 2 and btn.get("style") == 5:
                url = btn.get("url", "")
                if url:
                    return url   # caller decides how to handle (OAuth2 vs direct)

    # --- Priority 3: regex on text / embeds ---
    content = msg.get("content", "")
    for pattern in (
        r'https?://(?:www\.)?vaultcord\.(?:com|win)/[^\s>"]+',
        r'https?://discord\.com/oauth2/authorize[^\s>"]+',
    ):
        found = re.findall(pattern, content)
        if found:
            return found[0]

    for embed in msg.get("embeds", []):
        for text in (
            embed.get("description") or "",
            embed.get("url") or "",
            *(f.get("value") or "" for f in embed.get("fields", [])),
        ):
            for pattern in (
                r'https?://(?:www\.)?vaultcord\.(?:com|win)/[^\s>"]+',
                r'https?://discord\.com/oauth2/authorize[^\s>"]+',
            ):
                found = re.findall(pattern, text)
                if found:
                    return found[0]

    return None


def _complete_oauth2_verify(session, token, oauth_url, solver_type=None, solver_api_key=None, proxy=None):
    """Complete a Discord OAuth2 verification flow programmatically and submit
    the verification payload to the Vaultcord backend to authenticate the token.

    How it works:
      1. POSTs authorization to Discord's /oauth2/authorize endpoint.
      2. Receives a redirect location (e.g. https://vaultcord.win/auth?code=XXX&state=YYY).
      3. Parses the code, state, and domain from that location.
      4. Fetches the proxy's IP address.
      5. Solves Cloudflare Turnstile if state contains 'captcha' (using sitekey '0x4AAAAAAAKIBcu9J8jgbnL8').
      6. POSTs the verification packet to https://api.vaultcord.com/servers/verify.
    """
    from urllib.parse import urlparse, parse_qs

    short = format_token_id(token)
    try:
        parsed = urlparse(oauth_url)
        params = parse_qs(parsed.query, keep_blank_values=True)

        def p(key, default=""):
            return params.get(key, [default])[0]

        query = {
            "client_id":     p("client_id"),
            "response_type": p("response_type", "code"),
            "redirect_uri":  p("redirect_uri"),
            "scope":         p("scope"),
            "state":         p("state"),
            "prompt":        p("prompt", "none"),
        }
        query = {k: v for k, v in query.items() if v}

        log.info(
            f"OAuth2 authorize for {short}: client_id={query.get('client_id')}"
        )

        original_referer = session.headers.get("referer")
        session.headers["referer"] = oauth_url

        try:
            r = session.post(
                "https://discord.com/api/v9/oauth2/authorize",
                params=query,
                json={"authorize": True, "permissions": "0"},
                headers={"authorization": token},
            )
        finally:
            if original_referer:
                session.headers["referer"] = original_referer
            else:
                session.headers.pop("referer", None)

        if r.status_code not in (200, 201):
            log.debug(
                f"OAuth2 authorize POST failed for {short}: {r.status_code} {r.text[:200]}"
            )
            return False

        data = r.json()
        location = data.get("location")
        if not location:
            log.debug(f"No redirect location in OAuth2 response for {short}: {data}")
            return False

        log.info(f"OAuth2 redirect for {short} → {location}")

        # Parse callback parameters
        parsed_loc = urlparse(location)
        loc_params = parse_qs(parsed_loc.query)
        code = loc_params.get("code", [""])[0]
        state = loc_params.get("state", [""])[0]
        domain = parsed_loc.netloc

        if not code:
            log.debug(f"No code found in redirect callback for {short}: {location}")
            return False

        # Create an isolated external session for non-Discord verification endpoints
        # Ensures zero Discord cookies (__dcfduid, __sdcfduid, _cfuvid) or auth tokens are leaked
        ext_sess = StealthSession(timeout=default_request_timeout())
        if proxy:
            norm_proxy = format_proxy_url(proxy)
            if norm_proxy:
                ext_sess.proxies = {"http": norm_proxy, "https": norm_proxy}
        turnstile_ua = session.headers.get("user-agent", USER_AGENT)
        ext_sess.headers.update({
            "User-Agent": turnstile_ua,
            "Accept": "application/json, text/plain, */*",
            "Accept-Language": "en-US,en;q=0.9",
        })

        # Get proxy IP Address (Vaultcord checks this to verify server entry)
        ip_addr = None
        try:
            ip_res = ext_sess.get("https://api.ipify.org/?format=json", timeout=10)
            ip_addr = ip_res.json().get("ip")
        except Exception as e:
            log.debug(f"Could not retrieve proxy IP address for {short}: {e}")

        # Fingerprint generation (random 32-char hex string as a visitor ID)
        visitor_id = "".join(random.choices("0123456789abcdef", k=32))

        payload = {
            "code": code,
            "domain": domain,
            "ip": ip_addr,
            "fingerprint": visitor_id
        }

        # Solve Cloudflare Turnstile if state parameter specifies it
        if state and "captcha" in state and "no-captcha" not in state:
            if not solver_type or not solver_api_key:
                log.warning("Turnstile captcha required for Vaultcord, but solver is disabled or not configured. Skipping Vaultcord verification...")
                status = check_token_status(session)
                log.info(f"Account status after Turnstile check: {status}")
                save_joined_token(token, status if status in ("locked", "invalid") else "failed", "")
                return False

            log.info(f"Solving Turnstile captcha for Vaultcord verification on {domain}...")
            turnstile_token = None
            try:
                
                turnstile_token = DisabledChallengeClient(
                    solver_type,
                    f"https://{domain}/",
                    solver_api_key
                ).solve(
                    rqdata="",
                    user_agent=turnstile_ua,
                    proxy=proxy,
                    sitekey="0x4AAAAAAAKIBcu9J8jgbnL8",
                    task_type="TurnstileToken" if proxy else "TurnstileTokenProxyLess"
                )
            except Exception as e:
                log.error(f"Turnstile solving error: {e}")

            if not turnstile_token:
                log.warning(f"Could not solve Turnstile captcha for token {short}")
                return False

            log.info(f"Turnstile solved successfully!")
            payload["token"] = turnstile_token

        # Submit verified credentials to Vaultcord API via isolated session
        verify_url = "https://api.vaultcord.com/servers/verify"
        log.info(f"POSTing verification payload to Vaultcord backend for {short}...")
        
        time.sleep(random.uniform(1.0, 2.5))
        
        verify_res = ext_sess.post(
            verify_url,
            json=payload,
            headers={"Content-Type": "application/json", "Origin": f"https://{domain}", "Referer": f"https://{domain}/"}
        )

        try:
            res_json = verify_res.json()
        except Exception:
            res_json = {}

        if verify_res.status_code in (200, 201) and res_json.get("success"):
            log.info(
                f"{Fore.GREEN}Vaultcord OAuth2 verification fully completed for {short}!{Style.RESET_ALL}"
            )
            return True
        else:
            log.warning(
                f"Vaultcord verification API returned failure for {short}: "
                f"Status: {verify_res.status_code}, Message: {res_json.get('message', 'No message')}"
            )
            return False
    except Exception as e:
        log.debug(f"OAuth2 verify error for {short}: {e}")
        return False


def _is_verification_dm(dm):
    """Return True for any bot DM — message-level filtering handles specifics."""
    return any(rec.get("bot") for rec in dm.get("recipients", []))


def bypass_vaultcord(session, token, solver_type=None, solver_api_key=None, proxy=None):
    if not is_verification_enabled():
        return
    short = format_token_id(token)
    try:
        # Give the custom bot time to send its DM after join (2–5 s typically)
        time.sleep(random.uniform(4.0, 7.0))

        r = session.get(f"{API}/users/@me/channels")
        if r.status_code != 200:
            return
        dms = r.json()

        for dm in dms:
            if dm.get("type") != 1:        # type 1 = DM
                continue
            if not _is_verification_dm(dm): # skip non-bot DMs early
                continue

            dm_id = dm["id"]
            r_msgs = session.get(f"{API}/channels/{dm_id}/messages?limit=10")
            if r_msgs.status_code != 200:
                continue

            for msg in r_msgs.json():
                if not _is_vaultcord_msg(msg):
                    continue  # not a Vaultcord message — skip

                url = _extract_verify_url_from_msg(msg)
                if not url:
                    continue

                log.info(
                    f"Vaultcord verify detected for {short} → {url[:80]}"
                )
                time.sleep(random.uniform(1.5, 4.0))  # human reading delay
                try:
                    if "discord.com/oauth2/authorize" in url:
                        _complete_oauth2_verify(session, token, url, solver_type, solver_api_key, proxy)
                    else:
                        # Direct vaultcord.com link (older style)
                        res = session.get(url, allow_redirects=True)
                        if res.status_code in (200, 201, 204, 302):
                            log.info(
                                f"{Fore.GREEN}Vaultcord verified for {short} "
                                f"(HTTP {res.status_code}).{Style.RESET_ALL}"
                            )
                        else:
                            log.debug(
                                f"Vaultcord direct link failed for {short}: "
                                f"{res.status_code} {res.text[:200]}"
                            )
                except Exception as e:
                    log.debug(f"Vaultcord link error for {short}: {e}")
                return  # one attempt is enough
    except Exception as e:
        log.debug(f"Vaultcord bypass error for {short}: {e}")


def simulate_human_browsing(session, guild_id, gw=None, telemetry=None):
    try:
        # 1. Fetch own guild member object immediately upon joining
        session.get(f"{API}/guilds/{guild_id}/members/@me")
        time.sleep(random.uniform(0.5, 1.2))

        # 2. Check welcome screen configuration & member counts
        session.get(f"{API}/guilds/{guild_id}/new-member-welcome")
        session.get(f"{API}/guilds/{guild_id}/roles/member-counts")

        # 3. WebSocket Opcode 37: Subscribe to typing/activities for the guild
        if gw:
            gw.subscribe_guild(guild_id)

        # 4. Fetch channel hierarchy
        r_channels = session.get(f"{API}/guilds/{guild_id}/channels")
        if r_channels.status_code != 200:
            return
        channels = r_channels.json()
        
        # text channels type=0
        text_channels = [ch["id"] for ch in channels if ch.get("type") == 0]
        if not text_channels:
            return

        target_ch = random.choice(text_channels)

        # 6. WebSocket Opcode 14: Subscribe to member ranges in channel viewport.
        # Op 14 is off by default. The capture in websocket_history.xml is a full
        # join session -- op 2, 13, 37, 8, 40, 41, 43, 4 and 3 all appear -- and it
        # contains zero op 14 frames, while its op 37 subscriptions carry only
        # typing/activities/threads and no channel ranges. Sending a frame the
        # observed client never sends during the same activity is a tell, so the
        # sender is kept but not used unless explicitly enabled.
        if gw and load_config().get("send_guild_member_ranges", False):
            gw.subscribe_guild_ranges(guild_id, target_ch, [[0, 99]])

        # 7. WebSocket Opcode 13: Register active UI channel focus
        if gw:
            gw.select_channel(target_ch)

        # 8. Track channel open event for /api/v9/science telemetry
        if telemetry:
            telemetry.track("channel_opened", {
                "channel_id": str(target_ch),
                "channel_type": 0,
                "guild_id": str(guild_id),
            })

        # 9. HTTP REST: Query channel application command index & simulate loading viewport messages (14 limit)
        session.get(f"{API}/channels/{target_ch}/application-command-index")
        time.sleep(random.uniform(0.3, 0.8))
        r_msgs = session.get(f"{API}/channels/{target_ch}/messages?limit=14")
        time.sleep(random.uniform(1.2, 2.5))

        # 10. Acknowledge messages / clear unread badge matching live client capture (Item [364], [373], [399])
        if r_msgs.status_code == 200:
            msgs_data = r_msgs.json()
            if msgs_data and isinstance(msgs_data, list):
                # WebSocket Opcode 8: resolve the authors of the messages just
                # rendered. Every op 8 in the capture takes this form -- concrete
                # user_ids with presences:false -- and never a blank query, so it
                # can only be sent once there are ids to ask about.
                if gw:
                    author_ids = list(dict.fromkeys(
                        m.get("author", {}).get("id")
                        for m in msgs_data
                        if isinstance(m, dict) and m.get("author", {}).get("id")
                    ))[:24]
                    if author_ids:
                        gw.request_guild_members(guild_id, user_ids=author_ids)

                latest_msg_id = msgs_data[0].get("id")
                if latest_msg_id:
                    try:
                        session.post(
                            f"{API}/channels/{target_ch}/messages/{latest_msg_id}/ack",
                            json={"token": None, "last_viewed": random.randint(3000, 5000), "flags": 1}
                        )
                        # Guild level acknowledgment (Item [101], [246])
                        session.post(
                            f"{API}/guilds/{guild_id}/ack/4/{latest_msg_id}",
                            json={}
                        )
                    except Exception:
                        pass

        # Wait a bit to mimic reading
        time.sleep(random.uniform(2.0, 4.0))
    except Exception as e:
        log.debug(f"Failed human browsing simulation: {e}")

# Sessions were only ever dropped on error, so every token used in a run kept a
# StealthSession, a gateway WebSocket with its heartbeat and receive threads, and
# a telemetry flush thread for the life of the process. Across a large token file
# that is hundreds of threads and open sockets -- and it puts every one of those
# accounts online simultaneously, which is itself a pattern no human produces.
token_session_last_used = {}


def touch_session(token):
    """Mark a token's session as just used, for eviction ordering."""
    with sessions_lock:
        token_session_last_used[token] = time.time()


def _evict_idle_sessions(keep_token=None):
    """Close the least recently used sessions above the configured cap."""
    cfg = load_config()
    try:
        # Default to the size of the worker grid. A cap below the number of
        # active workers evicts a session that is about to be used again on the
        # next turn, so every cycle tears down and rebuilds gateways for no
        # reason. This is a safety net now that a burst ends with go_offline().
        grid = max(1, int(cfg.get("threads", 1))) * max(1, int(cfg.get("workers_per_thread", 9)))
        limit = int(cfg.get("max_live_sessions", grid))
    except (TypeError, ValueError):
        limit = 12
    if limit <= 0:
        return

    victims = []
    with sessions_lock:
        if len(token_sessions) <= limit:
            return
        ordered = sorted(token_sessions.keys(),
                         key=lambda t: token_session_last_used.get(t, 0.0))
        for tok in ordered:
            # token_sessions shrinks as entries are popped, so compare against it
            # directly; also subtracting len(victims) would double-count each one.
            if len(token_sessions) <= limit:
                break
            if tok == keep_token:
                continue
            victims.append((tok, token_sessions.pop(tok)))
            token_session_last_used.pop(tok, None)

    # Close outside the lock: shutting down a gateway does network I/O.
    for tok, cached_val in victims:
        log.debug(f"Evicting idle session for {format_token_id(tok)} (cap {limit})")
        _cleanup_session(cached_val)


def go_offline(token):
    """Close this token's gateway, session and telemetry thread.

    Real Discord sessions are short. In the two captures, all 13 page loads --
    each with exactly one gateway connection -- lasted between 0.2 and 4.1
    minutes, median 0.4; even the launch that made 154 requests was over in 1.2
    minutes. Nothing keeps a client_launch_id alive for hours.

    Holding a gateway open between bursts would do exactly that, and it also
    leaves every account showing online continuously. A fleet of accounts sharing
    a handful of exit IPs and never once going offline is a pattern no set of
    real users produces, whatever their fingerprints say.
    """
    with sessions_lock:
        cached = token_sessions.pop(token, None)
        token_session_last_used.pop(token, None)
    if cached:
        _cleanup_session(cached)
    try:
        from utils.browser_joiner import close_browser_session
        close_browser_session(token)
    except Exception:
        pass
    return bool(cached)


def _cleanup_session(cached_val):
    """Cleanly close Gateway WebSocket and flush/stop ScienceTelemetry when evicting a token session."""
    if not cached_val:
        return
    try:
        # Close Gateway WS
        if len(cached_val) > 2 and cached_val[2]:
            try:
                cached_val[2].close()
            except Exception:
                pass
        # Stop ScienceTelemetry thread
        if len(cached_val) > 5 and cached_val[5]:
            try:
                cached_val[5].stop()
            except Exception:
                pass
    except Exception as e:
        log.debug(f"Session cleanup error: {e}")

def save_joined_token(token, status, invite_code, guild_id=None, guild_name=None, logger=None):
    os.makedirs("output", exist_ok=True)
    short_token = format_token_id(token)

    if status in ("invalid", "locked", "limited"):
        # Terminate and clean up any active session, gateway, or telemetry thread
        with sessions_lock:
            cached_sess = token_sessions.pop(token, None)
        if cached_sess:
            _cleanup_session(cached_sess)
        # Terminate and clean up any open browser instance
        try:
            from utils.browser_joiner import close_browser_session
            close_browser_session(token)
        except Exception:
            pass

    if status == "Joined":
        STATS["unlocked"] += 1
        log_fn = log.info
        gid = str(guild_id) if guild_id else "Unknown"
        gname = str(guild_name) if guild_name else "Unknown"
        write_unique_line("output/joined.txt", f"{token} | {gid} | {gname}")
    elif status == "Already Member":
        log_fn = log.info
    elif status == "min_members_limit":
        log_fn = log.debug
    elif status == "locked":
        STATS["locked"] += 1
        log_fn = log.warning
        write_unique_line("output/locked.txt", token)
    elif status == "invalid":
        STATS["invalid"] += 1
        log_fn = log.error
        write_unique_line("output/invalid.txt", token)
    elif status == "invalid_invite":
        log_fn = log.warning
        if invite_code:
            write_unique_line("output/failed_invites.txt", f"{invite_code} | Unknown / Expired Invite")
    elif status == "limited":
        STATS["rate"] += 1
        log_fn = log.warning
        write_unique_line("output/limited.txt", token)
    elif status in ("failed_captcha", "captcha_skip", "captcha_exhausted"):
        STATS["rate"] += 1
        log_fn = log.warning
    elif status in ("captcha_retry", "retry", "backing_off"):
        log_fn = log.info
    elif status == "action_blocked":
        log_fn = log.warning
    else:
        STATS["error"] += 1
        log_fn = log.error
        if invite_code and status not in ("failed", "error", "captcha_retry", "retry", "backing_off"):
            write_unique_line("output/failed_invites.txt", f"{invite_code} | {status}")

    arrow = f"{Fore.LIGHTBLACK_EX}→{Style.RESET_ALL}"
    token_str = f"{Fore.CYAN}{short_token}{Style.RESET_ALL}"
    inv_str = f"{Fore.YELLOW}{invite_code}{Style.RESET_ALL}"

    if status == "Joined":
        log_msg = f"{token_str} {arrow} {Fore.GREEN}{Style.BRIGHT}Joined{Style.RESET_ALL} ({inv_str})"
    elif status == "Already Member":
        log_msg = f"{token_str} {arrow} {Fore.CYAN}Already in Server{Style.RESET_ALL} ({inv_str})"
    elif status == "min_members_limit":
        log_msg = f"{token_str} {arrow} {Fore.LIGHTBLACK_EX}Skipped (Min Members Limit){Style.RESET_ALL} ({inv_str})"
    elif status == "locked":
        log_msg = f"{token_str} {arrow} {Fore.LIGHTMAGENTA_EX}{Style.BRIGHT}Account Locked{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}(HTTP 403){Style.RESET_ALL}"
    elif status == "limited":
        log_msg = f"{token_str} {arrow} {Fore.LIGHTYELLOW_EX}{Style.BRIGHT}Temporarily Limited by Discord Safety{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}(Quarantined){Style.RESET_ALL} ({inv_str})"
    elif status == "invalid":
        log_msg = f"{token_str} {arrow} {Fore.LIGHTRED_EX}{Style.BRIGHT}Invalid Token{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}(HTTP 401){Style.RESET_ALL}"
    elif status in ("failed_captcha", "captcha_skip", "captchaed"):
        log_msg = f"{token_str} {arrow} {Fore.YELLOW}Captcha Skipped / Rate Limit{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}(HTTP 429){Style.RESET_ALL} ({inv_str})"
    elif status in ("captcha_retry", "retry", "backing_off"):
        log_msg = f"{token_str} {arrow} {Fore.YELLOW}Challenge Expired › Scheduled for retry{Style.RESET_ALL} ({inv_str})"
    elif status == "invalid_invite":
        log_msg = f"{token_str} {arrow} {Fore.YELLOW}Invalid / Expired Invite{Style.RESET_ALL} ({inv_str})"
    elif status == "action_blocked":
        log_msg = f"{token_str} {arrow} {Fore.LIGHTRED_EX}Join Blocked by Discord Security{Style.RESET_ALL} ({inv_str})"
    else:
        log_msg = f"{token_str} {arrow} {Fore.LIGHTRED_EX}Failed{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}(status={status}){Style.RESET_ALL} ({inv_str})"

    log_fn(log_msg)

def _apply_captcha_headers(session, cap_token, rqtoken, session_id):
    # Always drop stale captcha headers first so a previous round's (now
    # consumed) rqtoken can never leak into this submission.
    _clear_captcha_headers(session)
    headers = {"x-captcha-key": cap_token}
    # The real client omits these headers entirely when the challenge did not
    # provide them. Sending them with an empty value is both a fingerprint and a
    # reason for Discord to reject the submission outright.
    if rqtoken:
        headers["x-captcha-rqtoken"] = rqtoken
    if session_id:
        headers["x-captcha-session-id"] = session_id
    session.headers.update(headers)

def _clear_captcha_headers(session):
    for h in ("x-captcha-key", "x-captcha-rqtoken", "x-captcha-session-id"):
        session.headers.pop(h, None)

# Discord echoes back why a submitted captcha token was refused. Distinguishing
# "your token was bad" from "I want another captcha" is the difference between
# retrying usefully and burning solves in a loop.
_CAPTCHA_REJECT_CODES = {
    "captcha-invalid",
    # Observed live: Discord returns HTTP 400 with captcha_key ["invalid-response"]
    # when hCaptcha's siteverify refuses the submitted token.
    "invalid-response",
    "invalid-input-response",
    "invalid-captcha",
    "response-already-used",
    "response-already-used-by-another-user",
    "sitekey-secret-mismatch",
    "bad-rqdata",
    "rqdata-invalid",
    "expired-captcha",
    "challenge-expired",
    "timeout-or-duplicate",
}

def _captcha_reject_reason(res_json):
    """Extract Discord's stated reason for re-challenging, if any."""
    if not isinstance(res_json, dict):
        return None
    keys = res_json.get("captcha_key")
    if isinstance(keys, str):
        keys = [keys]
    if not isinstance(keys, list):
        return None
    return [str(k) for k in keys] or None

def _captcha_token_was_rejected(res_json):
    """True when the new challenge is because our token was refused (not merely required)."""
    reasons = _captcha_reject_reason(res_json) or []
    return any(r.lower() in _CAPTCHA_REJECT_CODES for r in reasons)

def _record_captcha_challenge(token, invite_code, res, res_json, round_no):
    """Append the raw re-challenge response to log/captcha_debug.log.

    Discord's reason code is the only reliable way to tell a rejected token from
    a plain re-challenge; without it this failure mode is pure guesswork.
    """
    try:
        os.makedirs("log", exist_ok=True)
        safe = {
            k: v
            for k, v in (res_json or {}).items()
            if k in ("captcha_key", "captcha_sitekey", "captcha_service", "code", "message", "retry_after")
        }
        with file_write_lock:
            with open("log/captcha_debug.log", "a", encoding="utf-8") as f:
                f.write(
                    f"{time.strftime('%Y-%m-%d %H:%M:%S')} | {format_token_id(token)} | "
                    f"invite={invite_code} | round={round_no} | "
                    f"status={res.status_code if res else 'None'} | {json.dumps(safe)}\n"
                )
    except Exception as e:
        log.debug(f"Failed to record captcha challenge: {e}")

def _build_solve_context(session, profile, timezone=None, ua=None, hardware=None):
    """Describe the submitting browser so the solver can mirror it exactly.

    hCaptcha fingerprints the browser that solves the challenge. Any mismatch
    between that browser and the one that submits the token (OS, Chrome version,
    client hints, timezone) tanks the token's risk score, and Discord answers a
    low-scoring token with a brand new challenge rather than an error.

    `hardware` is the session's telemetry hardware profile (GPU, threads, RAM,
    screen); the solver could not derive it itself (utils is not importable
    from the solver process) and fell back to one fixed GPU for every account.
    """
    ctx = {}
    ua = ua or (profile.get("user_agent") if profile else None)
    if not ua and session is not None:
        ua = session.headers.get("user-agent")
    ctx["user_agent"] = ua or USER_AGENT
    if hardware:
        ctx["hardware"] = dict(hardware)

    if profile:
        # The exact sec-ch-ua string the REST session sends (GREASE brand,
        # order and version rotate per major); the solver used to hardcode the
        # Chrome 149 form for every major.
        if profile.get("sec_ch_ua"):
            ctx["sec_ch_ua"] = profile["sec_ch_ua"]
        # Reuse the exact platform string the session already advertises in its
        # `sec-ch-ua-platform` header, so the solver browser and the join request
        # cannot disagree.
        platform = (profile.get("sec_ch_ua_platform") or "").strip('"')
        if platform:
            ctx["platform"] = platform

        os_version = str(profile.get("os_version") or "")
        if platform == "Windows":
            # Windows 11 builds (22000+, 22621, 22631, 26100) advertise platformVersion >= 13.0.0 (typically 15.0.0)
            if any(b in os_version for b in ("26100", "22631", "22621", "22000", "11")):
                ctx["platform_version"] = "15.0.0"
            else:
                ctx["platform_version"] = "10.0.0"
        elif platform == "macOS" and os_version:
            ctx["platform_version"] = os_version
        elif platform == "Linux" and os_version:
            ctx["platform_version"] = os_version

    if timezone:
        ctx["timezone"] = timezone
    return ctx

def _solve_join_captcha(solver_type, solver_api_key, sitekey, rqdata, proxy, token,
                        solve_ctx, max_retries=5, label="captcha"):
    """Solve one hCaptcha challenge.

    Returns (cap_token, burned). `burned` is True when the challenge itself is
    dead — the extension answered wrong and hCaptcha replaced it — meaning this
    rqdata can never produce an acceptable token and the caller must fetch a
    fresh challenge from Discord rather than retry.

    Deliberately does NOT rotate the proxy between attempts. The challenge is
    issued to a specific IP, and the account's gateway websocket and cookies are
    already bound to that IP — solving or submitting from a different one is
    itself a reason for Discord to issue another captcha.
    """
    
    
    import concurrent.futures

    cfg = load_config()
    solve_timeout = float(cfg.get("captcha_timeout", 120))
    start_solve_time = time.time()

    for cap_attempt in range(1, max_retries + 1):
        elapsed = time.time() - start_solve_time
        if elapsed >= solve_timeout:
            log.warning(
                f"{label.capitalize()} solve hard timeout reached ({solve_timeout}s) for token {format_token_id(token)}."
            )
            return "timeout", False

        if cap_attempt > 1:
            log.info(
                f"Retrying {label} solve for token {format_token_id(token)} "
                f"(Attempt {cap_attempt}/{max_retries})..."
            )

        remaining_time = max(1.0, solve_timeout - (time.time() - start_solve_time))
        # No `with` block: ThreadPoolExecutor.__exit__ joins the worker, so the
        # timeout below only fired after solve() had returned on its own (up to
        # the solver's full 120s poll) and the "hard timeout" was never a timeout.
        executor = concurrent.futures.ThreadPoolExecutor(max_workers=1)
        try:
            future = executor.submit(
                DisabledChallengeClient(
                    solver_type,
                    "https://discord.com/",
                    solver_api_key,
                ).solve,
                rqdata=rqdata,
                user_agent=solve_ctx.get("user_agent"),
                proxy=proxy,
                sitekey=sitekey,
                platform=solve_ctx.get("platform"),
                platform_version=solve_ctx.get("platform_version"),
                timezone=solve_ctx.get("timezone"),
                sec_ch_ua=solve_ctx.get("sec_ch_ua"),
                hardware=solve_ctx.get("hardware"),
            )
            cap_token = future.result(timeout=remaining_time)
            if cap_token:
                return cap_token, False
        except concurrent.futures.TimeoutError:
            log.warning(
                f"{label.capitalize()} solve timed out after {solve_timeout}s for token {format_token_id(token)}."
            )
            return "timeout", False
        except RuntimeError as e:
            # The token would be bound to a challenge Discord has already
            # replaced; solving the SAME rqdata again can only fail again (each
            # retry opened a browser and burned a solver credit). The caller
            # refreshes rqdata by re-POSTing the join, which is the only retry
            # that can work.
            log.info(
                f"Solver challenge replaced ({e.challenges or '?'} challenges processed); "
                f"refreshing the challenge instead of re-solving it."
            )
            return None, True
        except Exception as e:
            log.debug(f"{label.capitalize()} solve attempt {cap_attempt}/{max_retries} retry: {e}")
        finally:
            # Never join: on timeout the worker is abandoned (the solver's own
            # 120s cap ends it) instead of holding this thread until it returns.
            executor.shutdown(wait=False, cancel_futures=True)
        time.sleep(1.5)
    return None, False

def _handle_rate_limit(res_json, status_code):
    if status_code != 429:
        return False
    # If the 429 is a captcha challenge, do NOT handle it here (pass it immediately to captcha solver)
    if res_json.get("captcha_sitekey") or res_json.get("captcha_rqdata"):
        return False
    # retry_after is untrusted server input. Coerce it and clamp it: a null or
    # non-numeric value used to raise inside the f-string and in sleep(), and an
    # oversized value would park the worker indefinitely.
    try:
        retry_after = float(res_json.get("retry_after", 60))
    except (TypeError, ValueError):
        retry_after = 60.0
    retry_after = min(max(retry_after, 0.0), MAX_RETRY_AFTER)
    log.warning(
        f"{Fore.YELLOW}rate limited{Style.RESET_ALL}, "
        f"waiting {Fore.YELLOW}{retry_after:.0f}s{Style.RESET_ALL}..."
    )
    time.sleep(retry_after + 1)
    return True

def _post_json(session, url, payload, retries=1, backoff=1.0, resend_after_ratelimit=True):
    """POST JSON, optionally re-sending once after a rate limit.

    `resend_after_ratelimit=False` is required when the request carries a captcha
    token: captcha keys are single-use, so a silent re-POST would submit an
    already-consumed key and earn a fresh challenge instead of a join.
    """
    last_exc = None
    for attempt in range(retries + 1):
        try:
            res = session.post(url, json=payload, headers=BODY_ORIGIN)
            try:
                data = res.json()
            except Exception:
                data = {}
            if _handle_rate_limit(data, res.status_code) and resend_after_ratelimit:
                res = session.post(url, json=payload, headers=BODY_ORIGIN)
                try:
                    data = res.json()
                except Exception:
                    data = {}
            return res, data
        except Exception as e:
            last_exc = e
            if attempt < retries:
                time.sleep(backoff)
    if last_exc:
        log.debug(
            f"POST JSON failed {Fore.WHITE}→{Style.RESET_ALL} "
            f"type={Fore.CYAN}{type(last_exc).__name__}{Style.RESET_ALL} "
            f"error={Fore.LIGHTRED_EX}{last_exc}{Style.RESET_ALL}"
        )
    return None, None

def _solve_captcha(solver_type, solver_api_key, rqdata, proxy, token, website_url, session=None):
    if not solver_type or not solver_api_key:
        log.warning(
            f"Captcha encountered, but solver is disabled or not configured. "
            f"token={Fore.CYAN}{format_token_id(token)}{Style.RESET_ALL}"
        )
        return None, "solver_disabled"

    log.info(
        f"Solving captcha {Fore.WHITE}→{Style.RESET_ALL} "
        f"token={Fore.CYAN}{format_token_id(token)}{Style.RESET_ALL}"
    )
    start = time.time()
    cap_token = None
    max_retries = 3
    for attempt in range(1, max_retries + 1):
        if attempt > 1:
            try:
                from utils.proxy import ProxyManager
                new_p = ProxyManager().get_proxy()
                if new_p and new_p != proxy:
                    proxy = new_p
                    if session:
                        p_url = format_proxy_url(proxy)
                        if p_url:
                            session.proxies = {"http": p_url, "https": p_url}
                        else:
                            session.proxies = {}
                    clean_p = proxy.split("@")[-1] if "@" in proxy else proxy
                    log.warning(f"Rate limited / solver failed. Switched proxy for retry (Attempt {attempt}/{max_retries}) → {clean_p}")
            except Exception as pe:
                log.debug(f"Failed to rotate proxy: {pe}")
        try:
            cap_ua = session.headers.get("user-agent", USER_AGENT) if session else USER_AGENT
            cap_token = DisabledChallengeClient(solver_type, website_url, solver_api_key).solve(
                rqdata=rqdata,
                user_agent=cap_ua,
                proxy=proxy,
            )
            if cap_token:
                break
        except Exception as e:
            log.error(f"{Fore.LIGHTRED_EX}Captcha solve attempt {attempt}/{max_retries} error={type(e).__name__}: {e}{Style.RESET_ALL}")
        time.sleep(1.5)

    if not cap_token:
        return None, "solver_error"

    log.info(
        f"Captcha solved {Fore.WHITE}→{Style.RESET_ALL} "
        f"{Fore.GREEN}{time.time() - start:.1f}s{Style.RESET_ALL}"
    )
    return cap_token, None

def bypass_verification_bots(session, token, solver_type=None, solver_api_key=None, proxy=None):
    if not is_verification_enabled():
        return
    short = format_token_id(token)
    try:
        # Give bots enough time to send their DM after join
        time.sleep(random.uniform(5.0, 9.0))

        r = session.get(f"{API}/users/@me/channels")
        if r.status_code != 200:
            return
        dms = r.json()

        dc_done = False
        vc_done = False

        for dm in dms:
            recipients = dm.get("recipients", [])

            # --- Double Counter check ---
            if not dc_done:
                is_dc = any(
                    "double counter" in rec.get("username", "").lower()
                    or rec.get("id") == "538228399581560833"
                    for rec in recipients
                )
                if is_dc:
                    dm_channel_id = dm["id"]
                    r_msg = session.get(f"{API}/channels/{dm_channel_id}/messages?limit=5")
                    if r_msg.status_code == 200:
                        for msg in r_msg.json():
                            content = msg.get("content", "")
                            urls = re.findall(r'https?://[^\s]+', content)
                            for url in urls:
                                if "doublecounter" in url or "dcounter" in url:
                                    log.info(f"Double-Counter link detected: {url}. Bypassing...")
                                    try:
                                        clean_dc_headers = {
                                            k: v for k, v in session.headers.items()
                                            if not k.lower().startswith("x-") and k.lower() != "authorization"
                                        }
                                        res_dc = session.get(url, headers=clean_dc_headers)
                                        log.info(f"Double-Counter bypass response: {res_dc.status_code}")
                                    except Exception as e:
                                        log.debug(f"Double-Counter request failed: {e}")
                                    dc_done = True
                                    break
                        if dc_done:
                            time.sleep(random.uniform(1.5, 3.0))

            # --- Vaultcord check ---
            if not vc_done and dm.get("type") == 1 and _is_verification_dm(dm):
                dm_id = dm["id"]
                r_msgs = session.get(f"{API}/channels/{dm_id}/messages?limit=10")
                if r_msgs.status_code == 200:
                    for msg in r_msgs.json():
                        if not _is_vaultcord_msg(msg):
                            continue
                        url = _extract_verify_url_from_msg(msg)
                        if not url:
                            continue
                        log.info(f"Vaultcord verify detected for {short} → {url[:80]}")
                        time.sleep(random.uniform(1.5, 4.0))
                        try:
                            if "discord.com/oauth2/authorize" in url:
                                _complete_oauth2_verify(session, token, url, solver_type, solver_api_key, proxy)
                            else:
                                res = session.get(url, allow_redirects=True)
                                if res.status_code in (200, 201, 204, 302):
                                    log.info(f"{Fore.GREEN}Vaultcord verified for {short} (HTTP {res.status_code}).{Style.RESET_ALL}")
                                else:
                                    log.debug(f"Vaultcord direct link failed for {short}: {res.status_code} {res.text[:200]}")
                        except Exception as e:
                            log.debug(f"Vaultcord link error for {short}: {e}")
                        vc_done = True
                        break

            if dc_done and vc_done:
                break

    except Exception as e:
        log.debug(f"Verification bot bypass error: {e}")


def bypass_double_counter(session, token):
    if not is_verification_enabled():
        return
    try:
        # Search DM channels list for Double Counter bot
        r = session.get(f"{API}/users/@me/channels")
        if r.status_code != 200:
            return
        dms = r.json()
        for dm in dms:
            recipients = dm.get("recipients", [])
            is_dc = False
            for rec in recipients:
                if "double counter" in rec.get("username", "").lower() or rec.get("id") == "538228399581560833":
                    is_dc = True
                    break
            
            if is_dc:
                dm_channel_id = dm["id"]
                # Fetch recent messages from the bot channel
                r_msg = session.get(f"{API}/channels/{dm_channel_id}/messages?limit=5")
                if r_msg.status_code == 200:
                    for msg in r_msg.json():
                        content = msg.get("content", "")
                        urls = re.findall(r'https?://[^\s]+', content)
                        for url in urls:
                            if "doublecounter" in url or "dcounter" in url:
                                log.info(f"Double-Counter link detected: {url}. Bypassing using residential proxy...")
                                try:
                                    # Strip Discord auth/experiments headers to avoid leaking credentials to Double-Counter API
                                    clean_dc_headers = {k: v for k, v in session.headers.items() if not k.lower().startswith("x-") and k.lower() != "authorization"}
                                    res_dc = session.get(url, headers=clean_dc_headers)
                                    log.info(f"Double-Counter bypass response status: {res_dc.status_code}")
                                except Exception as e:
                                    log.debug(f"Double-counter verification request failed: {e}")
                                return
    except Exception as e:
        log.debug(f"Double-Counter check error: {e}")

def bypass_welcome_screen(session, guild_id):
    if not is_verification_enabled():
        return
    try:
        welcome_url = f"{API}/guilds/{guild_id}/welcome-screen"
        r = session.get(welcome_url)
        if r.status_code == 200:
            welcome_data = r.json()
            if welcome_data.get("enabled"):
                log.info(f"Welcome screen detected for guild {guild_id}. Simulating rules and channels acknowledgment...")
                # Submit acknowledgment settings
                ack_url = f"{API}/guilds/{guild_id}/requests/@me"
                session.patch(ack_url, json={"welcome_screen_viewed": True})
    except Exception as e:
        log.debug(f"Failed welcome screen bypass: {e}")

def click_component_button(session, guild_id, channel_id, message_id, application_id, custom_id, gw_session_id=None):
    try:
        url = f"{API}/interactions"
        payload = {
            "type": 3,
            "nonce": str(random.randint(100000000000000000, 999999999999999999)),
            "guild_id": guild_id,
            "channel_id": channel_id,
            "message_id": message_id,
            "application_id": application_id,
            "session_id": gw_session_id or "".join(random.choices(string.ascii_lowercase + string.digits, k=32)),
            "data": {
                "component_type": 2,
                "custom_id": custom_id
            }
        }
        res = session.post(url, json=payload, headers=BODY_ORIGIN)
        return res.status_code in (200, 201, 204)
    except Exception as e:
        log.debug(f"Failed clicking button component: {e}")
    return False

def find_best_verification_reaction(msg):
    reactions = msg.get("reactions", [])
    if not reactions:
        return None

    # Gather text from message content and embeds
    text_content = (msg.get("content") or "").lower()
    for embed in msg.get("embeds", []):
        text_content += " " + (embed.get("title") or "").lower()
        text_content += " " + (embed.get("description") or "").lower()
        for field in embed.get("fields", []):
            text_content += " " + (field.get("name") or "").lower()
            text_content += " " + (field.get("value") or "").lower()

    # Map text keywords to possible emoji names or characters
    keyword_emoji_map = {
        "lock": ["🔒", "🔓", "lock"],
        "key": ["🔑", "key"],
        "check": ["✅", "✔", "check", "tick"],
        "verify": ["✅", "✔", "verify"],
        "agree": ["✅", "✔", "agree"],
        "accept": ["✅", "✔", "accept"],
        "thumbs": ["👍", "thumbsup"],
        "yes": ["👍", "✅"],
        "heart": ["❤️", "💖", "heart"],
        "star": ["⭐", "star"],
        "bell": ["🔔", "bell"],
        "shield": ["🛡️", "shield"],
        "cross": ["❌", "cross"],
        "cancel": ["❌", "cancel"]
    }

    # 1. Search for explicit keywords in the instruction text
    target_emojis = []
    for kw, emojis in keyword_emoji_map.items():
        if kw in text_content:
            target_emojis.extend(emojis)

    if target_emojis:
        # Try to find a reaction matching the keyword emojis
        for react in reactions:
            emoji_info = react.get("emoji", {})
            name = (emoji_info.get("name") or "").lower()
            emoji_id = emoji_info.get("id")
            
            for target in target_emojis:
                if target in name or (emoji_id and target in str(emoji_id)):
                    return react
                if target == name:
                    return react

    return None

def check_verification_channels(session, guild_id):
    if not is_verification_enabled():
        return
    try:
        # Fetch all channels of the guild
        r_channels = session.get(f"{API}/guilds/{guild_id}/channels")
        if r_channels.status_code != 200:
            return
        
        channels = r_channels.json()
        target_keywords = ["verify", "verification", "welcome", "rules", "start", "landing", "get-started", "agree", "giveaway", "events", "gw", "unlock", "join"]
        
        # Filter channels matching verification keywords
        verify_channels = []
        for ch in channels:
            name = ch.get("name", "").lower()
            ch_type = ch.get("type")
            # Ensure it is a text channel
            if ch_type == 0 and any(keyword in name for keyword in target_keywords):
                verify_channels.append(ch["id"])
        
        reactions_done = 0

        # Scan messages in filtered verification channels
        for ch_id in verify_channels:
            if reactions_done >= 10:
                break

            r_msg = session.get(f"{API}/channels/{ch_id}/messages?limit=10")
            if r_msg.status_code != 200:
                continue
            
            messages = r_msg.json()
            for msg in messages:
                if reactions_done >= 10:
                    break

                message_id = msg.get("id")
                author = msg.get("author", {})
                author_id = author.get("id")
                is_bot = author.get("bot", False)
                components = msg.get("components", [])
                reactions = msg.get("reactions", [])
                
                # 1. Button verification bypass
                if components:
                    for comp in components:
                        # Row container type
                        if comp.get("type") == 1:
                            for sub_comp in comp.get("components", []):
                                # Button type (type 2)
                                if sub_comp.get("type") == 2:
                                    label = sub_comp.get("label", "").lower()
                                    custom_id = sub_comp.get("custom_id", "")
                                    
                                    # Skip auxiliary info buttons like "Why?", "What is this?", "Faq", etc.
                                    exclude_words = ["why", "what", "info", "help", "faq"]
                                    if any(ex in label for ex in exclude_words) or any(ex in custom_id.lower() for ex in exclude_words):
                                        continue

                                    if custom_id and any(word in label or word in custom_id.lower() for word in ["verify", "agree", "rules", "start", "accept", "unlock"]):
                                        log.info(f"Interaction button verification detected. Clicking button label='{sub_comp.get('label')}'...")
                                        success = click_component_button(session, guild_id, ch_id, message_id, author_id, custom_id)
                                        if success:
                                            log.info("Successfully clicked button verification.")
                                            reactions_done += 1
                                            time.sleep(random.uniform(3.0, 6.0))
                
                # 2. Emoji verification bypass (Reaction Role check)
                if reactions:
                    best_react = find_best_verification_reaction(msg)
                    if best_react:
                        emoji_info = best_react.get("emoji", {})
                        emoji_name = emoji_info.get("name")
                        emoji_id = emoji_info.get("id")
                        if emoji_name:
                            log.info(f"Intelligent reaction verification detected. Reacting with {emoji_name}...")
                            emoji_str = emoji_name if not emoji_id else f"{emoji_name}:{emoji_id}"
                            import urllib.parse
                            encoded_emoji = urllib.parse.quote(emoji_str)
                            react_url = f"{API}/channels/{ch_id}/messages/{message_id}/reactions/{encoded_emoji}/@me?location=Message%20Inline%20Button&type=0"
                            r_react = session.put(react_url)
                            if r_react.status_code in (200, 201, 204):
                                log.info(f"Successfully reacted to emoji verification.")
                                reactions_done += 1
                                time.sleep(random.uniform(3.0, 6.0))
                            else:
                                log.debug(f"Failed reacting: {r_react.status_code} - {r_react.text}")
                                try:
                                    res_data = r_react.json()
                                    if r_react.status_code == 403 and res_data.get("code") == 50009:
                                        log.warning("Verification level too high to add reactions. Skipping channel.")
                                        break
                                except Exception:
                                    pass
    except Exception as e:
        log.debug(f"Error checking verification channels: {e}")

def bypass_rules_and_onboarding(session, guild_id):
    if not is_verification_enabled():
        return
    try:
        # Rules Screening Verification (Gatekeeper Check)
        form_url = f"{API}/guilds/{guild_id}/member-verification?with_guild=true"
        r = session.get(form_url)
        if r.status_code == 200:
            form_data = r.json()
            if form_data.get("form_fields"):
                log.info(f"Submitting Rules Screening verification for guild {guild_id}...")
                # Simulate a human reading through the rules before accepting
                read_delay = random.uniform(8.0, 20.0)
                log.debug(f"Simulating rules read delay of {read_delay:.1f}s...")
                time.sleep(read_delay)
                submit_url = f"{API}/guilds/{guild_id}/requests/@me"
                fields = form_data["form_fields"]
                for field in fields:
                    if field.get("field_type") == "TERMS":
                        field["response"] = True
                
                payload = {
                    "form_fields": fields,
                    "version": form_data.get("version")
                }
                res = session.put(submit_url, json=payload)
                if res.status_code in (200, 201, 204):
                    log.info(f"Rules Screening successfully bypassed.")
                else:
                    log.debug(f"Rules screening submit status: {res.status_code} - {res.text}")

        # Member Onboarding Bypass
        onboard_url = f"{API}/guilds/{guild_id}/onboarding"
        r_onboard = session.get(onboard_url)
        if r_onboard.status_code == 200:
            onboard_data = r_onboard.json()
            if onboard_data.get("prompts"):
                log.info(f"Submitting onboarding choices for guild {guild_id}...")
                # Simulate a human scrolling through onboarding prompts
                onboard_read_delay = random.uniform(5.0, 12.0)
                log.debug(f"Simulating onboarding read delay of {onboard_read_delay:.1f}s...")
                time.sleep(onboard_read_delay)
                onboarding_responses = []
                prompts_seen = {}
                responses_seen = {}
                now_ms = int(time.time() * 1000)

                for prompt in onboard_data.get("prompts", []):
                    prompts_seen[prompt["id"]] = now_ms
                    for opt in prompt.get("options", []):
                        responses_seen[opt["id"]] = now_ms

                    if prompt.get("options"):
                        opts = prompt["options"]
                        # Handle single-select vs multi-select naturally
                        if prompt.get("single_select", True):
                            onboarding_responses.append(random.choice(opts)["id"])
                        else:
                            k = min(len(opts), random.randint(1, min(3, len(opts))))
                            onboarding_responses.extend([opt["id"] for opt in random.sample(opts, k)])
                
                submit_onboard_url = f"{API}/guilds/{guild_id}/onboarding-responses"
                payload = {
                    "onboarding_responses": onboarding_responses,
                    "onboarding_prompts_seen": prompts_seen,
                    "onboarding_responses_seen": responses_seen,
                }
                res_onboard = session.post(
                    submit_onboard_url,
                    json=payload,
                    headers={
                        "Referer": f"https://discord.com/channels/{guild_id}/onboarding"
                    }
                )
                if res_onboard.status_code in (200, 201, 204):
                    log.info(f"Onboarding flow successfully bypassed.")
                else:
                    log.debug(f"Onboarding submit status: {res_onboard.status_code} - {res_onboard.text}")
    except Exception as e:
        log.debug(f"Failed rules verification/onboarding bypass: {e}")

@releases_guild_claims
def join_server(
    token,
    invite_code,
    proxy=None,
    current_num=1,
    solver_type=None,
    solver_api_key=None,
    max_retries=3,
    max_guild_limit=80,
    min_member_count=0,
):
    from utils.core import worker_id_var
    worker_id_var.set(f"Thread {current_num}")

    proxy_label = proxy.split('@')[-1] if proxy else 'direct'
    log.info(
        f"Session active {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} "
        f"proxy={Fore.CYAN}{proxy_label}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}│{Style.RESET_ALL} "
        f"token={Fore.CYAN}{format_token_id(token)}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}│{Style.RESET_ALL} "
        f"target={Fore.YELLOW}{invite_code}{Style.RESET_ALL}"
    )

    # Early check using public invite metadata to avoid warming up the session/gateway if already joined globally
    cfg = load_config()
    if cfg.get("early_guild_check", True):
        try:
            temp_session = StealthSession(timeout=default_request_timeout())
            if proxy:
                proxy_url = format_proxy_url(proxy)
                if proxy_url:
                    temp_session.proxies = {"http": proxy_url, "https": proxy_url}
                    if "127.0.0.1" in proxy_url or "localhost" in proxy_url or "8080" in proxy_url:
                        temp_session.verify = False
            
            build_num = get_build_number(proxy)
            temp_profile = get_random_profile(build_num, token=token)
            # Same complete XHR header set and TLS profile as the real session:
            # this request leaves the same IP moments before it, so a partial
            # header set on a Chrome 136 handshake was a second fingerprint.
            temp_session.headers.update(
                build_headers(None, temp_profile["super_properties"],
                              detect_timezone(proxy, user_agent=temp_profile["user_agent"]),
                              temp_profile)
            )
            apply_tls_profile(temp_session, temp_profile)
            metadata = fetch_invite_metadata(temp_session, invite_code)
            if metadata:
                if metadata.get("code") == 10006:
                    log.warning(f"Invite {invite_code} is invalid (Unknown Invite). Skipping early.")
                    save_joined_token(token, "invalid_invite", invite_code)
                    return "invalid_invite"

                if min_member_count > 0:
                    approx_members = metadata.get("approximate_member_count", 0)
                    if approx_members < min_member_count:
                        # INFO, not debug: this is by far the most common reason a
                        # worker starts and finishes within the same second. Hiding
                        # it makes the token look like it was handed to several
                        # workers at once, when it was really released and re-picked.
                        log.info(f"Invite {invite_code} has {approx_members} members. Skipping early (minimum required: {min_member_count})")
                        save_joined_token(token, "min_members_limit", invite_code)
                        return "min_members_limit"

                guild_id = metadata.get("guild", {}).get("id")
                if guild_id:
                    if is_guild_globally_joined(guild_id):
                        log.info(f"Server {guild_id} (invite: {invite_code}) has already been joined. Skipping across all tokens.")
                        save_joined_token(token, "Already Member", invite_code)
                        return "Already Member"
        except Exception as e:
            log.debug(f"Early guild join check failed for invite {invite_code}: {e}")

    # Browser-driven join mode: execute join via full Playwright Chromium session with in-DOM extension captcha solving
    if False and cfg.get("join_method") == "browser":
        try:
            from utils.browser_joiner import browser_join_server

            build_num = get_build_number(proxy)
            browser_profile = get_random_profile(build_num, token=token)
            browser_timezone = detect_timezone(proxy, user_agent=browser_profile["user_agent"])

            guild_id = None
            guild_name = None
            if 'metadata' in locals() and metadata:
                guild_id = metadata.get("guild", {}).get("id")
                guild_name = metadata.get("guild", {}).get("name")

            res_status = browser_join_server(
                token=token,
                invite_code=invite_code,
                proxy=proxy,
                timeout_seconds=cfg.get("browser_timeout", 60),
                headless=cfg.get("browser_headless", False),
                user_agent=browser_profile["user_agent"],
                timezone=browser_timezone,
                profile=browser_profile,
            )
            save_joined_token(token, res_status, invite_code, guild_id=guild_id, guild_name=guild_name)
            if res_status == "Joined":
                if guild_id:
                    save_guild_to_db(token, guild_id)
                min_delay = float(cfg.get("min_join_delay", 420))
                max_delay = float(cfg.get("max_join_delay", 480))
                if min_delay > max_delay:
                    min_delay, max_delay = max_delay, min_delay
                delay = random.uniform(min_delay, max_delay)
                log.info(f"Join complete {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Pausing token for {Fore.CYAN}{delay / 60:.1f}m{Style.RESET_ALL} ({delay:.0f}s) with active human browsing...")
                from utils.browser_joiner import simulate_browser_human_activity
                simulate_browser_human_activity(token, delay)
            return res_status
        except Exception as be:
            log.error(f"Browser joiner failed: {be}")
            save_joined_token(token, "failed", invite_code)
            return "failed"

    for attempt in range(1, max_retries + 1):
        if attempt > 1:
            log.info(f"Retrying join for token={format_token_id(token)}, invite={invite_code} (Attempt {attempt}/{max_retries})")

        with sessions_lock:
            cached = token_sessions.get(token)
            if cached:
                token_session_last_used[token] = time.time()

        if cached:
            if len(cached) == 6:
                session, fingerprint, gw, timezone, profile, telemetry = cached
            elif len(cached) == 5:
                session, fingerprint, gw, timezone, profile = cached
                telemetry = None
            else:
                session, fingerprint, gw = cached[:3]
                timezone = cached[3] if len(cached) > 3 else "America/Los_Angeles"
                profile = None
                telemetry = None
        else:
            session = StealthSession(timeout=default_request_timeout())
            if proxy:
                proxy_url = format_proxy_url(proxy)
                if proxy_url:
                    session.proxies = {"http": proxy_url, "https": proxy_url}
                    if "127.0.0.1" in proxy_url or "localhost" in proxy_url or "8080" in proxy_url:
                        session.verify = False

            build_num = get_build_number(proxy)
            profile = get_random_profile(build_num, token=token)
            # TLS must match the announced Chrome from the very first request:
            # on a cache miss the long-lived __dcfduid cookies and the fingerprint
            # are minted below, and they were being created under stealth_requests'
            # default chrome136 handshake, then cached for 30 days.
            apply_tls_profile(session, profile)

            # Fetch timezone of proxy or direct connection
            timezone = detect_timezone(proxy, user_agent=profile["user_agent"])
            log.info(f"Detected connection timezone: {timezone}")

            # Check if long-lived edge state (cookies, fingerprint, profile) is cached on disk
            cached_edge = load_cached_edge_state(token)
            if cached_edge:
                cached_cookies, fingerprint, cached_profile = cached_edge
                if cached_cookies:
                    session.cookies.update(cached_cookies)
                if cached_profile:
                    # Repair before refreshing: a profile written by an older
                    # build is otherwise replayed verbatim for the cache's 30-day
                    # life, keeping a full-build user agent and a Chrome major
                    # above the TLS ceiling.
                    profile = refresh_session_launch_identifiers(
                        repair_cached_profile(cached_profile), build_num
                    )
                log.info(f"Edge cache active {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Reusing persistent installation & edge cookies for {Fore.CYAN}{format_token_id(token)}{Style.RESET_ALL}")
                gw = None
                with sessions_lock:
                    token_sessions[token] = (session, fingerprint, gw, timezone, profile)
                    token_session_last_used[token] = time.time()
            else:
                try:
                    dcfduid, sdcfduid = fetch_cookies(session, profile)
                    fingerprint = get_fingerprint(session, dcfduid, sdcfduid, profile)
                    save_cached_edge_state(token, session.cookies.get_dict(), fingerprint, profile)
                    gw = None
                    with sessions_lock:
                        token_sessions[token] = (session, fingerprint, gw, timezone, profile)
                    token_session_last_used[token] = time.time()
                except Exception as e:
                    log.error(
                        f"{Fore.LIGHTRED_EX}error={type(e).__name__}: {e}{Style.RESET_ALL}"
                    )
                    if attempt == max_retries:
                        save_joined_token(token, "error", invite_code)
                    time.sleep(random.uniform(1.0, 3.0))
                    continue

        try:
            build_num = get_build_number(proxy)
            if not profile:
                profile = get_random_profile(build_num, token=token)
            # Assign, never .update(): on a cache miss get_fingerprint has just
            # left its own header set (content-type, origin, cookie) on the
            # session, and merging onto it kept those on every later request
            # and pushed authorization/referer to the end of the wire order.
            session.headers = build_headers(
                fingerprint, profile["super_properties"], timezone, profile,
                token=token, referer="https://discord.com/channels/@me",
            )
            # TLS handshake must agree with the Chrome the headers announce.
            apply_tls_profile(session, profile)

            # Connect Gateway FIRST to establish an active WebSocket session before any HTTP API requests.
            # Real Discord web clients connect Gateway and receive READY before making HTTP API requests.
            newly_connected = False
            if not gw or not gw.alive:
                from utils.gateway import DiscordGateway
                gw = DiscordGateway(token, proxy, profile["user_agent"], build_num, profile=profile)
                gw.connect()
                newly_connected = True

                # Initialize /api/v9/science telemetry stream with coherent hardware & timezone context
                telemetry = ScienceTelemetry(session, token, profile=profile, timezone=timezone, analytics_token=getattr(gw, "analytics_token", None))
                telemetry.start()
                telemetry.track_app_startup(is_fast_connect=False)

                with sessions_lock:
                    token_sessions[token] = (session, fingerprint, gw, timezone, profile, telemetry)
                    token_session_last_used[token] = time.time()
                _evict_idle_sessions(keep_token=token)

                        # Verify token status after Gateway is connected and session is established
            status = check_token_status(session)
            if status in ("rate_limited", "transient_error"):
                log.info(
                    f"Token status check inconclusive ({status}) for {format_token_id(token)} — "
                    f"backing off, NOT retiring the token."
                )
                _drop_session(token)
                save_joined_token(token, "retry", invite_code)
                return "retry"
            if status != "Valid":
                with sessions_lock:
                    cached_val = token_sessions.pop(token, None)
                    _cleanup_session(cached_val)
                save_joined_token(token, status, invite_code)
                return status

            # One-time initial presence warmup per token (only on first startup across the entire run)
            is_initial_startup = False
            with sessions_lock:
                if token not in warmed_up_tokens:
                    warmed_up_tokens.add(token)
                    is_initial_startup = True

            if is_initial_startup:
                cfg = load_config()
                min_warmup = float(cfg.get("min_warmup_delay", 60))
                max_warmup = float(cfg.get("max_warmup_delay", 120))
                warmup_delay = random.uniform(min_warmup, max_warmup)
                log.info(f"Initial presence warmup {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} warming presence for {Fore.CYAN}{warmup_delay:.1f}s{Style.RESET_ALL} (first time startup only)...")
                time.sleep(warmup_delay)

            # Fetch invite metadata and extract target guild ID
            metadata = fetch_invite_metadata(session, invite_code)
            if metadata.get("code") == 10006:
                log.warning(f"Invite {invite_code} is invalid (Unknown Invite). Skipping.")
                save_joined_token(token, "invalid_invite", invite_code)
                return "invalid_invite"

            # Telemetry: Emit invite opened, viewed, and accept button rendered (stages 1-3)
            if 'telemetry' in locals() and telemetry:
                telemetry.track_invite_sequence_start(invite_code, metadata, location="Join Guild Modal")

            guild_id = metadata.get("guild", {}).get("id")

            # One token per server, fleet-wide. Claiming rather than only reading
            # matters once threads run concurrently: two of them would otherwise
            # both see the server as free during the join round trip and both
            # take it. Keying on the guild rather than the invite also catches
            # two different invite codes that resolve to the same server.
            if not reserve_guild(guild_id):
                log.info(f"Server {guild_id} is already joined, or being joined by another token. Skipping.")
                save_joined_token(token, "Already Member", invite_code)
                return "Already Member"

            joined_list = load_guilds_db().get(token, [])

            # Check minimum member count requirement
            if min_member_count > 0:
                approx_members = metadata.get("approximate_member_count", 0)
                if approx_members < min_member_count:
                    log.debug(f"Invite {invite_code} has {approx_members} members. Skipping (minimum required: {min_member_count})")
                    save_joined_token(token, "min_members_limit", invite_code)
                    return "min_members_limit"

            # Verify guild limit
            guild_count = len(joined_list)
            if guild_count >= max_guild_limit:
                log.warning(f"Token {format_token_id(token)} has joined {guild_count} guilds (max limit config: {max_guild_limit}). Skipping join.")
                save_joined_token(token, "failed", invite_code)
                return "failed"

            # Human warmup: simulate authentic user browsing & settings inspection before join
            simulate_human_warmup(session, token)

            # Join attempt — payload mirrors what the real Discord client sends
            join_url = f"{API}/invites/{invite_code}"
            
            # x-context-properties must carry the REAL invite context. A real
            # client always knows which guild/channel the invite points at (it
            # just rendered the invite card); an all-null context paired with a
            # location string is a shape no genuine client ever produces, and it
            # is trivially greppable server-side.
            invite_channel = metadata.get("channel") or {}
            join_context = {
                "location": "Accept Invite Page",
                "location_guild_id": guild_id,
                "location_channel_id": invite_channel.get("id"),
                "location_channel_type": invite_channel.get("type", 0),
            }
            # separators=(",", ":") to match JSON.stringify — a browser emits no
            # spaces after ':' or ','. build.py already does this for
            # x-super-properties, so without it the two base64 headers in the same
            # request are formatted differently, which no real client would do.
            session.headers["x-context-properties"] = base64.b64encode(
                json.dumps(join_context, separators=(",", ":")).encode()
            ).decode()
            # Attribution is fixed for the life of a client_launch_id -- one page
            # load. Across 13 captured launches referrer_current never changed
            # once, including a launch that handled 41 separate invites: it stays
            # pinned to whatever invite (or directory) opened the page. Only the
            # Referer header varies per request. Deciding this per invite would
            # make referrer_current and the utm keys flip mid-session, which no
            # captured launch ever does.
            invite_referer, invite_attribution = get_launch_attribution(profile, invite_code)
            session.headers["referer"] = invite_referer
            if invite_attribution:
                attributed_props = build_attributed_super_properties(
                    profile, invite_attribution, profile.get("_launch_invite", invite_code)
                )
                if attributed_props:
                    session.headers["x-super-properties"] = attributed_props

            # Ensure Gateway is connected and alive before submitting join
            if not gw or not gw.alive:
                from utils.gateway import DiscordGateway
                gw = DiscordGateway(token, proxy, profile["user_agent"], build_num, profile=profile)
                gw.connect()
                with sessions_lock:
                    token_sessions[token] = (session, fingerprint, gw, timezone, profile, telemetry)
                    token_session_last_used[token] = time.time()
                _evict_idle_sessions(keep_token=token)

            # The real client sends the gateway session it is connected on
            # (captured live from Brave: {"session_id": "<32 hex>"}); null only
            # when it has no gateway. We connect one right above, so claiming
            # none here contradicts the session Discord can see for this token.
            payload = {
                "session_id": gw.session_id if (gw and gw.alive and gw.session_id) else None,
            }

            # Telemetry: Emit invite actioned & resolved (stages 4-5)
            if 'telemetry' in locals() and telemetry:
                telemetry.track_invite_actioned(invite_code, guild_id, location="Accept Invite Page")

            res, res_json = _post_json(session, join_url, payload)

            if not res:
                if attempt == max_retries:
                    save_joined_token(token, "failed", invite_code)
                    return "failed"
                time.sleep(random.uniform(2.0, 5.0))
                continue

            # Successful join
            if res.status_code in (200, 201):
                # A join that goes through WITHOUT a captcha is the reset signal.
                # The token's captcha history is forgiven -- the distinct-invite
                # count and its per-token limit clear -- and the Bit Solver
                # fail-streak resets too: if joins are landing without needing the
                # solver, whatever was wrong with it no longer matters. (A solved
                # captcha is deliberately NOT a reset; only a clean join is.)
                with sessions_lock:
                    token_captcha_invites.pop(token, None)
                    token_captcha_limit.pop(token, None)
                _solver_fail_streak["count"] = 0
                guild_data = res_json.get("guild", {})
                guild_id = guild_data.get("id") or metadata.get("guild", {}).get("id")
                guild_name = guild_data.get("name") or metadata.get("guild", {}).get("name")
                # Guilds DB first: it is what one-token-per-server is enforced
                # from on restart. The join is already durable on Discord, so a
                # crash or /restart between the two writes must leave the DB,
                # not just joined.txt, knowing about it.
                if guild_id:
                    save_guild_to_db(token, guild_id)
                save_joined_token(token, "Joined", invite_code, guild_id=guild_id, guild_name=guild_name)
                if guild_id:
                    # Track guild joined telemetry event (stage 6)
                    if 'telemetry' in locals() and telemetry:
                        telemetry.track_guild_joined(invite_code, guild_id, invite_channel.get("id"), location="Join Guild Modal")

                    # x-context-properties belongs to the join POST only; the
                    # capture never carries it on the browsing GETs or /science.
                    session.headers.pop("x-context-properties", None)
                    # Simulate natural browsing of the server (emits WS opcodes 37, 8 & 13 + /science telemetry)
                    simulate_human_browsing(session, guild_id, gw, telemetry if 'telemetry' in locals() else None)
                    time.sleep(random.uniform(2.5, 4.5))

                    # Bypass all common verification systems if enabled in config
                    cfg = load_config()
                    if is_verification_enabled(cfg):
                        bypass_welcome_screen(session, guild_id)
                        time.sleep(random.uniform(2.0, 3.5))

                        bypass_rules_and_onboarding(session, guild_id)
                        time.sleep(random.uniform(2.5, 4.5))

                        check_verification_channels(session, guild_id)

                        # Give bots time to send DMs, then bypass them in one pass
                        bypass_verification_bots(session, token, solver_type, solver_api_key, proxy)
                    else:
                        log.debug(f"Verification bypass disabled in config for token {format_token_id(token)}.")

                # In Token Core mode, global pacing is governed by the round-robin dispatcher (35-45s per thread).
                # Brief natural pause before yielding to the next worker in the queue:
                cfg = load_config()
                # "fleet" is the current name; "token_core" is the legacy alias.
                if str(cfg.get("join_engine_mode", "fleet")).lower().strip() in ("fleet", "token_core"):
                    time.sleep(random.uniform(3.0, 5.0))
                    return "Joined"

                # Classic mode: keep browsing the new server before next action for this thread
                min_delay = float(cfg.get("min_join_delay", 420))
                max_delay = float(cfg.get("max_join_delay", 480))
                if min_delay > max_delay:
                    min_delay, max_delay = max_delay, min_delay
                delay = random.uniform(min_delay, max_delay)
                log.info(f"Join complete {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Pausing token for {Fore.CYAN}{delay / 60:.1f}m{Style.RESET_ALL} ({delay:.0f}s) with active browsing...")

                end_sleep = time.time() + delay
                while time.time() < end_sleep:
                    chunk = min(random.uniform(45.0, 90.0), max(1.0, end_sleep - time.time()))
                    time.sleep(chunk)
                    if time.time() < end_sleep and guild_id:
                        simulate_human_browsing(session, guild_id, gw, telemetry if 'telemetry' in locals() else None)
                return "Joined"

            # Check for captcha
            captcha_sitekey = res_json.get("captcha_sitekey")
            captcha_rqdata = res_json.get("captcha_rqdata")
            captcha_rqtoken = res_json.get("captcha_rqtoken")
            
            if captcha_sitekey and captcha_rqdata:
                cfg = load_config()

                # Count DISTINCT invites that have captcha'd this token. Retrying
                # the same invite does not grow the set, so this measures how many
                # different servers challenged the token, not how many attempts.
                # The token retires once that many separate invites have gated it,
                # at a per-token threshold randomised in [min, max]. max <= 0
                # disables the whole mechanism.
                try:
                    hi = int(cfg.get("max_captcha_before_skip", 8) or 0)
                except (TypeError, ValueError):
                    hi = 8
                try:
                    lo = int(cfg.get("min_captcha_before_skip", 5) or 0)
                except (TypeError, ValueError):
                    lo = 5
                if lo < 1:
                    lo = 1
                # max_captcha_before_skip <= 0 disables retirement; the clamp
                # below used to run first and turn 0 into lo, silently enabling it.
                if 0 < hi < lo:
                    hi = lo
                clean_invite = str(invite_code).split("?", 1)[0]
                with sessions_lock:
                    seen = token_captcha_invites.setdefault(token, set())
                    seen.add(clean_invite)
                    distinct_captchad = len(seen)
                    token_limit = token_captcha_limit.setdefault(token, random.randint(lo, hi))
                if hi > 0 and distinct_captchad >= token_limit:
                    log.warning(
                        f"Token {format_token_id(token)} was captcha'd on {distinct_captchad} "
                        f"separate invites (limit {token_limit}). Retiring the token."
                    )
                    _clear_captcha_headers(session)
                    _drop_session(token)
                    save_joined_token(token, "captcha_retired", invite_code)
                    return "captcha_retired"

                max_solves_cfg = cfg.get("max_captcha_solves", 1)
                
                # Check current captcha solve count for this token
                with sessions_lock:
                    current_solves = token_captcha_count.get(token, 0)
                
                # Determine if we should solve (if max_solves_cfg is "all", "infinite", 0, or current < max)
                if isinstance(max_solves_cfg, str) and max_solves_cfg.lower() in ("all", "infinite", "unlimited", "inf"):
                    can_solve = True
                    max_solves_label = "unlimited"
                elif isinstance(max_solves_cfg, (int, float)) and max_solves_cfg == 0:
                    can_solve = True
                    max_solves_label = "unlimited"
                else:
                    try:
                        max_limit = int(max_solves_cfg)
                        can_solve = current_solves < max_limit
                        max_solves_label = str(max_limit)
                    except ValueError:
                        can_solve = current_solves < 1
                        max_solves_label = "1"

                if not can_solve:
                    log.warning(
                        f"Captcha detected for token {format_token_id(token)} on invite {invite_code}, "
                        f"but token reached max captcha solve limit ({current_solves}/{max_solves_label}). Skipping token..."
                    )
                    with sessions_lock:
                        cached_val = token_sessions.pop(token, None)
                        if cached_val and len(cached_val) > 2 and cached_val[2]:
                            try:
                                cached_val[2].close()
                            except Exception:
                                pass
                    save_joined_token(token, "failed_captcha", invite_code)
                    return "captcha_skip"

                # Don't spend a captcha solve on an invite that is already gone.
                # This is the 403/10008 we were only discovering *after* the solve.
                if _invite_is_dead(session, invite_code):
                    log.warning(
                        f"Invite {invite_code} is no longer usable — skipping the captcha "
                        f"solve entirely. Dropping the invite, keeping the token."
                    )
                    save_joined_token(token, "invalid_invite", invite_code)
                    return "invalid_invite"

                log.info(
                    f"Captcha challenge detected {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} "
                    f"token={Fore.CYAN}{format_token_id(token)}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}│{Style.RESET_ALL} "
                    f"sitekey={Fore.YELLOW}{captcha_sitekey[:12]}...{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}│{Style.RESET_ALL} "
                    f"solve={Fore.WHITE}{current_solves + 1}/{max_solves_label}{Style.RESET_ALL}"
                )
                
                # Solve with the exact identity that will submit the token. The
                # solver browser must look like this account's browser, on this
                # account's IP, in this account's timezone — hCaptcha scores the
                # solve and Discord rejects low-scoring tokens by handing back a
                # fresh challenge (the endless "secondary captcha" loop).
                ua = profile["user_agent"] if profile else USER_AGENT
                solve_ctx = _build_solve_context(
                    session, profile, timezone, ua,
                    hardware=getattr(telemetry, "hw", None) if ('telemetry' in locals() and telemetry) else None,
                )

                cap_solve_start = time.time()
                cap_token, cap_burned = _solve_join_captcha(
                    solver_type=solver_type,
                    solver_api_key=solver_api_key,
                    sitekey=captcha_sitekey,
                    rqdata=captcha_rqdata,
                    proxy=proxy,
                    token=token,
                    solve_ctx=solve_ctx,
                    max_retries=5,
                    label="captcha",
                )
                cap_solve_elapsed = time.time() - cap_solve_start

                # Handle 120s timeout without burning the token
                if cap_token == "timeout":
                    log.warning(f"Captcha timeout for invite={invite_code} token={format_token_id(token)}")
                    STATS["captcha_fails"] = STATS.get("captcha_fails", 0) + 1
                    try:
                        from utils.dashboard import push_token_core_log
                        push_token_core_log(f"Captcha timeout invite={invite_code}", "captcha")
                    except Exception:
                        pass
                    _clear_captcha_headers(session)
                    save_joined_token(token, "Captcha Timeout", invite_code)
                    return "Captcha Timeout"

                # A burned challenge cannot be recovered on this attempt.
                if cap_burned and not cap_token:
                    log.warning(
                        f"Captcha challenge was lost for token {format_token_id(token)}. "
                        f"Backing off instead of re-requesting one — the invite will be "
                        f"retried later with a fresh session."
                    )
                    _clear_captcha_headers(session)
                    _drop_session(token)
                    save_joined_token(token, "captcha_retry", invite_code)
                    return "captcha_retry"

                if cap_token:
                    STATS["captcha_solves"] = STATS.get("captcha_solves", 0) + 1
                    with sessions_lock:
                        token_captcha_count[token] = current_solves + 1
                        new_count = token_captcha_count[token]

                    # Loop to handle chained/secondary captcha challenges
                    max_captcha_rounds = int(cfg.get("max_captcha_rounds", 4))
                    for captcha_round in range(max_captcha_rounds):
                        log.info(
                            f"Captcha solved successfully in {Fore.GREEN}{cap_solve_elapsed:.1f}s{Style.RESET_ALL}! "
                            f"Retrying join with captcha payload (round {captcha_round + 1}/{max_captcha_rounds})..."
                        )

                        # Extract captcha_session_id from response (matches acc-gen)
                        captcha_session_id = res_json.get("captcha_session_id")
                        _apply_captcha_headers(session, cap_token, captcha_rqtoken, captcha_session_id)

                        # Real users don't submit a solved captcha in the same
                        # millisecond the checkbox turns green.
                        time.sleep(random.uniform(1.2, 3.0))

                        # Retry POST with original join payload (matches acc-gen).
                        # resend_after_ratelimit=False: the captcha key is
                        # single-use, so a silent re-POST would submit a consumed
                        # key and be answered with a fresh challenge.
                        res, res_json = _post_json(
                            session, join_url, payload, retries=0, resend_after_ratelimit=False
                        )
                        _clear_captcha_headers(session)

                        if res and res.status_code in (200, 201):
                            guild_data = res_json.get("guild", {})
                            guild_id = guild_data.get("id") or metadata.get("guild", {}).get("id")
                            guild_name = guild_data.get("name") or metadata.get("guild", {}).get("name")
                            # DB before joined.txt: see the no-captcha path.
                            if guild_id:
                                save_guild_to_db(token, guild_id)
                            save_joined_token(token, "Joined", invite_code, guild_id=guild_id, guild_name=guild_name)
                            if guild_id:
                                # Run onboarding/welcome screens bypasses if verification enabled in config
                                if is_verification_enabled(cfg):
                                    if 'telemetry' in locals() and telemetry:
                                        telemetry.track_guild_joined(invite_code, guild_id, invite_channel.get("id"), location="Join Guild Modal")
                                    session.headers.pop("x-context-properties", None)
                                    simulate_human_browsing(session, guild_id, gw, telemetry if 'telemetry' in locals() else None)
                                    time.sleep(random.uniform(2.5, 4.5))
                                    bypass_welcome_screen(session, guild_id)
                                    time.sleep(random.uniform(2.0, 3.5))
                                    bypass_rules_and_onboarding(session, guild_id)
                                    time.sleep(random.uniform(2.5, 4.5))
                                    check_verification_channels(session, guild_id)
                                    bypass_verification_bots(session, token, solver_type, solver_api_key, proxy)
                                else:
                                    log.debug(f"Verification bypass disabled in config for token {format_token_id(token)}.")
                                
                            # Same defaults as the other two join paths, which use
                            # 420/480. These read 25/45, so with the keys absent
                            # this path paused ~35s instead of ~7min -- a ten-fold
                            # faster join rate on exactly the accounts that had
                            # just been challenged. Also guard an inverted range,
                            # which random.uniform accepts silently.
                            if str(cfg.get("join_engine_mode", "fleet")).lower().strip() in ("fleet", "token_core"):
                                # Fleet pacing is the dispatcher's per-token
                                # cooldown; this sleep runs inside the thread's
                                # worker and was stalling every worker on the
                                # exit IP for ~8 min after each solved captcha.
                                delay = random.uniform(3.0, 5.0)
                            else:
                                min_delay = float(cfg.get("min_join_delay", 420))
                                max_delay = float(cfg.get("max_join_delay", 480))
                                if min_delay > max_delay:
                                    min_delay, max_delay = max_delay, min_delay
                                delay = random.uniform(min_delay, max_delay)
                            log.debug(f"Mimicking human: browsing server, sleeping {delay:.1f}s...")
                            time.sleep(delay)
                            
                            # Check if token reached max solves allowed
                            reached_limit = False
                            if max_solves_label != "unlimited":
                                try:
                                    if new_count >= int(max_solves_label):
                                        reached_limit = True
                                except ValueError:
                                    pass

                            if reached_limit:
                                log.info(f"Token {format_token_id(token)} reached max captcha solve limit ({new_count}/{max_solves_label}). Skipping token for future joins.")
                                return "Joined_Captcha_Exhausted"
                            else:
                                return "Joined"

                        # Check if the retry returned ANOTHER captcha challenge (secondary captcha)
                        if res_json.get("captcha_sitekey") and res_json.get("captcha_rqdata"):
                            # Refresh EVERY field of the challenge. Re-solving
                            # against a stale sitekey produces a token bound to
                            # the wrong challenge, which guarantees another
                            # rejection — an infinite loop.
                            captcha_sitekey = res_json["captcha_sitekey"]
                            captcha_rqdata = res_json["captcha_rqdata"]
                            captcha_rqtoken = res_json.get("captcha_rqtoken")
                            captcha_session_id = res_json.get("captcha_session_id")

                            # Surface Discord's own explanation. "captcha-required"
                            # means it simply wants another one; anything in
                            # _CAPTCHA_REJECT_CODES means our token was refused.
                            reasons = _captcha_reject_reason(res_json)
                            rejected = _captcha_token_was_rejected(res_json)
                            log.warning(
                                f"Secondary captcha challenge received (round {captcha_round + 1}) "
                                f"[status={res.status_code if res else 'None'} "
                                f"reason={','.join(reasons) if reasons else 'unspecified'} "
                                f"service={res_json.get('captcha_service', '?')} "
                                f"sitekey={captcha_sitekey}]. Re-solving..."
                            )
                            if rejected:
                                log.warning(
                                    f"Discord REJECTED the submitted captcha token "
                                    f"({','.join(reasons)}) — the token was not accepted for this "
                                    f"challenge. Usual causes: the solver answered the images wrong "
                                    f"and hCaptcha swapped the challenge (watch the solver window), "
                                    f"or the solver browser's fingerprint/IP/timezone does not match "
                                    f"the account session."
                                )
                            _record_captcha_challenge(token, invite_code, res, res_json, captcha_round + 1)

                            # No round left to submit into — don't burn a solve
                            # (and a solver credit) on a token we'd never send.
                            if captcha_round + 1 >= max_captcha_rounds:
                                log.warning(
                                    f"Exhausted {max_captcha_rounds} captcha rounds for token "
                                    f"{format_token_id(token)} without an accepted token."
                                )
                                break

                            # Back off a little more each round; hammering the
                            # endpoint is what escalates the challenge difficulty.
                            time.sleep(random.uniform(3.0, 6.0) * (captcha_round + 1))

                            sec_solve_start = time.time()
                            cap_token, cap_burned = _solve_join_captcha(
                                solver_type=solver_type,
                                solver_api_key=solver_api_key,
                                sitekey=captcha_sitekey,
                                rqdata=captcha_rqdata,
                                proxy=proxy,
                                token=token,
                                solve_ctx=solve_ctx,
                                max_retries=3,
                                label="secondary captcha",
                            )
                            cap_solve_elapsed = time.time() - sec_solve_start

                            if not cap_token:
                                if cap_burned:
                                    # Challenge died mid-solve. Same reasoning as
                                    # above: back off rather than pestering Discord
                                    # for another challenge.
                                    log.warning(
                                        f"Secondary challenge was lost for token "
                                        f"{format_token_id(token)}. Backing off — the invite "
                                        f"will be retried later with a fresh session."
                                    )
                                    _clear_captcha_headers(session)
                                    _drop_session(token)
                                    save_joined_token(token, "captcha_retry", invite_code)
                                    return "captcha_retry"
                                log.warning(f"Failed to solve secondary captcha for token {format_token_id(token)}. Giving up.")
                                break

                            with sessions_lock:
                                token_captcha_count[token] = token_captcha_count.get(token, 0) + 1
                                new_count = token_captcha_count[token]
                            STATS["captcha_solves"] = STATS.get("captcha_solves", 0) + 1
                            continue
                        else:
                            # The captcha itself was ACCEPTED — this is a plain join
                            # failure. Classify it like the normal join path instead
                            # of blaming the captcha, so the token isn't written off
                            # as a captcha failure.
                            err_status = res.status_code if res else None
                            err_code = (res_json or {}).get("code")
                            log.warning(
                                f"Captcha accepted, but the join failed "
                                f"(status={err_status} code={err_code}): {res_json}"
                            )
                            _clear_captcha_headers(session)

                            if err_status == 401:
                                save_joined_token(token, "invalid", invite_code)
                                return "invalid"
                            if err_status == 403 and err_code == 10006:
                                # 10006 = Unknown Invite (truly expired or deleted)
                                log.warning(
                                    f"Invite {invite_code} is no longer usable "
                                    f"(code={err_code}). Dropping the invite, keeping the token."
                                )
                                save_joined_token(token, "invalid_invite", invite_code)
                                return "invalid_invite"
                            if err_status == 403 and err_code == 10008:
                                # 10008 = Unknown Message (Discord anti-abuse / security block on this join attempt)
                                log.warning(
                                    f"Join attempt was blocked by Discord security filters (code=10008 / Unknown Message) "
                                    f"for token {format_token_id(token)} on invite {invite_code}. Rotating to next token..."
                                )
                                with sessions_lock:
                                    cached_val = token_sessions.pop(token, None)
                                    _cleanup_session(cached_val)
                                save_joined_token(token, "action_blocked", invite_code)
                                return "action_blocked"
                            if err_status == 403:
                                save_joined_token(token, "locked", invite_code)
                                return "locked"

                            # Anything else is transient: keep the token, retry later.
                            save_joined_token(token, "failed", invite_code)
                            return "failed"

                # If solving fails or resolved retry fails, skip the token
                _clear_captcha_headers(session)
                log.warning(
                    f"Captcha solving failed or secondary captcha required for token {format_token_id(token)} on invite {invite_code}. "
                    f"Skipping this token... (reason codes logged to log/captcha_debug.log)"
                )
                # Solver health: only meaningful when a solver is actually enabled.
                # A run of failures means the Bit Solver is not returning usable
                # tokens (extension/service broken, wrong sitekey, IP blocked) --
                # a solver problem, not a token problem -- so tell the operator.
                if solver_type and solver_api_key:
                    _solver_fail_streak["count"] += 1
                    if _solver_fail_streak["count"] >= SOLVER_FAIL_WARN_AT:
                        log.error(
                            f"{Fore.LIGHTRED_EX}Bit Solver has failed {_solver_fail_streak['count']} captchas in a row.{Style.RESET_ALL} "
                            f"The solver service is likely not working (check the extension, the solver on :5001, "
                            f"or your solver credentials) — joins that hit a captcha will keep failing until it is fixed."
                        )
                        try:
                            from utils.dashboard import push_token_core_log
                            push_token_core_log(
                                f"Bit Solver failing ({_solver_fail_streak['count']} in a row) - check the solver service",
                                "error",
                            )
                        except Exception:
                            pass
                with sessions_lock:
                    cached_val = token_sessions.pop(token, None)
                    if cached_val and len(cached_val) > 2 and cached_val[2]:
                        try:
                            cached_val[2].close()
                        except Exception:
                            pass
                save_joined_token(token, "failed_captcha", invite_code)
                return "captcha_skip"


            if res and res.status_code == 403:
                res_code = (res_json or {}).get("code")
                res_msg = str((res_json or {}).get("message", "")).lower()

                with sessions_lock:
                    cached_val = token_sessions.pop(token, None)
                    _cleanup_session(cached_val)

                if res_code == 10006:
                    save_joined_token(token, "invalid_invite", invite_code)
                    return "invalid_invite"
                elif res_code == 10008 or "unknown message" in res_msg:
                    save_joined_token(token, "action_blocked", invite_code)
                    return "action_blocked"
                elif res_code in (40007, 20028) or "temporarily limited" in res_msg or "limited your access" in res_msg or "unable to join" in res_msg or "quarantine" in res_msg:
                    log.warning(f"Token {format_token_id(token)} has a temporary feature limitation (Discord Safety quarantine). Moving to limited list.")
                    save_joined_token(token, "limited", invite_code)
                    return "limited"
                else:
                    save_joined_token(token, "locked", invite_code)
                    return "locked"
            elif res and res.status_code == 401:
                with sessions_lock:
                    cached_val = token_sessions.pop(token, None)
                    if cached_val and len(cached_val) > 2 and cached_val[2]:
                        try:
                            cached_val[2].close()
                        except Exception:
                            pass
                save_joined_token(token, "invalid", invite_code)
                return "invalid"
            else:
                log.error(f"Join failed: {res.status_code if res else 'No Response'} - {res_json}")
                if attempt == max_retries:
                    with sessions_lock:
                        cached_val = token_sessions.pop(token, None)
                        if cached_val and len(cached_val) > 2 and cached_val[2]:
                            try:
                                cached_val[2].close()
                            except Exception:
                                pass
                    save_joined_token(token, "failed", invite_code)
                    return "failed"
                time.sleep(random.uniform(2.0, 5.0))
        finally:
            # Whatever the outcome, the join context must not ride on the next
            # request this (reused) session makes.
            try:
                session.headers.pop("x-context-properties", None)
            except NameError:
                pass
    return "failed"

def close_all_gateways():
    with sessions_lock:
        for token, cached in list(token_sessions.items()):
            if len(cached) > 2 and cached[2]:
                try:
                    cached[2].close()
                except Exception:
                    pass
        token_sessions.clear()''',
    'utils.build': r'''import os, time, base64, json, platform, uuid, re, requests, threading, hashlib

from colorama import Fore, Style
from stealth_requests import StealthSession

from utils.core import setup_logger, write_json_atomic, default_request_timeout
from utils.proxy import format_proxy_url
log = setup_logger(__name__)

EDGE_CACHE_FILE = "output/edge_cache.json"
_edge_cache_lock = threading.Lock()

def load_cached_edge_state(token):
    """Load persistent long-lived edge cookies, fingerprint, and profile for a token."""
    with _edge_cache_lock:
        if not os.path.exists(EDGE_CACHE_FILE):
            return None
        try:
            with open(EDGE_CACHE_FILE, "r", encoding="utf-8") as f:
                cache = json.load(f)
                data = cache.get(token)
                if data and isinstance(data, dict):
                    # Cache valid for up to 30 days (matches browser cookie lifetime)
                    if time.time() - data.get("timestamp", 0) < 30 * 86400:
                        return data.get("cookies"), data.get("fingerprint"), data.get("profile")
        except Exception as e:
            log.debug(f"Failed to read edge cache: {e}")
    return None

def save_cached_edge_state(token, cookies_dict, fingerprint, profile):
    """Persist long-lived edge cookies, fingerprint, and profile for a token."""
    with _edge_cache_lock:
        os.makedirs("output", exist_ok=True)
        cache = {}
        if os.path.exists(EDGE_CACHE_FILE):
            try:
                with open(EDGE_CACHE_FILE, "r", encoding="utf-8") as f:
                    cache = json.load(f)
            except Exception:
                cache = {}
        
        cache[token] = {
            "cookies": cookies_dict,
            "fingerprint": fingerprint,
            "profile": profile,
            "timestamp": int(time.time()),
        }
        try:
            write_json_atomic(EDGE_CACHE_FILE, cache)
        except Exception as e:
            # Torn write here wipes every token's device profile at once, and the
            # loader treats the corruption as "no cache", so all tokens
            # regenerate fingerprints simultaneously.
            log.warning(f"Failed to write edge cache: {e}")


_cached_build_number = None
_build_number_lock = threading.Lock()

_OFFICIAL_CHROME_VERSIONS = {}
_OFFICIAL_DISCORD_VERSIONS = {}
_OFFICIAL_ELECTRON_PAIRS = []
_OFFICIAL_LINUX_KERNELS = []
_versions_lock = threading.Lock()
# Set once the live Chrome version fetch has finished (success or not), so
# the first profile of a run can wait for it instead of using a stale pool.
_chrome_versions_ready = threading.Event()

def fetch_official_chrome_versions():
    """Fetch the latest 5 active stable Chrome release version strings directly from Google's Version History API
    for Windows, Mac, and Linux platforms.
    """
    global _OFFICIAL_CHROME_VERSIONS
    platforms = {"win": "win", "mac": "mac", "linux": "linux"}
    fetched = {}

    for plat_key, plat_api in platforms.items():
        try:
            url = f"https://versionhistory.googleapis.com/v1/chrome/platforms/{plat_api}/channels/stable/versions"
            r = requests.get(url, timeout=5)
            if r.status_code == 200:
                # Restrict strictly to the top 5 latest versions
                vers = [v["version"] for v in r.json().get("versions", []) if "version" in v][:5]
                if vers:
                    fetched[plat_key] = vers
        except Exception as e:
            log.debug(f"Failed to fetch Chrome version history for {plat_key}: {e}")

    with _versions_lock:
        for k, v in fetched.items():
            _OFFICIAL_CHROME_VERSIONS[k] = v

    if fetched:
        log.debug(f"Loaded {sum(len(v) for v in fetched.values())} official Chrome release versions from Google API.")
    _chrome_versions_ready.set()


def _discord_get(url, timeout=5):
    """GET a discord.com URL on a Chrome handshake.

    Plain python-requests presents an OpenSSL JA3 and a python-requests UA to
    discord.com; even token-less, that is a non-browser fingerprint from the
    host IP. Use curl_cffi's newest Chrome target instead.
    """
    from curl_cffi import requests as _cffi
    target = _CHROME_TARGETS[-1][1] if _CHROME_TARGETS else "chrome136"
    return _cffi.get(url, impersonate=target, timeout=timeout)


def fetch_official_discord_versions():
    """Fetch live Discord client versions directly from Discord distribution manifests."""
    global _OFFICIAL_DISCORD_VERSIONS
    fetched = {}

    # 1. Windows manifest
    try:
        url = "https://discord.com/api/updates/distributions/app/manifests/latest?channel=stable&platform=win&arch=x64"
        r = _discord_get(url)
        if r.status_code == 200:
            modules = r.json().get("modules", {})
            for m in modules.values():
                hv = m.get("full", {}).get("host_version")
                if hv and len(hv) >= 3:
                    major, minor, build = hv[0], hv[1], hv[2]
                    fetched["win"] = [
                        f"{major}.{minor}.{build}",
                        f"{major}.{minor}.{max(1, build - 4)}",
                        f"{major}.{minor}.{max(1, build - 9)}",
                        f"{major}.{minor}.{max(1, build - 16)}",
                        f"{major}.{minor}.{max(1, build - 34)}",
                        f"{major}.{minor}.{max(1, build - 59)}",
                    ]
                    break
    except Exception as e:
        log.debug(f"Failed to fetch Discord Windows manifest: {e}")

    # 2. Linux manifest
    try:
        url = "https://discord.com/api/updates/distributions/app/manifests/latest?channel=stable&platform=linux&arch=x64"
        r = _discord_get(url)
        if r.status_code == 200:
            modules = r.json().get("modules", {})
            for m in modules.values():
                hv = m.get("full", {}).get("host_version")
                if hv and len(hv) >= 3:
                    major, minor, build = hv[0], hv[1], hv[2]
                    fetched["linux"] = [
                        f"{major}.{minor}.{build}",
                        f"{major}.{minor}.{max(1, build - 2)}",
                        f"{major}.{minor}.{max(1, build - 5)}",
                        "0.0.95", "0.0.92", "0.0.89"
                    ]
                    break
    except Exception as e:
        log.debug(f"Failed to fetch Discord Linux manifest: {e}")

    # 3. macOS
    if "mac" not in fetched:
        fetched["mac"] = ["0.0.408", "0.0.405", "0.0.395", "0.0.380"]

    with _versions_lock:
        for k, v in fetched.items():
            _OFFICIAL_DISCORD_VERSIONS[k] = v

    if fetched:
        log.debug(f"Loaded official Discord client versions for {list(fetched.keys())}.")


def fetch_official_electron_pairs():
    """Fetch live stable Electron -> Chromium pairing map from electron-to-chromium registry."""
    global _OFFICIAL_ELECTRON_PAIRS
    try:
        url = "https://raw.githubusercontent.com/Kilian/electron-to-chromium/master/full-versions.json"
        r = requests.get(url, timeout=5)
        if r.status_code == 200:
            data = r.json()
            stable_majors = {}
            for v, c in data.items():
                if "-" not in v:
                    major = int(v.split(".")[0])
                    if major not in stable_majors:
                        stable_majors[major] = (v, c)
            top_pairs = [stable_majors[m] for m in sorted(stable_majors.keys(), reverse=True)[:6]]
            if top_pairs:
                with _versions_lock:
                    _OFFICIAL_ELECTRON_PAIRS = top_pairs
                log.debug(f"Loaded {len(top_pairs)} live Electron-Chromium release pairs.")
    except Exception as e:
        log.debug(f"Failed to fetch Electron-Chromium pairs: {e}")


def fetch_official_linux_kernels():
    """Fetch live stable and LTS Linux kernel releases from kernel.org."""
    global _OFFICIAL_LINUX_KERNELS
    try:
        url = "https://www.kernel.org/releases.json"
        r = requests.get(url, timeout=5)
        if r.status_code == 200:
            releases = r.json().get("releases", [])
            lts = [f"{rel['version']}-generic" for rel in releases if rel.get("moniker") in ("longterm", "stable")][:5]
            if lts:
                with _versions_lock:
                    _OFFICIAL_LINUX_KERNELS = lts
                log.debug(f"Loaded {len(lts)} live Linux kernel releases from kernel.org.")
    except Exception as e:
        log.debug(f"Failed to fetch Linux kernels: {e}")


_bootstrap_started = False
_bootstrap_lock = threading.Lock()

def fetch_all_dynamic_versions(background=True):
    """Unified bootstrap to query live version registries concurrently without blocking startup."""
    global _bootstrap_started
    with _bootstrap_lock:
        if _bootstrap_started:
            return
        _bootstrap_started = True

    t1 = threading.Thread(target=fetch_official_chrome_versions, daemon=True)
    t2 = threading.Thread(target=fetch_official_discord_versions, daemon=True)
    t3 = threading.Thread(target=fetch_official_electron_pairs, daemon=True)
    t4 = threading.Thread(target=fetch_official_linux_kernels, daemon=True)

    threads = [t1, t2, t3, t4]
    for t in threads:
        t.start()
    if not background:
        for t in threads:
            t.join(timeout=2.0)


def get_latest_chrome_version():
    try:
        with _versions_lock:
            win_versions = _OFFICIAL_CHROME_VERSIONS.get("win")
        if win_versions:
            return int(win_versions[0].split(".")[0])
        # Trigger non-blocking background fetch if not started
        fetch_all_dynamic_versions(background=True)
        return 136  # verified modern stable default
    except Exception as e:
        log.debug(f"get_latest_chrome_version fallback: {e}")
        return 136  # fallback


CHROME_VERSION = get_latest_chrome_version()
EDGE_VERSION = CHROME_VERSION
log.debug(f"using CHROME_VERSION={CHROME_VERSION} EDGE_VERSION={EDGE_VERSION}")

import random

# ── TLS / user-agent coherence ─────────────────────────────────────────────
# The profile pool advertises Chrome 149-152, but the TLS layer can only imitate
# the Chrome builds curl_cffi ships a profile for. Claiming a version the
# handshake cannot reproduce is a split fingerprint, which is worse than claiming
# an older browser honestly. Both the version pool and the impersonation target
# are therefore derived from what this curl_cffi build actually supports.

def _available_chrome_targets():
    """(major, target_name) for every Chrome TLS profile this curl_cffi ships."""
    try:
        import typing
        from curl_cffi.requests.impersonate import BrowserTypeLiteral
        names = typing.get_args(BrowserTypeLiteral)
    except Exception:
        names = ("chrome110", "chrome116", "chrome119", "chrome120",
                 "chrome123", "chrome124", "chrome131", "chrome136")
    out = []
    for n in names:
        if not n.startswith("chrome") or "android" in n:
            continue
        digits = n[len("chrome"):]
        if digits[:3].isdigit():
            out.append((int(digits[:3]), n))
    return sorted(set(out))


_CHROME_TARGETS = _available_chrome_targets()


def max_impersonatable_chrome():
    """Newest Chrome major this curl_cffi can imitate at the TLS layer."""
    return _CHROME_TARGETS[-1][0] if _CHROME_TARGETS else 136


def newest_stable_chrome():
    """Current public stable Chrome major, from the live Google version API.

    Waits briefly for the background fetch so the first profile of a run does
    not fall back to a stale number. Falls back to the newest impersonatable
    target when the API is unreachable.
    """
    _chrome_versions_ready.wait(6.0)
    majors = []
    with _versions_lock:
        for vers in _OFFICIAL_CHROME_VERSIONS.values():
            for v in vers:
                try:
                    majors.append(int(str(v).split(".")[0]))
                except (TypeError, ValueError):
                    pass
    return max(majors) if majors else max_impersonatable_chrome()


def pick_chrome_impersonation(major_ver):
    """Highest shipped Chrome TLS profile not newer than the version claimed.

    The old ladder in utils/gateway.py only knew 120-136 and fell through to
    chrome136 for anything else, so a profile claiming Chrome 152 sent a Chrome
    136 handshake.
    """
    try:
        major = int(str(major_ver).split(".")[0])
    except (TypeError, ValueError):
        major = 0
    best = None
    for ver, name in _CHROME_TARGETS:
        if ver <= major:
            best = name
    return best or (_CHROME_TARGETS[-1][1] if _CHROME_TARGETS else "chrome136")


def chromium_major_from_profile(profile):
    """The Chromium major a profile really presents.

    On a Discord desktop profile `browser_version` is the Electron version while
    the user agent carries the real Chromium, and the TLS profile has to match
    the user agent, not the Electron number.
    """
    if not profile:
        return None
    ua = profile.get("user_agent") or ""
    m = re.search(r"Chrome/(\d+)", ua)
    if m:
        return int(m.group(1))
    try:
        return int(str(profile.get("browser_version", "")).split(".")[0])
    except (TypeError, ValueError):
        return None


def _reduce_chrome_ver(ver):
    """Chrome freezes the minor components of its user agent: it reports
    MAJOR.0.0.0 and never the full build. Verified against this tree's own
    captures -- 1074 user agents in other-joiner.xml and 1 in
    websocket_history.xml, every one MAJOR.0.0.0 and not a single full build. A
    profile emitting Chrome/150.0.7871.114 is identifiable as not-a-browser from
    the user agent alone."""
    return f"{str(ver).split('.', 1)[0]}.0.0.0"


def _get_official_chrome_ver(plat_key="win", rng=None):
    """A Chrome version string in the reduced MAJOR.0.0.0 form a real Chrome sends.

    The pool is the current public stable and the two before it, newest
    weighted heaviest -- Chrome auto-updates, so nearly everyone is on the
    current major within days. It is deliberately NOT capped at what curl_cffi
    can impersonate: the TLS profile is picked separately as the nearest target
    at or below the announced major (pick_chrome_impersonation), and curl_cffi
    only adds a target when the handshake actually changes, so the handshake
    still matches. Capping here meant the live 151/152 were fetched and then
    thrown away, and every profile announced 145-150 while real users were on
    152 -- a browser several majors behind is its own signal.
    """
    top = newest_stable_chrome()
    majors = [top - 2, top - 1, top]
    return _reduce_chrome_ver((rng or random).choices(majors, weights=[1, 2, 5])[0])


def get_dynamic_mac_os_version():
    """Dynamically synthesize strictly modern, active macOS releases (macOS 15 Sequoia, 14 Sonoma, 13 Ventura)."""
    tier = random.choices(["sequoia", "sonoma", "ventura"], weights=[60, 30, 10])[0]
    if tier == "sequoia":
        minor = random.choice([0, 1, 2, 3, 4])
        patch = random.choice([0, 1, 2])
        return f"15.{minor}.{patch}"
    elif tier == "sonoma":
        minor = random.choice([4, 5, 6, 7])
        patch = random.choice([0, 1, 2])
        return f"14.{minor}.{patch}"
    else:
        minor = random.choice([5, 6, 7])
        patch = random.choice([0, 1, 2])
        return f"13.{minor}.{patch}"


def get_dynamic_win_os_version():
    """Dynamically synthesize verified modern Windows OS builds (Windows 11 24H2/23H2/22H2 & Windows 10 22H2)."""
    builds = [
        "10.0.26100",  # Windows 11 24H2
        "10.0.22631",  # Windows 11 23H2
        "10.0.22621",  # Windows 11 22H2
        "10.0.19045",  # Windows 10 22H2
    ]
    return random.choices(builds, weights=[45, 30, 15, 10])[0]


def get_dynamic_linux_os_version():
    """Dynamically synthesize strictly modern Linux kernel releases from live kernel.org registry or LTS fallbacks."""
    with _versions_lock:
        if _OFFICIAL_LINUX_KERNELS:
            return random.choice(_OFFICIAL_LINUX_KERNELS)
    kernels = [
        "6.18.0-1-generic",        # Linux 6.18 LTS
        "6.12.10-arch1-1",         # Linux 6.12 LTS
        "6.8.0-45-generic",        # Ubuntu 24.04 LTS
        "6.6.75-generic",          # Linux 6.6 LTS
        "6.1.128-generic",         # Linux 6.1 LTS
        "x86_64",                  # Generic
    ]
    return random.choices(kernels, weights=[25, 25, 25, 10, 10, 5])[0]


def get_dynamic_darwin_kernel_version():
    """Dynamically synthesize verified modern macOS Darwin kernel releases (macOS 15 Sequoia -> Darwin 24.x, macOS 14 Sonoma -> Darwin 23.x, macOS 13 Ventura -> Darwin 22.x)."""
    kernels = [
        # macOS 15 (Sequoia) Darwin 24.x releases
        "24.4.0", "24.3.0", "24.2.0", "24.1.0", "24.0.0",
        # macOS 14 (Sonoma) Darwin 23.x releases
        "23.6.0", "23.5.0", "23.4.0", "23.3.0",
        # macOS 13 (Ventura) Darwin 22.x releases
        "22.6.0", "22.5.0", "22.4.0",
    ]
    return random.choices(
        kernels,
        weights=[20, 15, 15, 10, 10, 8, 7, 5, 4, 3, 2, 1]
    )[0]


def get_dynamic_discord_client_version(plat):
    """Dynamically synthesize verified Discord Desktop client versions from live manifests."""
    with _versions_lock:
        vers = _OFFICIAL_DISCORD_VERSIONS.get(plat)
    if vers:
        return random.choice(vers)

    if plat == "linux":
        versions = [
            "1.0.154",
            "1.0.152",
            "0.0.95",
            "0.0.92",
            "0.0.89",
        ]
        return random.choices(versions, weights=[40, 30, 15, 10, 5])[0]
    elif plat == "mac":
        versions = [
            "0.0.408",
            "0.0.405",
            "0.0.395",
            "0.0.380",
        ]
        return random.choices(versions, weights=[40, 30, 20, 10])[0]
    else:
        versions = [
            "1.0.9254",  # Live production latest
            "1.0.9250",
            "1.0.9245",
            "1.0.9238",
            "1.0.9220",
            "1.0.9210",
            "1.0.9195",
            "1.0.9171",
        ]
        return random.choices(versions, weights=[35, 20, 15, 10, 10, 5, 3, 2])[0]


_ELECTRON_FALLBACK_PAIRS = [
    # (electron_version, chromium_full_version) -- real releases, mirroring the
    # electron-to-chromium registry fetched at startup.
    ("43.0.0", "150.0.7871.46"),
    ("42.0.0", "148.0.7778.96"),
    ("41.0.0", "146.0.7680.65"),
    ("40.0.0", "144.0.7559.60"),
    ("39.0.0", "142.0.7444.52"),
    ("38.0.0", "140.0.7339.41"),
]


def _exactly_impersonatable_pairs(pairs):
    """Keep only Electron releases whose Chromium major curl_cffi ships a profile for.

    An Electron app reports its real Chromium build in the user agent, and
    curl_cffi only ships TLS profiles for certain majors. Electron 42 carries
    Chromium 148, which falls back to a chrome146 handshake -- a two-major split
    between what the user agent claims and what the socket does. Restricting the
    pool to exact matches removes that without inventing a pairing: every pair
    kept is a real Electron release, just one whose Chromium can be reproduced.
    """
    exact = {major for major, _ in _CHROME_TARGETS}
    kept = [pr for pr in pairs if str(pr[1]).split(".")[0].isdigit()
            and int(str(pr[1]).split(".")[0]) in exact]
    return kept or list(pairs)


def get_dynamic_electron_and_chromium():
    """
    Dynamically synthesize verified paired Electron and Chromium versions from live registry.
    """
    with _versions_lock:
        live = list(_OFFICIAL_ELECTRON_PAIRS)
    if live:
        return random.choice(_exactly_impersonatable_pairs(live))

    pairs = _exactly_impersonatable_pairs(_ELECTRON_FALLBACK_PAIRS)
    # Newest weighted heaviest: Discord desktop auto-updates.
    weights = list(range(1, len(pairs) + 1))[::-1]
    return random.choices(pairs, weights=weights)[0]


# Only platforms we hold a real web-client capture for are emitted. Every one
# of the 522 captured authenticated requests is Linux; the Windows and macOS
# templates stay defined so they can be switched on once a capture of each
# exists to verify them against, but nothing is sent that has not been checked.
ENABLED_PLATFORMS = ("linux",)

_PROFILES_TEMPLATES = [
    # Chrome Web Client on Windows 11/10 (x64) - Matches Burp Suite Ground Truth
    {
        "plat_key": "win",
        "client_type": "web",
        "os": "Windows",
        "browser": "Chrome",
        "os_version": "10",
        "os_arch": "x64",
        "app_arch": "x64",
        "ua_builder": lambda ver: f"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{ver} Safari/537.36",
        "sec_ua_builder": lambda major: build_sec_ch_ua(major),
        "sec_platform": '"Windows"'
    },
    # Chrome Web Client on Linux (x64) - Exact match from Burp XML capture
    {
        "plat_key": "linux",
        "client_type": "web",
        "os": "Linux",
        "browser": "Chrome",
        "os_version": "",
        "os_arch": "x64",
        "app_arch": "x64",
        "ua_builder": lambda ver: f"Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{ver} Safari/537.36",
        "sec_ua_builder": lambda major: build_sec_ch_ua(major),
        "sec_platform": '"Linux"'
    },
    # Chrome Web Client on macOS (ARM64 Apple Silicon)
    {
        "plat_key": "mac",
        "client_type": "web",
        "os": "Mac OS X",
        "browser": "Chrome",
        "os_version": "10.15.7",  # ua-parser of "Intel Mac OS X 10_15_7"; Windows gives "10", Linux ""
        "os_arch": "arm64",
        "app_arch": "arm64",
        "ua_builder": lambda ver: f"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{ver} Safari/537.36",
        "sec_ua_builder": lambda major: build_sec_ch_ua(major),
        "sec_platform": '"macOS"'
    },
]

# Chromium derives its sec-ch-ua GREASE entry from the major version
# (components/embedder_support/user_agent_utils.cc): the brand punctuation, the
# greased version, and the order of the three entries all move with it. The
# profiles below hardcoded '"Not)A;Brand";v="24"' with Chrome always first, which
# is only correct for majors like 149. Since the Chrome version is fetched live,
# most majors produced a header no real browser sends.
_GREASE_CHARS = [" ", "(", ":", "-", ".", "/", ")", ";", "=", "?", "_"]
_GREASE_VERSIONS = ["8", "99", "24"]
_GREASE_ORDERS = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]


def build_sec_ch_ua(major, brand="Google Chrome"):
    """Reproduce Chromium's sec-ch-ua for a given major version."""
    seed = int(major)
    greased = 'Not{}A{}Brand'.format(
        _GREASE_CHARS[seed % len(_GREASE_CHARS)],
        _GREASE_CHARS[(seed + 1) % len(_GREASE_CHARS)],
    )
    order = _GREASE_ORDERS[seed % len(_GREASE_ORDERS)]
    entries = [None, None, None]
    entries[order[0]] = f'"{greased}";v="{_GREASE_VERSIONS[seed % len(_GREASE_VERSIONS)]}"'
    entries[order[1]] = f'"Chromium";v="{seed}"'
    entries[order[2]] = f'"{brand}";v="{seed}"'
    return ", ".join(entries)


def _selftest_sec_ch_ua():
    # Matches the Burp capture (Chrome 149 engine).
    assert build_sec_ch_ua(149) == '"Google Chrome";v="149", "Chromium";v="149", "Not)A;Brand";v="24"'
    # Independent check: the real Chrome 120 header, not derived from any capture here.
    assert build_sec_ch_ua(120) == '"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"'
    for v in range(100, 200):
        out = build_sec_ch_ua(v)
        assert out.count(';v=') == 3, out
        assert f'"Chromium";v="{v}"' in out, out
    print("sec_ch_ua selftest OK")


def generate_installation_id(rng=None) -> str:
    """Generate a genuine Discord installation_id matching official client format (Snowflake.27-char base64).

    The real client makes one per install and keeps it in localStorage, so it is
    part of the device. Drawn from the token-seeded rng it survives a lost edge
    cache like the rest of the identity; unseeded it changed on every regenerate
    and the same account came back as a fresh install.
    """
    r = rng or random
    prefix = r.randint(1500000000000000000, 1600000000000000000)
    suffix = base64.urlsafe_b64encode(r.getrandbits(160).to_bytes(20, "big")).decode("utf-8").rstrip("=")
    return f"{prefix}.{suffix}"


def get_random_profile(build_number, token=None):
    """Build a device profile. Passing `token` pins the device to that account.

    The OS, browser and Chrome version were drawn at random on every call, so an
    account could present as Windows Chrome on one run and macOS Discord Desktop
    on the next. The edge cache masked this for 30 days, but any cache loss --
    or a token used before the cache existed -- reintroduced it, and an account
    that changes operating system between sessions is the strongest new-device
    signal there is. Seeding the draw from the token makes the identity a pure
    function of the account: stable across runs, across machines, and across a
    deleted cache, with no state file to lose. The distribution across accounts is
    unchanged, because the seed is a hash.
    """
    rng = random
    if token:
        rng = random.Random(int.from_bytes(
            hashlib.sha256(str(token).encode("utf-8")).digest()[:16], "big"
        ))
    tmpl = rng.choice([t for t in _PROFILES_TEMPLATES if t["plat_key"] in ENABLED_PLATFORMS])
    chrome_ver = _get_official_chrome_ver(tmpl["plat_key"], rng=rng)
    major_ver = chrome_ver.split(".")[0]

    ua = tmpl["ua_builder"](chrome_ver)
    sec_ua = tmpl["sec_ua_builder"](major_ver)
    sec_platform = tmpl["sec_platform"]

    launch_id = str(uuid.uuid4())
    launch_sig = str(uuid.uuid4())
    heartbeat_session_id = str(uuid.uuid4())
    installation_id = generate_installation_id(rng=rng)

    # 1:1 Coherent Discord Web Super Properties schema matching Burp captures
    super_props = {
        "os": tmpl["os"],
        "browser": tmpl["browser"],
        "device": "",
        "system_locale": "en-US",
        "has_client_mods": False,
        "browser_user_agent": ua,
        "browser_version": chrome_ver,
        "os_version": tmpl["os_version"],
        "referrer": "https://discord.com/",
        "referring_domain": "discord.com",
        "referrer_current": "https://discord.com/",
        "referring_domain_current": "discord.com",
        "release_channel": "stable",
        "client_build_number": build_number,
        "client_event_source": None,
        "client_launch_id": launch_id,
        "launch_signature": launch_sig,
        "client_heartbeat_session_id": heartbeat_session_id,
        "client_app_state": "focused",
    }

    raw = json.dumps(super_props, separators=(",", ":")).encode()
    encoded = base64.b64encode(raw).decode()

    return {
        "os": tmpl["os"],
        "browser": tmpl["browser"],
        "os_version": tmpl["os_version"],
        "os_arch": tmpl["os_arch"],
        "app_arch": tmpl["app_arch"],
        "browser_version": chrome_ver,
        "user_agent": ua,
        "sec_ch_ua": sec_ua,
        "sec_ch_ua_platform": sec_platform,
        "client_launch_id": launch_id,
        "launch_signature": launch_sig,
        "client_heartbeat_session_id": heartbeat_session_id,
        "installation_id": installation_id,
        "super_properties": encoded,
        "super_properties_raw": super_props,
    }


# ── Invite attribution ─────────────────────────────────────────────────────
# Verified against discord_requests.xml and discord-new-brup-list.xml (579
# discord.com requests). referrer_current / referring_domain_current are NEVER
# empty on REST; a directory referral adds utm_source_current, utm_medium_current
# and utm_campaign_current after referring_domain_current and before
# release_channel, the 22-key form seen 39 times, always paired with a matching
# utm query in the Referer.
INVITE_ATTRIBUTIONS = [
    (65, {
        "referer_query": None,
        "referrer_current": "https://discord.com/app/invite-with-guild-onboarding/{code}",
        "referring_domain_current": "discord.com",
    }),
    (35, {
        "referer_query": "utm_source=disboard&utm_medium=external_directory&utm_campaign=organic_discovery",
        "referrer_current": "https://disboard.org/",
        "referring_domain_current": "disboard.org",
        "utm_source_current": "disboard",
        "utm_medium_current": "external_directory",
        "utm_campaign_current": "organic_discovery",
    }),
]


def pick_invite_attribution(provider=None):
    """Choose how this invite was arrived at."""
    if provider == "disboard":
        return INVITE_ATTRIBUTIONS[1][1]
    if provider == "direct":
        return INVITE_ATTRIBUTIONS[0][1]
    return random.choices([a for _, a in INVITE_ATTRIBUTIONS],
                          weights=[w for w, _ in INVITE_ATTRIBUTIONS])[0]


def build_attributed_super_properties(profile, attribution, invite_code=""):
    """Re-encode x-super-properties so it agrees with the Referer being sent.

    Returns None if the profile has no usable super_properties, so callers can
    leave the existing header alone rather than send a broken one.
    """
    if not profile or not attribution:
        return None
    try:
        props = json.loads(base64.b64decode(profile.get("super_properties", "")))
    except Exception:
        return None
    if not isinstance(props, dict) or "referring_domain_current" not in props:
        return None

    code = str(invite_code).split("?", 1)[0]
    out = {}
    for key, value in props.items():
        if key == "referrer_current":
            out[key] = attribution["referrer_current"].replace("{code}", code)
            continue
        if key == "referring_domain_current":
            out[key] = attribution["referring_domain_current"]
            # The utm keys sit between referring_domain_current and
            # release_channel in every captured 22-key header.
            for utm in ("utm_source_current", "utm_medium_current", "utm_campaign_current"):
                if utm in attribution:
                    out[utm] = attribution[utm]
            continue
        if key.startswith("utm_"):
            continue  # rebuilt above, in the captured position
        out[key] = value
    return base64.b64encode(json.dumps(out, separators=(",", ":")).encode()).decode()


def _repair_desktop_profile(profile, sp):
    """Snap a cached desktop profile onto an Electron/Chromium pair the TLS layer
    can reproduce exactly.

    Unlike Chrome web, an Electron app does report its full Chromium build, so
    the build number is left intact. What is corrected is the pairing: a cached
    Electron 42 / Chromium 148 profile opens its socket with a chrome146
    handshake, two majors below what its user agent claims. The replacement is a
    real registry pair, so the Electron and Chromium numbers still belong
    together.
    """
    ua = profile.get("user_agent") or ""
    m = re.search(r"Chrome/([\d.]+)", ua)
    if not m:
        return profile
    cached = m.group(1)
    major = int(cached.split(".")[0])
    if major in {mj for mj, _ in _CHROME_TARGETS}:
        return profile  # already exact

    with _versions_lock:
        live = list(_OFFICIAL_ELECTRON_PAIRS)
    pairs = _exactly_impersonatable_pairs(live or _ELECTRON_FALLBACK_PAIRS)
    below = [pr for pr in pairs if int(str(pr[1]).split(".")[0]) <= major]
    electron_ver, chromium_ver = (max(below, key=lambda pr: int(str(pr[1]).split(".")[0]))
                                  if below else min(pairs, key=lambda pr: int(str(pr[1]).split(".")[0])))

    repaired = dict(profile)
    repaired["user_agent"] = ua.replace(f"Chrome/{cached}", f"Chrome/{chromium_ver}")
    if str(profile.get("browser_version", "")).split(".")[0].isdigit() and \
            int(str(profile.get("browser_version", "0")).split(".")[0]) < 100:
        repaired["browser_version"] = electron_ver
    sp = dict(sp)
    sp["browser_user_agent"] = repaired["user_agent"]
    if "client_version" not in sp:
        sp["browser_version"] = electron_ver
    repaired["super_properties"] = base64.b64encode(
        json.dumps(sp, separators=(",", ":")).encode()
    ).decode()
    log.debug(f"Repaired desktop profile: Chromium {cached} -> {chromium_ver} (Electron {electron_ver})")
    return repaired


def repair_cached_profile(profile):
    """Bring a profile written by an older build back into fingerprint coherence.

    The edge cache is valid for 30 days and is replayed verbatim, so a profile
    stored before the user-agent and TLS fixes keeps serving the old identity for
    a month: a full build number in the user agent (real Chrome sends
    MAJOR.0.0.0) and often a major above what this curl_cffi can imitate at the
    TLS layer, which is the split fingerprint those fixes exist to remove.

    Only version-dependent fields are rewritten, and web and desktop profiles are
    handled differently: a desktop profile really does report its Electron and
    Chromium versions, so it is snapped onto an impersonatable pair rather than
    frozen.
    """
    if not profile or not isinstance(profile, dict):
        return profile

    sp = {}
    try:
        sp = json.loads(base64.b64decode(profile.get("super_properties", "")))
    except Exception:
        pass

    if str(sp.get("browser", profile.get("browser", ""))).strip() == "Discord Client":
        return _repair_desktop_profile(profile, sp)

    ua = profile.get("user_agent") or ""
    m = re.search(r"Chrome/([\d.]+)", ua)
    if not m:
        return profile
    cached_ver = m.group(1)
    major = int(cached_ver.split(".")[0])
    top = newest_stable_chrome()
    floor = top - 2

    needs_reduction = cached_ver != _reduce_chrome_ver(cached_ver)
    # Ahead of public stable is impossible; more than two majors behind is a
    # browser that stopped auto-updating. Either way move it to the current
    # stable -- a version bump on the same installation is what a real Chrome
    # does every few weeks, and is not a new-device signal (OS, installation
    # id and timezone are untouched).
    out_of_range = major > top or major < floor
    stale_sec_ua = profile.get("sec_ch_ua") not in (None, "") and \
        profile.get("sec_ch_ua") != build_sec_ch_ua(major)
    # An older template stored "" for macOS; the client derives "10.15.7" from
    # the Mac user agent, so "" disagrees with the UA on the same request.
    bad_mac_ver = sp.get("os") == "Mac OS X" and not sp.get("os_version")

    if not (needs_reduction or out_of_range or stale_sec_ua or bad_mac_ver):
        return profile

    new_major = top if out_of_range else major
    new_ver = _reduce_chrome_ver(new_major)

    repaired = dict(profile)
    repaired["user_agent"] = re.sub(r"Chrome/[\d.]+", f"Chrome/{new_ver}", ua)
    repaired["browser_version"] = new_ver
    if profile.get("sec_ch_ua"):
        repaired["sec_ch_ua"] = build_sec_ch_ua(new_major)

    if sp:
        sp["browser_user_agent"] = repaired["user_agent"]
        sp["browser_version"] = new_ver
        if bad_mac_ver:
            sp["os_version"] = "10.15.7"
            repaired["os_version"] = "10.15.7"
        repaired["super_properties"] = base64.b64encode(
            json.dumps(sp, separators=(",", ":")).encode()
        ).decode()

    log.debug(f"Repaired cached profile: Chrome/{cached_ver} -> Chrome/{new_ver} (public stable {top})")
    return repaired


def refresh_session_launch_identifiers(profile, build_number=None):
    """
    Refreshes runtime session and boot identifiers for a new launch matching genuine browser behavior:
    - installation_id: 100% PERSISTENT (remains bound to device/token on disk)
    - cookies (__dcfduid, __sdcfduid): 100% PERSISTENT (30-day edge cache)
    - client_launch_id: REGENERATED (crypto.randomUUID() on tab/app boot)
    - launch_signature: REGENERATED (paired with client_launch_id for this boot)
    - client_heartbeat_session_id: REGENERATED (unique UUID per gateway session)
    - super_properties: Re-encoded with updated launch_id, launch_sig, heartbeat_id, and latest buildNumber
    """
    if not profile or not isinstance(profile, dict):
        return profile

    new_profile = dict(profile)
    launch_id = str(uuid.uuid4())
    launch_sig = str(uuid.uuid4())
    heartbeat_session_id = str(uuid.uuid4())

    # A new client_launch_id is a new page load, so the attribution that was
    # pinned to the previous one must not carry over. These markers are also
    # stripped from anything restored out of the edge cache.
    new_profile.pop("_launch_attribution", None)
    new_profile.pop("_launch_invite", None)

    new_profile["client_launch_id"] = launch_id
    new_profile["launch_signature"] = launch_sig
    new_profile["client_heartbeat_session_id"] = heartbeat_session_id

    # Preserve or generate installation_id
    if not new_profile.get("installation_id"):
        new_profile["installation_id"] = generate_installation_id()

    os_name = new_profile.get("os", "Windows")
    os_ver_default = "10" if os_name == "Windows" else ""
    os_ver = new_profile.get("os_version", os_ver_default)
    browser_name = new_profile.get("browser", "Chrome")
    browser_ver = new_profile.get("browser_version") or _get_official_chrome_ver("win" if os_name == "Windows" else ("linux" if os_name == "Linux" else "mac"))
    ua_val = new_profile.get("user_agent") or USER_AGENT

    # Update super_properties JSON
    super_props = {
        "os": os_name,
        "browser": browser_name,
        "device": "",
        "system_locale": "en-US",
        "has_client_mods": False,
        "browser_user_agent": ua_val,
        "browser_version": browser_ver,
        "os_version": os_ver,
        "referrer": "https://discord.com/",
        "referring_domain": "discord.com",
        "referrer_current": "https://discord.com/",
        "referring_domain_current": "discord.com",
        "release_channel": "stable",
        "client_build_number": build_number or new_profile.get("client_build_number", 599735),
        "client_event_source": None,
        "client_launch_id": launch_id,
        "launch_signature": launch_sig,
        "client_heartbeat_session_id": heartbeat_session_id,
        "client_app_state": "focused",
    }
    raw = json.dumps(super_props, separators=(",", ":")).encode()
    new_profile["super_properties"] = base64.b64encode(raw).decode()
    new_profile["super_properties_raw"] = super_props

    return new_profile


# Fallback module globals for legacy imports
_default_profile = get_random_profile(599735)
USER_AGENT = _default_profile["user_agent"]
SEC_CH_UA = _default_profile["sec_ch_ua"]
SEC_CH_UA_PLATFORM = _default_profile["sec_ch_ua_platform"]


def get_build_number(proxy=None):
    global _cached_build_number
    if _cached_build_number is not None:
        return _cached_build_number

    with _build_number_lock:
        if _cached_build_number is not None:
            return _cached_build_number

        try:
            sess = StealthSession(timeout=default_request_timeout())
            # This is a page load of discord.com, so it goes out through the
            # token's proxy from the start (the first GET used to be direct,
            # leaking the host IP) and on the current Chrome's handshake with a
            # matching Linux UA rather than stealth_requests' chrome136 default.
            if proxy:
                proxy_url = format_proxy_url(proxy)
                if proxy_url:
                    sess.proxies = {"http": proxy_url, "https": proxy_url}
                    if "127.0.0.1" in proxy_url or "localhost" in proxy_url or "8080" in proxy_url:
                        sess.verify = False
            _top = newest_stable_chrome()
            sess.impersonate = pick_chrome_impersonation(_top)
            sess.headers["user-agent"] = next(
                t for t in _PROFILES_TEMPLATES if t["plat_key"] == "linux"
            )["ua_builder"](_reduce_chrome_ver(_top))
            page = sess.get("https://discord.com/app", timeout=15).text

            assets = re.findall(r'src="/assets/([^\"]+)"', page)

            for _, asset in enumerate(reversed(assets)):
                js = sess.get(f"https://discord.com/assets/{asset}", timeout=15).text
                if "buildNumber:" in js:
                    try:
                        build = int(js.split('buildNumber:"')[1].split('"')[0])
                        log.debug(
                            f"Found build number {Fore.WHITE}→{Style.RESET_ALL} "
                            f"build={Fore.CYAN}{build}{Style.RESET_ALL} "
                            f"asset={Fore.CYAN}{asset}{Style.RESET_ALL}"
                        )
                        _cached_build_number = build
                        return build
                    except Exception as e:
                        log.debug(
                            f"Build number parse failed {Fore.WHITE}→{Style.RESET_ALL} "
                            f"asset={Fore.CYAN}{asset}{Style.RESET_ALL} "
                            f"err={Fore.LIGHTRED_EX}{e!r}{Style.RESET_ALL}"
                        )
        except Exception as e:
            log.warning(
                f"Build number fetch timed out/failed ({e}). Using cached build number 599735."
            )
        
        # Default build fallback
        _cached_build_number = 599735
        return 599735


def build_super_properties(build_number):
    return get_random_profile(build_number)["super_properties"]


def fetch_cookies(session, profile=None):

    headers = {
        "accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
        "accept-encoding": "gzip, deflate, br, zstd",
        "accept-language": "en-US,en;q=0.9",
        "sec-ch-ua": profile["sec_ch_ua"] if profile and profile.get("sec_ch_ua") else SEC_CH_UA,
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": profile["sec_ch_ua_platform"] if profile and profile.get("sec_ch_ua_platform") else SEC_CH_UA_PLATFORM,
        "sec-fetch-dest": "document",
        "sec-fetch-mode": "navigate",
        "sec-fetch-site": "none",
        "sec-fetch-user": "?1",
        "upgrade-insecure-requests": "1",
        "user-agent": profile["user_agent"] if profile else USER_AGENT,
    }
    # Clean up None values
    headers = {k: v for k, v in headers.items() if v is not None}
    session.headers = headers

    session.get("https://discord.com")

    cookies = session.cookies.get_dict()
    dcfduid = cookies.get("__dcfduid")
    sdcfduid = cookies.get("__sdcfduid")

    log.debug(
        f"Cookies fetched {Fore.WHITE}→{Style.RESET_ALL} "
        f"dcfduid={Fore.CYAN}{'present' if dcfduid else 'missing'}{Style.RESET_ALL} "
        f"sdcfduid={Fore.CYAN}{'present' if sdcfduid else 'missing'}{Style.RESET_ALL} "
        f"total_cookies={Fore.CYAN}{len(cookies)}{Style.RESET_ALL}"
    )

    return dcfduid, sdcfduid


def get_fingerprint(session, dcfduid, sdcfduid, profile=None):
    super_props = profile.get("super_properties") if profile else None

    headers = {
        "accept": "*/*",
        "accept-encoding": "gzip, deflate, br, zstd",
        "accept-language": "en-US,en;q=0.9",
        "content-type": "application/json",
        "cookie": f"__dcfduid={dcfduid}; __sdcfduid={sdcfduid}",
        "origin": "https://discord.com",
        "referer": "https://discord.com/",
        "priority": "u=1, i",
        "sec-ch-ua": profile["sec_ch_ua"] if profile and profile.get("sec_ch_ua") else SEC_CH_UA,
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": profile["sec_ch_ua_platform"] if profile and profile.get("sec_ch_ua_platform") else SEC_CH_UA_PLATFORM,
        "sec-fetch-dest": "empty",
        "sec-fetch-mode": "cors",
        "sec-fetch-site": "same-origin",
        "user-agent": profile["user_agent"] if profile else USER_AGENT,
        "x-debug-options": "bugReporterEnabled",
        "x-discord-locale": "en-US",
        "x-super-properties": super_props,
    }
    # Clean up None values
    headers = {k: v for k, v in headers.items() if v is not None}
    session.headers = headers

    res = session.get("https://discord.com/api/v9/experiments?with_guild_experiments=true")

    if res.status_code != 200:
        raise RuntimeError(
            f"experiments returned status={res.status_code} error={res.text[:200]}"
        )

    try:
        fp = res.json().get("fingerprint")
    except ValueError as e:
        raise RuntimeError(f"experiments non-json error={res.text[:200]}") from e

    if not fp:
        raise RuntimeError(f"experiments missing fingerprint field error={res.text[:200]}")

    log.info(
        f"Fingerprint acquired {Fore.WHITE}→{Style.RESET_ALL} "
        f"{Fore.CYAN}{fp}{Style.RESET_ALL}"
    )
    return fp


BODY_ORIGIN = {"origin": "https://discord.com"}


def apply_tls_profile(session, profile):
    """Point a curl_cffi session's TLS handshake at the Chrome the profile announces.

    stealth_requests hardcodes impersonate='chrome136', and curl_cffi's
    impersonation adds a browser's PAGE-NAVIGATION default headers
    (Upgrade-Insecure-Requests, Sec-Fetch-User) that no XHR ever carries.
    Verified live against a TLS echo: the REST JA4 was Chrome 136's while the
    user agent said 152 and the gateway handshook as 150 -- every API request
    disagreed with its own UA. Both are per-request attributes on the session,
    so set them once the announced profile is known. build_headers supplies
    the complete XHR header set, so the defaults are not needed.
    """
    session.impersonate = pick_chrome_impersonation(chromium_major_from_profile(profile))
    session.default_headers = False
    return session


def build_headers(fingerprint=None, super_props=None, timezone="America/Los_Angeles", profile=None,
                  include_fingerprint=False, token=None, referer="https://discord.com/"):
    # Real Discord client only sends x-fingerprint on unauthenticated
    # endpoints (register, login, pre-auth /science). Sending it on authenticated API calls
    # is a bot fingerprint.
    #
    # Key order is the wire order of a real Chrome XHR to the API (captured live
    # from the web client); curl_cffi sends custom headers in the order given.
    # content-type and origin are NOT session-level. Across 558 authenticated
    # requests in the captures, 273 of 277 GETs carry neither, and every
    # request that does carry them has a body. Putting them on the session
    # stamped them onto every GET the browsing simulation makes, which no
    # real client does. curl_cffi adds content-type itself for `json=`
    # requests; origin is added per-POST via BODY_ORIGIN.
    headers = {
        "sec-ch-ua-platform": profile["sec_ch_ua_platform"] if profile and profile.get("sec_ch_ua_platform") else SEC_CH_UA_PLATFORM,
        # authorization sits second on the wire in the capture, not appended
        # last after everything else the way a later .update() put it.
        "authorization": token,
        "x-installation-id": profile.get("installation_id") if profile else None,
        "x-debug-options": "bugReporterEnabled",
        "sec-ch-ua": profile["sec_ch_ua"] if profile and profile.get("sec_ch_ua") else SEC_CH_UA,
        "sec-ch-ua-mobile": "?0",
        "x-discord-timezone": timezone,
        "x-fingerprint": fingerprint if (include_fingerprint and fingerprint) else None,
        "x-super-properties": super_props,
        "x-discord-locale": "en-US",
        "user-agent": profile["user_agent"] if profile else USER_AGENT,
        "accept": "*/*",
        "accept-language": "en-US,en;q=0.9",
        "sec-fetch-site": "same-origin",
        "sec-fetch-mode": "cors",
        "sec-fetch-dest": "empty",
        "referer": referer,
        "accept-encoding": "gzip, deflate, br, zstd",
        "priority": "u=1, i",
    }
    # Clean up None values
    headers = {k: v for k, v in headers.items() if v is not None}

    log.debug(
        f"API headers built {Fore.WHITE}→{Style.RESET_ALL} "
        f"header_count={Fore.CYAN}{len(headers)}{Style.RESET_ALL}"
    )
    return headers''',
    'utils.core': r'''import time, os, logging, sys, json


from colorama import Fore, Style

from utils.version import __version__
from config import load_config

config = load_config()
START_TIME = time.time()


# ! CUSTOM LEVELS
AD_LEVEL = 25
logging.addLevelName(AD_LEVEL, "AD")


def ad(self, message, *args, **kwargs):
    if self.isEnabledFor(AD_LEVEL):
        self._log(AD_LEVEL, message, args, **kwargs)


logging.Logger.ad = ad


# ! STATS
STATS = {
    "checked": 0,
    "valid": 0,
    "unlocked": 0,
    "invalid": 0,
    "locked": 0,
    "rate": 0,
    "error": 0,
    "captcha_solves": 0,
}


# ! CPM
def get_cpm():
    elapsed = time.time() - START_TIME

    total = (
        STATS["unlocked"] +
        STATS["invalid"] +
        STATS["locked"] +
        STATS["rate"] +
        STATS["error"]
    )

    return round((total / elapsed) * 60, 2) if elapsed > 0 else 0.0


# ! LIVE
def update_stats(code):
    STATS["checked"] += 1

    if code == 200:
        STATS["valid"] += 1
    elif code == 401:
        STATS["invalid"] += 1
    elif code == 403:
        STATS["locked"] += 1
    elif code == 429:
        STATS["rate"] += 1
    else:
        STATS["error"] += 1


# ! FORMAT
def format_token_id(token: str) -> str:
    if token and len(token) > 10:
        return f"{token[:4]}...{token[-4:]}"
    elif token and len(token) > 0:
        return f"{token[:4]}.."
    else:
        return "Unknown***"





import contextvars

worker_id_var = contextvars.ContextVar("worker_id", default=None)

# ! HELPER
class BitFillerFormatter(logging.Formatter):
    LEVEL_STYLES = {
        "DEBUG": Fore.BLUE + "DBG",
        "INFO": Fore.CYAN + Style.BRIGHT + "INF",
        "AD": Fore.LIGHTMAGENTA_EX + Style.BRIGHT + "ADS",
        "WARNING": Fore.YELLOW + Style.BRIGHT + "WRN",
        "ERROR": Fore.LIGHTRED_EX + Style.BRIGHT + "ERR",
        "CRITICAL": Fore.LIGHTRED_EX + Style.BRIGHT + "CRT",
    }

    SEP = Fore.LIGHTBLACK_EX + "│" + Style.RESET_ALL
    MSG_COLOR = Fore.WHITE

    def format(self, record):
        level = self.LEVEL_STYLES.get(record.levelname, record.levelname[:3].upper())
        time_str = time.strftime("%H:%M:%S", time.localtime(record.created))

        msg = record.getMessage()
        worker_id = worker_id_var.get()
        
        thread_part = ""
        if worker_id:
            thread_part = f"{Fore.LIGHTMAGENTA_EX}[{worker_id}]{Style.RESET_ALL} "

        time_tag = f"{Fore.LIGHTBLACK_EX}[{Fore.LIGHTCYAN_EX}{time_str}{Fore.LIGHTBLACK_EX}]{Style.RESET_ALL}"

        return f"{time_tag} {self.SEP} {level} {self.SEP} {thread_part}{msg}"


import re
ANSI_ESCAPE_RE = re.compile(r'\x1b\[[0-9;]*[a-zA-Z]')

class BitFillerFileFormatter(logging.Formatter):
    def format(self, record):
        orig_msg = record.msg
        worker_id = worker_id_var.get()
        if worker_id:
            record.msg = f"[{worker_id}] {orig_msg}"
        result = super().format(record)
        record.msg = orig_msg
        return ANSI_ESCAPE_RE.sub('', result)


# ! LOGGER
import threading
_logger_lock = threading.Lock()

def setup_logger(name="bitfiller"):
    logger = logging.getLogger(name)
    if logger.handlers:
        return logger

    with _logger_lock:
        if logger.handlers:
            return logger

        try:
            os.makedirs("log", exist_ok=True)
        except Exception:
            pass

        logger.setLevel(logging.DEBUG)

        debug_enabled = False
        try:
            # Safe read without recursive logger invocation
            if os.path.exists("input/config.json"):
                with open("input/config.json", "r", encoding="utf-8") as f:
                    cfg = json.load(f)
                    debug_enabled = bool(cfg.get("debug", False))
        except Exception:
            pass

        fmt = "%(message)s"
        console = logging.StreamHandler(sys.stdout)
        console.setLevel(logging.DEBUG if debug_enabled else logging.INFO)
        console.setFormatter(BitFillerFormatter(fmt))

        try:
            file = logging.FileHandler("log/logs.txt", encoding="utf-8")
            file.setLevel(logging.DEBUG if debug_enabled else logging.INFO)
            file.setFormatter(BitFillerFileFormatter(
                "%(asctime)s │ %(levelname)-5s │ %(message)s",
                "%Y-%m-%d %H:%M:%S"
            ))
            logger.addHandler(file)
        except Exception:
            pass

        logger.addHandler(console)
        return logger



log = setup_logger(__name__)

# ! MAP
STATUS_MAP = {
    200: ("✔ JOINED", Fore.GREEN),
    401: ("✖ INVALID", Fore.LIGHTRED_EX),
    403: ("🔒 LOCKED", Fore.LIGHTMAGENTA_EX),
    429: ("⏳ RATE", Fore.YELLOW),
}


def format_status(code):
    label, color = STATUS_MAP.get(code, ("✖ ERROR", Fore.LIGHTRED_EX))
    return f"{color}{Style.BRIGHT}{label:<9}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}[{code}]{Style.RESET_ALL}"


# ! SYSTEM 
def system(cmd=None, title=None):
    if cmd == "clear":
        os.system("cls" if os.name == "nt" else "clear")

    if title and os.name == "nt":
        os.system(f'title "{title}"')


# ! TITLE
_last = 0
def update_title(title=None, delay=0.5):
    if title is None:
        title = f"Bit Filler V{__version__}"

    global _last
    now = time.time()

    if now - _last > delay:
        cpm = get_cpm()

        total = (
            STATS["unlocked"] +
            STATS["locked"] +
            STATS["invalid"]
        )

        rate_percent = (
            (STATS["unlocked"] / total) * 100
            if total > 0 else 0
        )

        t = (
            f"{title} │ "
            f"Joined: {STATS['unlocked']} │ "
            f"Locked: {STATS['locked']} │ "
            f"Invalid: {STATS['invalid']} │ "
            f"Success: {rate_percent:.1f}% │ "
            f"CPM: {cpm}"
        )

        system(title=t)
        _last = now


# ! BANNER
def show_banner():
    import unicodedata, re

    c1 = Fore.CYAN
    c2 = Fore.LIGHTCYAN_EX
    m = Fore.LIGHTMAGENTA_EX
    w = Fore.WHITE
    dim = Fore.LIGHTBLACK_EX
    rst = Style.RESET_ALL
    b = Style.BRIGHT

    def display_width(text):
        clean = re.sub(r'\x1b\[[0-9;]*m', '', text)
        width = 0
        for ch in clean:
            if unicodedata.east_asian_width(ch) in ('F', 'W'):
                width += 2
            else:
                width += 1
        return width

    inner_w = 75
    lines = [
        "██████╗ ██╗████████╗    ███████╗██╗██╗     ██╗     ███████╗██████╗ ",
        "██╔══██╗██║╚══██╔══╝    ██╔════╝██║██║     ██║     ██╔════╝██╔══██╗",
        "██████╔╝██║   ██║       █████╗  ██║██║     ██║     █████╗  ██████╔╝",
        "██╔══██╗██║   ██║       ██╔══╝  ██║██║     ██║     ██╔══╝  ██╔══██╗",
        "██████╔╝██║   ██║       ██║     ██║███████╗███████╗███████╗██║  ██║",
        "╚══════╝╚═╝   ╚═╝       ╚═╝     ╚═╝╚══════╝╚══════╝╚══════╝╚═╝  ╚═╝",
    ]

    print(f"\n  {c1}{b}╔" + "═" * inner_w + f"╗{rst}")
    print(f"  {c1}{b}║" + " " * inner_w + f"║{rst}")
    for line in lines:
        pad = inner_w - 6 - len(line)
        print(f"  {c1}{b}║      {c2}{line}" + " " * pad + f"{c1}{b}║{rst}")
    print(f"  {c1}{b}║" + " " * inner_w + f"║{rst}")

    info_line = f"    {m}* {w}BIT FILLER {dim}v{__version__}{rst}  {dim}│{rst}  {c2}Multi-Threaded Discord Joiner & Solver Suite"
    pad_info = max(0, inner_w - display_width(info_line))
    print(f"  {c1}{b}║{rst}" + info_line + (" " * pad_info) + f"{c1}{b}║{rst}")
    print(f"  {c1}{b}╚" + "═" * inner_w + f"╝{rst}\n")


# ! EXIT
def exit_program():
    input("press enter to exit")

# ! ATOMIC JSON WRITE
def write_json_atomic(path, data, indent=2):
    """Write JSON to path atomically: temp file in the same directory, then rename.

    os.replace is atomic within a filesystem, so an interrupted write (crash,
    kill, full disk) can never leave a truncated file where the original was.
    Plain open(path, "w") truncates first, which on a multi-megabyte database
    means a mid-write crash destroys every record.
    """
    import tempfile
    path = str(path)
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=directory, prefix=".tmp-", suffix=".json")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=indent)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


# ! DEFAULT REQUEST TIMEOUT
def default_request_timeout():
    """Seconds before an HTTP request is abandoned.

    Nothing set a timeout: not stealth_requests, not the call sites. Every HTTP
    call on the join path runs inside asyncio.to_thread, so one hung socket pins a
    worker thread permanently; enough of them and the pool drains to zero with no
    error and no joins. curl_cffi honours `timeout` as a constructor argument (its
    get/post are partialmethods bound at class-definition time, so patching the
    instance's request() is never reached).
    """
    try:
        from config import load_config
        return float(load_config().get("request_timeout", 30))
    except Exception:
        return 30.0


# ! CONFIG READ-MODIFY-WRITE
_config_write_lock = threading.Lock()


def update_config_keys(updates, config_path="input/config.json"):
    """Merge `updates` into a JSON config file under a lock, atomically.

    Two places rewrote config.json with a read-modify-write: the Discord bot
    saving its stats channel and message ids, and the license gate saving the
    key. Each read, mutated and wrote independently, so running concurrently they
    silently dropped each other's keys.
    """
    with _config_write_lock:
        existing = {}
        if os.path.exists(config_path):
            with open(config_path, "r", encoding="utf-8") as f:
                # Deliberately not caught: replacing a config we cannot parse
                # would discard the license key and solver credentials in it.
                existing = json.load(f)
        if not isinstance(existing, dict):
            raise ValueError(f"{config_path} is not a JSON object")
        existing.update(updates)
        write_json_atomic(config_path, existing)
        return existing


# ! ATOMIC TEXT WRITE
def write_text_atomic(path, text):
    """Write text via a temp file in the same directory, then rename.

    input/tokens.txt and input/invites.txt are rewritten in full whenever an
    entry is removed. Path.write_text truncates the target first, so a crash or a
    full disk mid-write leaves the whole token or invite list destroyed -- and
    these are the operator's inputs, not regenerable state.
    """
    import tempfile
    path = str(path)
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=directory, prefix=".tmp-", suffix=".txt")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
''',
    'utils.dashboard': 'import http.server\nimport json\nimport threading\nimport time\nimport os\nimport base64\nimport hmac\nimport urllib.parse\nfrom colorama import Fore, Style\nfrom config import load_config\nfrom utils.core import STATS, START_TIME, get_cpm, setup_logger\n\nlog = setup_logger(__name__)\n\nCPM_MINUTE_HISTORY = []\n_cpm_history_lock = threading.Lock()\n_last_cpm_minute_recorded = 0\n\nTOKEN_CORE_STATE = {\n    "session_created": 0,\n    "captcha_fails": 0,\n    "invalid_tokens": 0,\n    "tokens_left": 0,\n    "total_tokens": 0,\n    "tokens_retired": 0,\n    "invites_left": 0,\n    "session_stopped": False,\n    "current_session": {\n        "user_id": 0,\n        "joins": 0,\n    },\n    "queue": [],\n    "workers": [],\n    "logs": [],\n}\n_token_core_lock = threading.Lock()\n\nimport re as _re\n\n# Anything the dashboard shows is visible to anyone who can reach the page, so\n# tokens and invite codes are masked before they leave the process. The first\n# chars of a Discord token are the base64 account id, so only a 4-char stub is\n# kept -- enough to tell two workers apart, not enough to identify or reuse the\n# account. Invite codes are hidden entirely; the operator does not need the code\n# to watch progress.\n_TOKEN_RE = _re.compile(r"\\b(?:[MNO][A-Za-z0-9_-]{23,26})\\.[A-Za-z0-9_-]{6}\\.[A-Za-z0-9_-]{27,}\\b")\n_INVITE_RE = _re.compile(r"((?:https?://)?(?:discord\\.gg|discord(?:app)?\\.com/invite|discord\\.com/invite)/)([A-Za-z0-9-]+)")\n_TOKEN_KV_RE = _re.compile(r"(token[=:\\s]+)([A-Za-z0-9_.-]{20,})", _re.IGNORECASE)\n# Bare invite codes: the engine logs "target=abc123", "invite=abc123",\n# "Invite abc123" and "(abc123)" without a discord.gg/ prefix, which the URL\n# pattern above does not catch -- and a bare code is just as joinable.\n_INVITE_KV_RE = _re.compile(r"((?:target|invite)[=:\\s]+)([A-Za-z0-9-]{2,})", _re.IGNORECASE)\n_INVITE_PAREN_RE = _re.compile(r"(\\((?:HTTP \\d+\\) \\()?)([A-Za-z0-9-]{6,})(\\))")\n\n\ndef mask_token_str(token: str) -> str:\n    if not token:\n        return "—"\n    clean = token.split(":")[-1].strip() if ":" in token else token.strip()\n    if len(clean) <= 4:\n        return clean\n    return clean[:4] + "…"\n\n\ndef mask_invite_str(invite: str) -> str:\n    if not invite:\n        return "—"\n    return "discord.gg/•••••"\n\n\ndef scrub_sensitive(text: str) -> str:\n    """Remove full tokens and invite codes from any free text (log lines, etc.).\n\n    Defence in depth for anything that reaches the dashboard as raw text rather\n    than through the per-field masks above: a leaked log line could otherwise\n    carry a full token or a joinable invite.\n    """\n    if not text:\n        return text\n    text = _TOKEN_RE.sub("•••token•••", text)\n    text = _INVITE_RE.sub(r"\\1•••••", text)\n    text = _TOKEN_KV_RE.sub(r"\\1•••", text)\n    text = _INVITE_KV_RE.sub(r"\\1•••••", text)\n    text = _INVITE_PAREN_RE.sub(r"\\1•••••\\3", text)\n    return text\n\ndef init_token_core_workers(num_workers: int = 10, limit: int = 33):\n    with _token_core_lock:\n        TOKEN_CORE_STATE["workers"] = [\n            {\n                "id": i + 1,\n                "token": "—",\n                "invite": "—",\n                "joins": 0,\n                "limit": limit,\n                "status": "Idle"\n            }\n            for i in range(num_workers)\n        ]\n\ndef set_worker_state(worker_id: int, token: str = None, invite: str = None, joins: int = None, limit: int = None, status: str = None):\n    with _token_core_lock:\n        workers = TOKEN_CORE_STATE.get("workers", [])\n        for w in workers:\n            if w.get("id") == worker_id:\n                if token is not None:\n                    w["token"] = mask_token_str(token)\n                if invite is not None:\n                    w["invite"] = mask_invite_str(invite)\n                if joins is not None:\n                    w["joins"] = joins\n                if limit is not None:\n                    w["limit"] = limit\n                if status is not None:\n                    w["status"] = status\n                break\n\ndef push_token_core_log(message: str, log_type: str = "info"):\n    # Callers pass full invite codes (e.g. "Joined discord.gg/abcd"); scrub before\n    # storing so the dashboard never holds an unmasked invite or token.\n    message = scrub_sensitive(message)\n    with _token_core_lock:\n        logs = TOKEN_CORE_STATE.setdefault("logs", [])\n        logs.append({\n            "message": message,\n            "type": log_type\n        })\n        if len(logs) > 100:\n            logs.pop(0)\n\ndef update_token_core_telemetry(session_created=None, captcha_fails=None, invalid_tokens=None, tokens_left=None, invites_left=None, session_stopped=None, user_id=None, total_tokens=None, tokens_retired=None):\n    with _token_core_lock:\n        if session_created is not None:\n            TOKEN_CORE_STATE["session_created"] = session_created\n            if "current_session" in TOKEN_CORE_STATE and TOKEN_CORE_STATE["current_session"]:\n                TOKEN_CORE_STATE["current_session"]["joins"] = session_created\n        if captcha_fails is not None:\n            TOKEN_CORE_STATE["captcha_fails"] = captcha_fails\n        if invalid_tokens is not None:\n            TOKEN_CORE_STATE["invalid_tokens"] = invalid_tokens\n        if tokens_left is not None:\n            TOKEN_CORE_STATE["tokens_left"] = tokens_left\n        if invites_left is not None:\n            TOKEN_CORE_STATE["invites_left"] = invites_left\n        if session_stopped is not None:\n            TOKEN_CORE_STATE["session_stopped"] = session_stopped\n        if total_tokens is not None:\n            TOKEN_CORE_STATE["total_tokens"] = total_tokens\n        if tokens_retired is not None:\n            TOKEN_CORE_STATE["tokens_retired"] = tokens_retired\n        if user_id is not None:\n            if "current_session" not in TOKEN_CORE_STATE or not TOKEN_CORE_STATE["current_session"]:\n                TOKEN_CORE_STATE["current_session"] = {"user_id": user_id, "joins": 0}\n            else:\n                TOKEN_CORE_STATE["current_session"]["user_id"] = user_id\n\ndef get_dashboard_html() -> bytes:\n    html_file = os.path.join(os.path.dirname(__file__), "dashboard.html")\n    if os.path.exists(html_file):\n        try:\n            with open(html_file, "rb") as f:\n                return f.read()\n        except Exception:\n            pass\n    return HTML_CONTENT.encode("utf-8")\n\n\ndef _record_cpm_tick():\n    global _last_cpm_minute_recorded\n    while True:\n        try:\n            now = time.time()\n            if now - _last_cpm_minute_recorded >= 60:\n                _last_cpm_minute_recorded = now\n                current_time_str = time.strftime("%H:%M")\n                cpm_val = get_cpm()\n                with _cpm_history_lock:\n                    CPM_MINUTE_HISTORY.append({\n                        "time": current_time_str,\n                        "cpm": cpm_val\n                    })\n                    if len(CPM_MINUTE_HISTORY) > 60:\n                        CPM_MINUTE_HISTORY.pop(0)\n        except Exception:\n            pass\n        time.sleep(1)\n\n\nclass DashboardHandler(http.server.BaseHTTPRequestHandler):\n    def log_message(self, format, *args):\n        # Suppress request logging in the main console to prevent spam\n        pass\n\n    def _check_auth(self):\n        """Return True if auth passes or no password is configured."""\n        cfg = load_config()\n        password = cfg.get("dashboard_password", "").strip()\n        if not password:\n            return True  # No password set — open access\n        auth_header = self.headers.get("Authorization", "")\n        if auth_header.startswith("Basic "):\n            try:\n                decoded = base64.b64decode(auth_header[6:]).decode("utf-8")\n                _, provided = decoded.split(":", 1)\n                if hmac.compare_digest(provided, password):\n                    return True\n            except Exception:\n                pass\n        # Send 401 with WWW-Authenticate to trigger browser login prompt\n        self.send_response(401)\n        self.send_header("WWW-Authenticate", \'Basic realm="Bit Filler Dashboard"\')\n        self.send_header("Content-Type", "text/plain")\n        self.end_headers()\n        self.wfile.write(b"Unauthorized")\n        return False\n\n    def do_GET(self):\n        if not self._check_auth():\n            return\n        parsed_url = urllib.parse.urlparse(self.path)\n\n        if parsed_url.path == "/api/stats":\n            self.send_response(200)\n            self.send_header("Content-Type", "application/json")\n            self.end_headers()\n\n            elapsed = time.time() - START_TIME\n            unlocked = STATS.get("unlocked", 0)\n            locked = STATS.get("locked", 0)\n            invalid = STATS.get("invalid", 0)\n            total = unlocked + locked + invalid\n            success_rate = (unlocked / total * 100) if total > 0 else 0\n\n            # Count remaining items from input files safely\n            token_count = 0\n            invite_count = 0\n            if os.path.exists("input/tokens.txt"):\n                try:\n                    with open("input/tokens.txt", "r", encoding="utf-8", errors="ignore") as f:\n                        token_count = sum(1 for line in f if line.strip())\n                except Exception:\n                    pass\n\n            if os.path.exists("input/invites.txt"):\n                try:\n                    with open("input/invites.txt", "r", encoding="utf-8", errors="ignore") as f:\n                        invite_count = sum(1 for line in f if line.strip())\n                except Exception:\n                    pass\n\n            cfg = load_config()\n            solver_cfg = cfg.get("solver", {})\n            solver_name = "Enabled" if solver_cfg.get("enabled", True) else "Disabled"\n\n            loaded_tokens = []\n            if os.path.exists("input/tokens.txt"):\n                try:\n                    with open("input/tokens.txt", "r", encoding="utf-8", errors="ignore") as f:\n                        loaded_tokens = [l.strip() for l in f if l.strip()]\n                except Exception:\n                    pass\n\n            guilds_db = {}\n            if os.path.exists("output/joined_guilds.json"):\n                try:\n                    with open("output/joined_guilds.json", "r", encoding="utf-8") as f:\n                        guilds_db = json.load(f)\n                except Exception:\n                    pass\n\n            if loaded_tokens:\n                total_loaded_joins = sum(len(guilds_db.get(tok, [])) for tok in loaded_tokens)\n                effective_tokens = len(loaded_tokens)\n                avg_joins_per_token = round(total_loaded_joins / effective_tokens, 1)\n            else:\n                effective_tokens = max(token_count, 1)\n                avg_joins_per_token = round(unlocked / effective_tokens, 1)\n\n            max_guild_limit = cfg.get("max_guild_limit", 80)\n            token_cap_pct = min(100.0, round((avg_joins_per_token / max_guild_limit) * 100, 1)) if max_guild_limit else 0.0\n\n            with _cpm_history_lock:\n                if not CPM_MINUTE_HISTORY:\n                    cpm_hist = [{"time": time.strftime("%H:%M"), "cpm": get_cpm()}]\n                else:\n                    cpm_hist = list(CPM_MINUTE_HISTORY)\n\n            data = {\n                "unlocked": unlocked,\n                "locked": locked,\n                "invalid": invalid,\n                "error": STATS.get("error", 0),\n                "rate_limit": STATS.get("rate", 0),\n                "captcha_solves": STATS.get("captcha_solves", 0),\n                "total_tokens": token_count,\n                "total_invites": invite_count,\n                "threads": cfg.get("threads", 1),\n                "solver": solver_name,\n                "cpm": get_cpm(),\n                "cpm_history": cpm_hist,\n                "token_cap_pct": token_cap_pct,\n                "avg_joins_per_token": avg_joins_per_token,\n                "max_guild_limit": max_guild_limit,\n                "success_rate": round(success_rate, 1),\n                "elapsed": round(elapsed, 0),\n            }\n            self.wfile.write(json.dumps(data).encode("utf-8"))\n\n        elif parsed_url.path == "/api/recent_joins":\n            self.send_response(200)\n            self.send_header("Content-Type", "application/json")\n            self.end_headers()\n\n            recent = []\n            if os.path.exists("output/joined.txt"):\n                try:\n                    with open("output/joined.txt", "r", encoding="utf-8", errors="ignore") as f:\n                        lines = [l.strip() for l in f if l.strip()]\n                        for line in lines[-20:]:\n                            parts = [p.strip() for p in line.split("|")]\n                            if len(parts) >= 3:\n                                raw_tok = parts[0]\n                                masked_tok = mask_token_str(raw_tok)\n                                recent.append({\n                                    "token": masked_tok,\n                                    "guild_id": parts[1],\n                                    "guild_name": parts[2],\n                                })\n                            elif len(parts) == 1:\n                                raw_tok = parts[0]\n                                masked_tok = mask_token_str(raw_tok)\n                                recent.append({\n                                    "token": masked_tok,\n                                    "guild_id": "—",\n                                    "guild_name": "Joined Server",\n                                })\n                except Exception:\n                    pass\n            self.wfile.write(json.dumps({"joins": list(reversed(recent))}).encode("utf-8"))\n\n        elif parsed_url.path == "/api/logs":\n            self.send_response(200)\n            self.send_header("Content-Type", "application/json")\n            self.end_headers()\n\n            logs = []\n            if os.path.exists("log/logs.txt"):\n                try:\n                    import re\n                    ansi_re = re.compile(r\'\\x1b\\[[0-9;]*[a-zA-Z]|\\b\\[[0-9;]+m\')\n                    with open("log/logs.txt", "r", encoding="utf-8", errors="ignore") as f:\n                        lines = f.readlines()\n                        for line in lines[-150:]:\n                            cleaned = ansi_re.sub(\'\', line).strip()\n                            if cleaned:\n                                # Raw log lines carry full invites and can carry\n                                # tokens; mask both before they reach the page.\n                                logs.append(scrub_sensitive(cleaned))\n                except Exception as e:\n                    logs = [f"Error reading logs: {e}"]\n            else:\n                logs = ["No engine logs recorded yet."]\n\n            self.wfile.write(json.dumps({"logs": logs}).encode("utf-8"))\n\n        elif parsed_url.path == "/api/data":\n            self.send_response(200)\n            self.send_header("Content-Type", "application/json")\n            self.end_headers()\n\n            with _token_core_lock:\n                data = dict(TOKEN_CORE_STATE)\n                data["session_created"] = STATS.get("unlocked", 0)\n                data["captcha_fails"] = STATS.get("captcha_fails", 0)\n                data["invalid_tokens"] = STATS.get("invalid", 0) + STATS.get("locked", 0)\n                if data.get("current_session"):\n                    data["current_session"]["joins"] = STATS.get("unlocked", 0)\n                data["workers"] = list(TOKEN_CORE_STATE.get("workers", []))\n                data["logs"] = [\n                    {"message": scrub_sensitive(l.get("message", "")), "type": l.get("type", "info")}\n                    if isinstance(l, dict) else scrub_sensitive(str(l))\n                    for l in TOKEN_CORE_STATE.get("logs", [])\n                ]\n\n            self.wfile.write(json.dumps(data).encode("utf-8"))\n\n        elif parsed_url.path == "/" or parsed_url.path == "/index.html":\n            self.send_response(200)\n            self.send_header("Content-Type", "text/html; charset=utf-8")\n            self.end_headers()\n            self.wfile.write(get_dashboard_html())\n        else:\n            self.send_response(404)\n            self.end_headers()\n\n\nHTML_CONTENT = r"""<!DOCTYPE html>\n<html lang="en">\n<head>\n    <meta charset="UTF-8">\n    <meta name="viewport" content="width=device-width, initial-scale=1.0">\n    <title>Bit Filler › Command Dashboard</title>\n    <link rel="preconnect" href="https://fonts.googleapis.com">\n    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n    <link href="https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@300;400;500;600;700;800&family=JetBrains+Mono:wght@400;500;600;700&display=swap" rel="stylesheet">\n    <script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.1/dist/chart.umd.min.js"></script>\n    <style>\n        :root {\n            --bg-base: #070913;\n            --bg-card: rgba(13, 18, 36, 0.65);\n            --bg-card-hover: rgba(18, 25, 51, 0.85);\n            --primary: #5865F2;\n            --primary-glow: rgba(88, 101, 242, 0.35);\n            --cyan: #00F2FE;\n            --cyan-glow: rgba(0, 242, 254, 0.3);\n            --success: #57F287;\n            --success-glow: rgba(87, 242, 135, 0.25);\n            --warning: #FEE75C;\n            --warning-glow: rgba(254, 231, 92, 0.25);\n            --danger: #ED4245;\n            --danger-glow: rgba(237, 66, 69, 0.25);\n            --magenta: #EB459E;\n            --text-main: #F2F3F5;\n            --text-muted: #80848E;\n            --border: rgba(255, 255, 255, 0.07);\n            --border-hover: rgba(0, 242, 254, 0.3);\n            --font-main: \'Plus Jakarta Sans\', -apple-system, BlinkMacSystemFont, sans-serif;\n            --font-mono: \'JetBrains Mono\', monospace;\n        }\n\n        * {\n            box-sizing: border-box;\n            margin: 0;\n            padding: 0;\n            scrollbar-width: thin;\n            scrollbar-color: rgba(255, 255, 255, 0.12) transparent;\n        }\n\n        *::-webkit-scrollbar {\n            width: 5px;\n            height: 5px;\n        }\n        *::-webkit-scrollbar-track { background: transparent; }\n        *::-webkit-scrollbar-thumb {\n            background: rgba(255, 255, 255, 0.12);\n            border-radius: 4px;\n        }\n        *::-webkit-scrollbar-thumb:hover {\n            background: rgba(255, 255, 255, 0.25);\n        }\n\n        body {\n            font-family: var(--font-main);\n            background-color: var(--bg-base);\n            color: var(--text-main);\n            min-height: 100vh;\n            overflow-x: hidden;\n            position: relative;\n            background-image: \n                radial-gradient(circle at 15% 10%, rgba(88, 101, 242, 0.12) 0%, transparent 45%),\n                radial-gradient(circle at 85% 90%, rgba(0, 242, 254, 0.08) 0%, transparent 50%),\n                radial-gradient(circle at 50% 50%, rgba(235, 69, 158, 0.04) 0%, transparent 60%);\n            background-attachment: fixed;\n        }\n\n        /* Top Navigation Header */\n        header {\n            display: flex;\n            justify-content: space-between;\n            align-items: center;\n            padding: 1.1rem 5%;\n            border-bottom: 1px solid var(--border);\n            background: rgba(7, 9, 19, 0.75);\n            backdrop-filter: blur(20px);\n            position: sticky;\n            top: 0;\n            z-index: 100;\n        }\n\n        .brand-container {\n            display: flex;\n            align-items: center;\n            gap: 14px;\n        }\n\n        .brand-logo {\n            width: 42px;\n            height: 42px;\n            background: linear-gradient(135deg, var(--primary), var(--cyan));\n            border-radius: 12px;\n            display: flex;\n            align-items: center;\n            justify-content: center;\n            box-shadow: 0 0 20px var(--primary-glow);\n            color: #fff;\n            font-weight: 800;\n            font-size: 1.2rem;\n            letter-spacing: -0.5px;\n        }\n\n        .brand-text h1 {\n            font-size: 1.35rem;\n            font-weight: 800;\n            letter-spacing: -0.3px;\n            background: linear-gradient(135deg, #fff 30%, var(--cyan) 100%);\n            -webkit-background-clip: text;\n            -webkit-text-fill-color: transparent;\n        }\n\n        .brand-text p {\n            font-size: 0.75rem;\n            color: var(--text-muted);\n            font-weight: 600;\n            text-transform: uppercase;\n            letter-spacing: 0.8px;\n        }\n\n        .header-status-pill {\n            display: flex;\n            align-items: center;\n            gap: 9px;\n            background: rgba(87, 242, 135, 0.08);\n            border: 1px solid rgba(87, 242, 135, 0.25);\n            color: var(--success);\n            padding: 7px 16px;\n            border-radius: 20px;\n            font-size: 0.8rem;\n            font-weight: 700;\n            letter-spacing: 0.5px;\n            box-shadow: 0 0 15px var(--success-glow);\n        }\n\n        .status-pulse {\n            width: 8px;\n            height: 8px;\n            background: var(--success);\n            border-radius: 50%;\n            animation: pulse-ring 2s infinite ease-in-out;\n        }\n\n        @keyframes pulse-ring {\n            0% { transform: scale(0.9); box-shadow: 0 0 0 0 rgba(87, 242, 135, 0.7); }\n            70% { transform: scale(1.1); box-shadow: 0 0 0 7px rgba(87, 242, 135, 0); }\n            100% { transform: scale(0.9); box-shadow: 0 0 0 0 rgba(87, 242, 135, 0); }\n        }\n\n        /* Main Container */\n        .container {\n            max-width: 1440px;\n            margin: 0 auto;\n            padding: 2rem 5%;\n        }\n\n        /* Top 5 Stat Metrics Cards */\n        .metrics-grid {\n            display: grid;\n            grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));\n            gap: 18px;\n            margin-bottom: 2rem;\n        }\n\n        .stat-card {\n            background: var(--bg-card);\n            border: 1px solid var(--border);\n            border-radius: 18px;\n            padding: 1.4rem 1.5rem;\n            backdrop-filter: blur(25px);\n            position: relative;\n            overflow: hidden;\n            transition: all 0.35s cubic-bezier(0.16, 1, 0.3, 1);\n            box-shadow: 0 6px 24px rgba(0, 0, 0, 0.3);\n        }\n\n        .stat-card:hover {\n            transform: translateY(-4px);\n            border-color: var(--border-hover);\n            background: var(--bg-card-hover);\n        }\n\n        .stat-card::before {\n            content: \'\';\n            position: absolute;\n            top: 0;\n            left: 0;\n            width: 4px;\n            height: 100%;\n            background: var(--primary);\n        }\n\n        .stat-card.joined::before { background: linear-gradient(180deg, var(--success), #00F2FE); }\n        .stat-card.locked::before { background: linear-gradient(180deg, var(--warning), #ff9800); }\n        .stat-card.invalid::before { background: linear-gradient(180deg, var(--danger), var(--magenta)); }\n        .stat-card.speed::before { background: linear-gradient(180deg, var(--cyan), var(--primary)); }\n        .stat-card.rate::before { background: linear-gradient(180deg, var(--magenta), #a855f7); }\n\n        .stat-top {\n            display: flex;\n            justify-content: space-between;\n            align-items: center;\n            margin-bottom: 0.9rem;\n        }\n\n        .stat-title {\n            font-size: 0.8rem;\n            color: var(--text-muted);\n            font-weight: 700;\n            text-transform: uppercase;\n            letter-spacing: 0.8px;\n        }\n\n        .stat-icon {\n            width: 32px;\n            height: 32px;\n            border-radius: 9px;\n            background: rgba(255, 255, 255, 0.04);\n            display: flex;\n            align-items: center;\n            justify-content: center;\n            font-size: 1rem;\n        }\n\n        .stat-val {\n            font-size: 2.3rem;\n            font-weight: 800;\n            letter-spacing: -1px;\n            line-height: 1.1;\n            margin-bottom: 0.3rem;\n        }\n\n        .stat-sub {\n            font-size: 0.75rem;\n            color: var(--text-muted);\n            font-weight: 500;\n        }\n\n        /* 2-Column Analytics & Dashboard Section */\n        .analytics-grid {\n            display: grid;\n            grid-template-columns: 360px 1fr;\n            gap: 20px;\n            margin-bottom: 2rem;\n        }\n\n        @media (max-width: 1024px) {\n            .analytics-grid { grid-template-columns: 1fr; }\n        }\n\n        .glass-panel {\n            background: var(--bg-card);\n            border: 1px solid var(--border);\n            border-radius: 20px;\n            padding: 1.6rem;\n            backdrop-filter: blur(25px);\n            display: flex;\n            flex-direction: column;\n            box-shadow: 0 8px 30px rgba(0, 0, 0, 0.25);\n        }\n\n        .panel-heading {\n            display: flex;\n            justify-content: space-between;\n            align-items: center;\n            font-size: 1.05rem;\n            font-weight: 700;\n            padding-bottom: 0.9rem;\n            margin-bottom: 1.2rem;\n            border-bottom: 1px solid var(--border);\n        }\n\n        .panel-heading span {\n            display: flex;\n            align-items: center;\n            gap: 8px;\n        }\n\n        /* Performance Matrix Rows */\n        .matrix-row {\n            display: flex;\n            justify-content: space-between;\n            align-items: center;\n            padding: 0.75rem 0;\n            border-bottom: 1px dashed rgba(255, 255, 255, 0.05);\n        }\n\n        .matrix-row:last-child { border-bottom: none; }\n        .matrix-label { font-size: 0.85rem; color: #cbd5e1; font-weight: 500; }\n        .matrix-value { font-family: var(--font-mono); font-weight: 700; font-size: 1rem; }\n\n        .cap-progress-track {\n            width: 100%;\n            height: 6px;\n            background: rgba(255, 255, 255, 0.06);\n            border-radius: 999px;\n            overflow: hidden;\n            border: 1px solid rgba(255, 255, 255, 0.08);\n            margin: 4px 0 2px 0;\n        }\n\n        .cap-progress-fill {\n            height: 100%;\n            background: linear-gradient(90deg, #00F2FE, #5865F2);\n            border-radius: 999px;\n            transition: width 0.4s ease;\n            box-shadow: 0 0 8px rgba(0, 242, 254, 0.4);\n        }\n\n        /* Chart Canvas Containers */\n        .chart-box {\n            width: 100%;\n            height: 190px;\n            margin-top: 1rem;\n            position: relative;\n        }\n\n        /* Right Panel: Join Feed & Terminal Stack */\n        .right-stack {\n            display: flex;\n            flex-direction: column;\n            gap: 20px;\n        }\n\n        /* Recent Joins Live Table */\n        .table-container {\n            max-height: 220px;\n            overflow-y: auto;\n            border-radius: 12px;\n            border: 1px solid rgba(255, 255, 255, 0.04);\n            background: rgba(4, 6, 14, 0.6);\n        }\n\n        table.joins-table {\n            width: 100%;\n            border-collapse: collapse;\n            font-size: 0.82rem;\n            text-align: left;\n        }\n\n        table.joins-table th {\n            background: rgba(255, 255, 255, 0.03);\n            color: var(--text-muted);\n            font-weight: 600;\n            text-transform: uppercase;\n            font-size: 0.7rem;\n            letter-spacing: 0.5px;\n            padding: 9px 14px;\n            position: sticky;\n            top: 0;\n            z-index: 2;\n        }\n\n        table.joins-table td {\n            padding: 9px 14px;\n            border-bottom: 1px solid rgba(255, 255, 255, 0.03);\n            color: #d1d5db;\n        }\n\n        table.joins-table tr:hover td {\n            background: rgba(255, 255, 255, 0.02);\n        }\n\n        .guild-badge {\n            display: inline-flex;\n            align-items: center;\n            gap: 6px;\n            font-weight: 600;\n            color: #fff;\n        }\n\n        .token-mono {\n            font-family: var(--font-mono);\n            color: var(--cyan);\n            font-size: 0.78rem;\n        }\n\n        .tag-joined {\n            display: inline-block;\n            background: rgba(87, 242, 135, 0.15);\n            color: var(--success);\n            font-weight: 700;\n            font-size: 0.7rem;\n            padding: 3px 8px;\n            border-radius: 6px;\n            letter-spacing: 0.5px;\n        }\n\n        /* Terminal Window */\n        .terminal-box {\n            display: flex;\n            flex-direction: column;\n            min-height: 420px;\n        }\n\n        .terminal-toolbar {\n            display: flex;\n            justify-content: space-between;\n            align-items: center;\n            padding: 10px 14px;\n            background: rgba(5, 7, 16, 0.8);\n            border-radius: 12px 12px 0 0;\n            border: 1px solid var(--border);\n            border-bottom: none;\n            gap: 12px;\n            flex-wrap: wrap;\n        }\n\n        .mac-dots {\n            display: flex;\n            gap: 6px;\n        }\n\n        .mac-dot {\n            width: 10px;\n            height: 10px;\n            border-radius: 50%;\n        }\n        .dot-red { background-color: #ff5f56; }\n        .dot-yellow { background-color: #ffbd2e; }\n        .dot-green { background-color: #27c93f; }\n\n        .terminal-actions {\n            display: flex;\n            align-items: center;\n            gap: 8px;\n        }\n\n        .search-input {\n            background: rgba(255, 255, 255, 0.04);\n            border: 1px solid var(--border);\n            color: #fff;\n            padding: 4px 10px;\n            border-radius: 6px;\n            font-size: 0.75rem;\n            outline: none;\n            font-family: var(--font-mono);\n            width: 150px;\n            transition: all 0.2s;\n        }\n\n        .search-input:focus {\n            border-color: var(--cyan);\n            background: rgba(255, 255, 255, 0.07);\n            width: 200px;\n        }\n\n        .filter-chip {\n            background: rgba(255, 255, 255, 0.03);\n            border: 1px solid var(--border);\n            color: var(--text-muted);\n            padding: 4px 10px;\n            border-radius: 6px;\n            font-size: 0.72rem;\n            font-weight: 700;\n            cursor: pointer;\n            transition: all 0.2s;\n        }\n\n        .filter-chip:hover, .filter-chip.active {\n            background: var(--primary-glow);\n            color: #fff;\n            border-color: var(--primary);\n        }\n\n        .tool-btn {\n            background: rgba(255, 255, 255, 0.04);\n            border: 1px solid var(--border);\n            color: var(--text-muted);\n            padding: 4px 9px;\n            border-radius: 6px;\n            font-size: 0.72rem;\n            cursor: pointer;\n            transition: all 0.2s;\n        }\n\n        .tool-btn:hover {\n            background: rgba(255, 255, 255, 0.1);\n            color: #fff;\n        }\n\n        .terminal-screen {\n            background: #02040a;\n            border: 1px solid var(--border);\n            border-radius: 0 0 14px 14px;\n            flex-grow: 1;\n            padding: 1rem 1.2rem;\n            overflow-y: auto;\n            font-family: var(--font-mono);\n            font-size: 0.82rem;\n            line-height: 1.65;\n            box-shadow: inset 0 2px 20px rgba(0, 0, 0, 0.9);\n            max-height: 380px;\n        }\n\n        .log-row {\n            display: flex;\n            align-items: flex-start;\n            gap: 10px;\n            padding: 2px 4px;\n            border-radius: 4px;\n            transition: background 0.15s;\n        }\n\n        .log-row:hover {\n            background: rgba(255, 255, 255, 0.03);\n        }\n\n        .log-time {\n            color: var(--text-muted);\n            user-select: none;\n            font-size: 0.75rem;\n            flex-shrink: 0;\n            padding-top: 1px;\n        }\n\n        .log-badge {\n            font-weight: 700;\n            padding: 0 6px;\n            border-radius: 4px;\n            font-size: 0.68rem;\n            letter-spacing: 0.5px;\n            flex-shrink: 0;\n            text-transform: uppercase;\n        }\n\n        .badge-info { background: rgba(88, 101, 242, 0.2); color: #8ea1ff; border: 1px solid rgba(88, 101, 242, 0.4); }\n        .badge-dbg { background: rgba(0, 242, 254, 0.12); color: var(--cyan); border: 1px solid rgba(0, 242, 254, 0.3); }\n        .badge-warn { background: rgba(254, 231, 92, 0.15); color: var(--warning); border: 1px solid rgba(254, 231, 92, 0.3); }\n        .badge-err { background: rgba(237, 66, 69, 0.2); color: var(--danger); border: 1px solid rgba(237, 66, 69, 0.4); }\n        .badge-sys { background: rgba(255, 255, 255, 0.08); color: var(--text-muted); }\n\n        /* High-Definition Log Color Classes */\n        .log-tag-thread {\n            background: rgba(168, 85, 247, 0.15);\n            color: #c084fc;\n            border: 1px solid rgba(168, 85, 247, 0.35);\n            padding: 1px 7px;\n            border-radius: 5px;\n            font-weight: 600;\n            font-size: 0.76rem;\n            display: inline-block;\n        }\n\n        .log-tag-joined {\n            background: rgba(87, 242, 135, 0.18);\n            color: #4ade80;\n            border: 1px solid rgba(87, 242, 135, 0.45);\n            padding: 1px 8px;\n            border-radius: 5px;\n            font-weight: 800;\n            font-size: 0.76rem;\n            letter-spacing: 0.5px;\n            display: inline-block;\n            box-shadow: 0 0 10px rgba(87, 242, 135, 0.2);\n        }\n\n        .log-tag-locked {\n            background: rgba(245, 158, 11, 0.18);\n            color: #fbbf24;\n            border: 1px solid rgba(245, 158, 11, 0.45);\n            padding: 1px 8px;\n            border-radius: 5px;\n            font-weight: 800;\n            font-size: 0.76rem;\n            display: inline-block;\n        }\n\n        .log-tag-invalid {\n            background: rgba(239, 68, 68, 0.18);\n            color: #f87171;\n            border: 1px solid rgba(239, 68, 68, 0.45);\n            padding: 1px 8px;\n            border-radius: 5px;\n            font-weight: 800;\n            font-size: 0.76rem;\n            display: inline-block;\n        }\n\n        .log-tag-skipped {\n            background: rgba(148, 163, 184, 0.12);\n            color: #94a3b8;\n            border: 1px solid rgba(148, 163, 184, 0.25);\n            padding: 1px 7px;\n            border-radius: 5px;\n            font-weight: 600;\n            font-size: 0.74rem;\n            display: inline-block;\n        }\n\n        .log-tag-already {\n            background: rgba(0, 242, 254, 0.12);\n            color: #38bdf8;\n            border: 1px solid rgba(0, 242, 254, 0.3);\n            padding: 1px 7px;\n            border-radius: 5px;\n            font-weight: 600;\n            font-size: 0.74rem;\n            display: inline-block;\n        }\n\n        .log-tag-captcha {\n            background: rgba(254, 231, 92, 0.15);\n            color: #fde047;\n            border: 1px solid rgba(254, 231, 92, 0.35);\n            padding: 1px 7px;\n            border-radius: 5px;\n            font-weight: 700;\n            font-size: 0.76rem;\n            display: inline-block;\n        }\n\n        .log-tag-solver {\n            background: rgba(52, 211, 153, 0.15);\n            color: #34d399;\n            border: 1px solid rgba(52, 211, 153, 0.35);\n            padding: 1px 7px;\n            border-radius: 5px;\n            font-weight: 700;\n            font-size: 0.76rem;\n            display: inline-block;\n        }\n\n        .log-param-key { color: #64748b; font-weight: 500; }\n        .log-param-val { color: #38bdf8; font-weight: 600; }\n        .log-invite-val { color: #fbbf24; font-weight: 600; }\n        .log-token-val { color: #00F2FE; font-weight: 600; }\n        .log-symbol { color: #475569; }\n        .log-timer-val { color: #f472b6; font-weight: 700; }\n        .log-telemetry { color: #818cf8; }\n        .log-http-code { font-weight: 700; padding: 0 4px; border-radius: 3px; }\n        .http-200 { color: #4ade80; background: rgba(74, 222, 128, 0.1); }\n        .http-204 { color: #818cf8; background: rgba(129, 140, 248, 0.1); }\n        .http-401 { color: #f87171; background: rgba(248, 113, 113, 0.1); }\n        .http-403 { color: #fbbf24; background: rgba(251, 191, 36, 0.1); }\n        .http-429 { color: #f59e0b; background: rgba(245, 158, 11, 0.1); }\n\n        .log-text {\n            color: #e2e8f0;\n            word-break: normal;\n            overflow-wrap: break-word;\n            flex-grow: 1;\n            line-height: 1.5;\n        }\n\n        .empty-state {\n            color: var(--text-muted);\n            text-align: center;\n            padding: 2rem;\n            font-size: 0.85rem;\n        }\n\n        /* ── Comprehensive Mobile & Responsive Media Queries ── */\n        @media (max-width: 1024px) {\n            .container {\n                padding: 1.5rem 4%;\n            }\n            .analytics-grid {\n                grid-template-columns: 1fr;\n                gap: 16px;\n            }\n        }\n\n        @media (max-width: 768px) {\n            header {\n                padding: 1rem 1.2rem;\n                flex-direction: column;\n                align-items: flex-start;\n                gap: 12px;\n            }\n\n            .header-status-pill {\n                align-self: flex-start;\n                padding: 5px 12px;\n                font-size: 0.72rem;\n            }\n\n            .brand-logo {\n                width: 38px;\n                height: 38px;\n                font-size: 1.2rem;\n            }\n\n            .brand-text h1 {\n                font-size: 1.25rem;\n            }\n\n            .brand-text p {\n                font-size: 0.72rem;\n            }\n\n            .container {\n                padding: 1rem 12px;\n            }\n\n            .metrics-grid {\n                grid-template-columns: repeat(2, 1fr);\n                gap: 10px;\n                margin-bottom: 1.2rem;\n            }\n\n            .stat-card {\n                padding: 1rem 1.1rem;\n                border-radius: 14px;\n            }\n\n            .stat-val {\n                font-size: 1.7rem;\n            }\n\n            .stat-title {\n                font-size: 0.7rem;\n            }\n\n            .stat-icon {\n                width: 28px;\n                height: 28px;\n                font-size: 0.85rem;\n            }\n\n            .glass-panel {\n                padding: 1.2rem;\n                border-radius: 16px;\n            }\n\n            .chart-box {\n                height: 160px;\n            }\n\n            .terminal-toolbar {\n                padding: 8px 10px;\n                flex-direction: column;\n                align-items: stretch;\n                gap: 8px;\n            }\n\n            .mac-dots {\n                display: none;\n            }\n\n            .terminal-actions {\n                width: 100%;\n                justify-content: space-between;\n                flex-wrap: wrap;\n                gap: 6px;\n            }\n\n            .search-input {\n                width: 100%;\n            }\n\n            .search-input:focus {\n                width: 100%;\n            }\n\n            .filter-chips {\n                display: flex;\n                gap: 4px;\n                width: 100%;\n                overflow-x: auto;\n                padding-bottom: 2px;\n            }\n\n            .terminal-screen {\n                padding: 0.8rem 0.9rem;\n                font-size: 0.75rem;\n                max-height: 320px;\n            }\n\n            .log-row {\n                gap: 6px;\n                flex-wrap: wrap;\n                margin-bottom: 3px;\n            }\n\n            .log-time {\n                font-size: 0.68rem;\n            }\n\n            .log-badge {\n                font-size: 0.62rem;\n                padding: 0 4px;\n            }\n\n            .log-text {\n                width: 100%;\n                font-size: 0.76rem;\n                overflow-wrap: break-word;\n            }\n\n            .table-container {\n                max-height: 200px;\n                overflow-x: auto;\n                -webkit-overflow-scrolling: touch;\n            }\n\n            table.joins-table th, table.joins-table td {\n                padding: 7px 10px;\n                font-size: 0.75rem;\n                white-space: nowrap;\n            }\n        }\n\n        @media (max-width: 480px) {\n            .metrics-grid {\n                grid-template-columns: 1fr;\n            }\n            .matrix-label {\n                font-size: 0.78rem;\n            }\n            .matrix-value {\n                font-size: 0.9rem;\n            }\n        }\n    </style>\n</head>\n<body>\n    <header>\n        <div class="brand-container">\n            <div class="brand-logo">⚡</div>\n            <div class="brand-text">\n                <h1>BIT FILLER</h1>\n                <p>High-Throughput Discord Automation Engine</p>\n            </div>\n        </div>\n        <div class="header-status-pill">\n            <div class="status-pulse"></div>\n            <span>LIVE ENGINE ACTIVE</span>\n        </div>\n    </header>\n\n    <main class="container">\n        <!-- Top 5 Primary Metric Cards -->\n        <div class="metrics-grid">\n            <div class="stat-card joined">\n                <div class="stat-top">\n                    <span class="stat-title">Joined Servers</span>\n                    <div class="stat-icon" style="color: var(--success);">✔</div>\n                </div>\n                <div class="stat-val" id="val-unlocked" style="color: var(--success);">0</div>\n                <div class="stat-sub">Successfully entered guilds</div>\n            </div>\n\n            <div class="stat-card locked">\n                <div class="stat-top">\n                    <span class="stat-title">Locked Tokens</span>\n                    <div class="stat-icon" style="color: var(--warning);">🔒</div>\n                </div>\n                <div class="stat-val" id="val-locked" style="color: var(--warning);">0</div>\n                <div class="stat-sub">HTTP 403 phone/email verification</div>\n            </div>\n\n            <div class="stat-card invalid">\n                <div class="stat-top">\n                    <span class="stat-title">Invalid Tokens</span>\n                    <div class="stat-icon" style="color: var(--danger);">✖</div>\n                </div>\n                <div class="stat-val" id="val-invalid" style="color: var(--danger);">0</div>\n                <div class="stat-sub">HTTP 401 revoked / dead tokens</div>\n            </div>\n\n            <div class="stat-card speed">\n                <div class="stat-top">\n                    <span class="stat-title">Join Velocity</span>\n                    <div class="stat-icon" style="color: var(--cyan);">⚡</div>\n                </div>\n                <div class="stat-val" id="val-cpm" style="color: var(--cyan);">0</div>\n                <div class="stat-sub">Joins Per Minute (CPM)</div>\n            </div>\n\n            <div class="stat-card rate">\n                <div class="stat-top">\n                    <span class="stat-title">Success Rate</span>\n                    <div class="stat-icon" style="color: var(--magenta);">📈</div>\n                </div>\n                <div class="stat-val" id="val-rate" style="color: var(--magenta);">0%</div>\n                <div class="stat-sub">Overall join conversion ratio</div>\n            </div>\n        </div>\n\n        <!-- 2-Column Analytics Layout -->\n        <div class="analytics-grid">\n            <!-- Left Side: Performance Matrix & Velocity Graph -->\n            <div class="glass-panel">\n                <div class="panel-heading">\n                    <span>⚙️ Engine Matrix</span>\n                </div>\n                <div class="matrix-row">\n                    <span class="matrix-label">Active Worker Threads</span>\n                    <span class="matrix-value" id="val-threads" style="color: var(--cyan);">1</span>\n                </div>\n                <div class="matrix-row">\n                    <span class="matrix-label">Tokens Loaded</span>\n                    <span class="matrix-value" id="tok-total" style="color: #fff;">0</span>\n                </div>\n                <div class="matrix-row">\n                    <span class="matrix-label">Invites in Queue</span>\n                    <span class="matrix-value" id="inv-total" style="color: var(--warning);">0</span>\n                </div>\n                <div class="matrix-row">\n                    <span class="matrix-label">Captcha Solver</span>\n                    <span class="matrix-value" id="val-solver" style="color: var(--success);">Bit Solver</span>\n                </div>\n                <div class="matrix-row">\n                    <span class="matrix-label">Elapsed Session Time</span>\n                    <span class="matrix-value" id="run-elapsed" style="color: var(--magenta);">0s</span>\n                </div>\n                <div class="matrix-row" style="flex-direction: column; align-items: flex-start; gap: 4px;">\n                    <div style="display: flex; justify-content: space-between; width: 100%;">\n                        <span class="matrix-label">Token Capacity Usage</span>\n                        <span class="matrix-value" id="val-cap-pct" style="color: var(--cyan);">0%</span>\n                    </div>\n                    <div class="cap-progress-track">\n                        <div class="cap-progress-fill" id="cap-progress-bar" style="width: 0%;"></div>\n                    </div>\n                    <div style="display: flex; justify-content: space-between; width: 100%; font-size: 0.72rem; color: var(--text-muted);">\n                        <span id="val-cap-sub">0 / 80 avg guilds/token</span>\n                        <span id="val-cap-total">0 slots filled</span>\n                    </div>\n                </div>\n\n                <div class="panel-heading" style="margin-top: 1.6rem;">\n                    <span>📊 Velocity Curve (CPM)</span>\n                </div>\n                <div class="chart-box">\n                    <canvas id="cpmChart"></canvas>\n                </div>\n            </div>\n\n            <!-- Right Side: Recent Joins Live Table + Live Terminal -->\n            <div class="right-stack">\n                <!-- Recent Server Joins Feed -->\n                <div class="glass-panel">\n                    <div class="panel-heading">\n                        <span>🎯 Real-Time Server Joins</span>\n                        <span id="joins-count-badge" style="font-size: 0.75rem; color: var(--success); font-weight: 700;">Live Feed</span>\n                    </div>\n                    <div class="table-container">\n                        <table class="joins-table">\n                            <thead>\n                                <tr>\n                                    <th>Token</th>\n                                    <th>Server ID</th>\n                                    <th>Server Name</th>\n                                    <th>Status</th>\n                                </tr>\n                            </thead>\n                            <tbody id="joins-tbody">\n                                <tr>\n                                    <td colspan="4" class="empty-state">No server joins recorded yet.</td>\n                                </tr>\n                            </tbody>\n                        </table>\n                    </div>\n                </div>\n\n                <!-- Terminal Output Panel -->\n                <div class="glass-panel terminal-box">\n                    <div class="terminal-toolbar">\n                        <div class="mac-dots">\n                            <div class="mac-dot dot-red"></div>\n                            <div class="mac-dot dot-yellow"></div>\n                            <div class="mac-dot dot-green"></div>\n                        </div>\n                        <div class="terminal-actions">\n                            <input type="text" id="log-search" class="search-input" placeholder="Search logs..." oninput="renderLogs()">\n                            <button class="filter-chip active" onclick="setLogFilter(\'ALL\', this)">ALL</button>\n                            <button class="filter-chip" onclick="setLogFilter(\'INF\', this)">INFO</button>\n                            <button class="filter-chip" onclick="setLogFilter(\'WRN\', this)">WARNS</button>\n                            <button class="filter-chip" onclick="setLogFilter(\'ERR\', this)">ERRORS</button>\n                            <button class="tool-btn" id="autoscroll-toggle" onclick="toggleAutoScroll()">Scroll: ON</button>\n                            <button class="tool-btn" onclick="copyTerminalLogs()">Copy</button>\n                        </div>\n                    </div>\n                    <div class="terminal-screen" id="terminal-output">\n                        <div class="log-row">\n                            <span class="log-time">[00:00:00]</span>\n                            <span class="log-badge badge-sys">SYS</span>\n                            <span class="log-text">Connecting to Bit Filler engine streaming logs...</span>\n                        </div>\n                    </div>\n                </div>\n            </div>\n        </div>\n    </main>\n\n    <script>\n        let currentFilter = \'ALL\';\n        let rawLogs = [];\n        let autoScrollEnabled = true;\n        let cpmHistory = [];\n        let timeLabels = [];\n        let cpmChart;\n\n        // Initialize Sleek Modern Velocity Curve Chart\n        const ctx = document.getElementById(\'cpmChart\').getContext(\'2d\');\n        const cpmGradient = ctx.createLinearGradient(0, 0, 0, 200);\n        cpmGradient.addColorStop(0, \'rgba(0, 242, 254, 0.28)\');\n        cpmGradient.addColorStop(0.65, \'rgba(0, 242, 254, 0.05)\');\n        cpmGradient.addColorStop(1, \'rgba(0, 242, 254, 0.0)\');\n\n        cpmChart = new Chart(ctx, {\n            type: \'line\',\n            data: {\n                labels: timeLabels,\n                datasets: [{\n                    label: \'Joins/Min (CPM)\',\n                    data: cpmHistory,\n                    borderColor: \'#00F2FE\',\n                    backgroundColor: cpmGradient,\n                    borderWidth: 2.5,\n                    tension: 0.42,\n                    fill: true,\n                    pointRadius: 0,\n                    pointHoverRadius: 6,\n                    pointHitRadius: 16,\n                    pointHoverBackgroundColor: \'#00F2FE\',\n                    pointHoverBorderColor: \'#ffffff\',\n                    pointHoverBorderWidth: 2\n                }]\n            },\n            options: {\n                responsive: true,\n                maintainAspectRatio: false,\n                interaction: {\n                    mode: \'index\',\n                    intersect: false\n                },\n                plugins: {\n                    legend: { display: false },\n                    tooltip: {\n                        backgroundColor: \'rgba(7, 9, 19, 0.94)\',\n                        titleColor: \'#00F2FE\',\n                        titleFont: { size: 12, weight: \'700\' },\n                        bodyColor: \'#ffffff\',\n                        bodyFont: { size: 12 },\n                        borderColor: \'rgba(0, 242, 254, 0.35)\',\n                        borderWidth: 1,\n                        padding: 10,\n                        cornerRadius: 8,\n                        displayColors: false,\n                        callbacks: {\n                            label: function(context) {\n                                return `Speed: ${context.parsed.y} CPM (joins/min)`;\n                            }\n                        }\n                    }\n                },\n                scales: {\n                    x: {\n                        display: true,\n                        grid: { display: false },\n                        ticks: {\n                            color: \'#80848E\',\n                            font: { size: 10 },\n                            maxTicksLimit: 6,\n                            maxRotation: 0\n                        }\n                    },\n                    y: {\n                        beginAtZero: true,\n                        grid: { \n                            color: \'rgba(255, 255, 255, 0.04)\',\n                            drawBorder: false\n                        },\n                        ticks: { \n                            color: \'#80848E\', \n                            font: { size: 10 },\n                            maxTicksLimit: 5\n                        }\n                    }\n                }\n            }\n        });\n\n        function formatTime(seconds) {\n            const h = Math.floor(seconds / 3600);\n            const m = Math.floor((seconds % 3600) / 60);\n            const s = Math.floor(seconds % 60);\n            return `${h > 0 ? h + \'h \' : \'\'}${m > 0 ? m + \'m \' : \'\'}${s}s`;\n        }\n\n        async function fetchStats() {\n            try {\n                const res = await fetch(\'/api/stats\');\n                if (!res.ok) return;\n                const data = await res.json();\n\n                document.getElementById(\'val-unlocked\').textContent = data.unlocked;\n                document.getElementById(\'val-locked\').textContent = data.locked;\n                document.getElementById(\'val-invalid\').textContent = data.invalid;\n                document.getElementById(\'val-cpm\').textContent = data.cpm;\n                document.getElementById(\'val-rate\').textContent = data.success_rate + \'%\';\n\n                document.getElementById(\'val-threads\').textContent = data.threads;\n                document.getElementById(\'tok-total\').textContent = data.total_tokens;\n                document.getElementById(\'inv-total\').textContent = data.total_invites;\n                document.getElementById(\'val-solver\').textContent = data.solver;\n                document.getElementById(\'run-elapsed\').textContent = formatTime(data.elapsed);\n\n                // Update Token Capacity Progress\n                if (data.token_cap_pct !== undefined) {\n                    document.getElementById(\'val-cap-pct\').textContent = data.token_cap_pct + \'%\';\n                    document.getElementById(\'cap-progress-bar\').style.width = data.token_cap_pct + \'%\';\n                    document.getElementById(\'val-cap-sub\').textContent = `${data.avg_joins_per_token || 0} / ${data.max_guild_limit || 80} avg guilds/token`;\n                    const totalSlots = (data.total_tokens || 0) * (data.max_guild_limit || 80);\n                    document.getElementById(\'val-cap-total\').textContent = `${data.unlocked || 0} / ${totalSlots} pool slots`;\n                }\n\n                // Update Minute-by-Minute CPM Chart\n                if (data.cpm_history && Array.isArray(data.cpm_history) && data.cpm_history.length > 0) {\n                    cpmChart.data.labels = data.cpm_history.map(item => item.time);\n                    cpmChart.data.datasets[0].data = data.cpm_history.map(item => item.cpm);\n                    cpmChart.update();\n                }\n            } catch (err) {\n                console.error("Error fetching stats:", err);\n            }\n        }\n\n        async function fetchRecentJoins() {\n            try {\n                const res = await fetch(\'/api/recent_joins\');\n                if (!res.ok) return;\n                const data = await res.json();\n                const tbody = document.getElementById(\'joins-tbody\');\n\n                if (!data.joins || data.joins.length === 0) {\n                    tbody.innerHTML = \'<tr><td colspan="4" class="empty-state">No server joins recorded yet.</td></tr>\';\n                    return;\n                }\n\n                tbody.innerHTML = \'\';\n                data.joins.forEach(j => {\n                    const tr = document.createElement(\'tr\');\n                    tr.innerHTML = `\n                        <td><span class="token-mono">${escapeHtml(j.token)}</span></td>\n                        <td><span style="font-family: var(--font-mono); color: #80848E;">${escapeHtml(j.guild_id)}</span></td>\n                        <td><div class="guild-badge"><span>🌐</span><span>${escapeHtml(j.guild_name)}</span></div></td>\n                        <td><span class="tag-joined">✔ JOINED</span></td>\n                    `;\n                    tbody.appendChild(tr);\n                });\n            } catch (err) {\n                console.error("Error fetching recent joins:", err);\n            }\n        }\n\n        function setLogFilter(filter, el) {\n            currentFilter = filter;\n            document.querySelectorAll(\'.filter-chip\').forEach(c => c.classList.remove(\'active\'));\n            if (el) el.classList.add(\'active\');\n            renderLogs();\n        }\n\n        function toggleAutoScroll() {\n            autoScrollEnabled = !autoScrollEnabled;\n            const btn = document.getElementById(\'autoscroll-toggle\');\n            btn.textContent = `Scroll: ${autoScrollEnabled ? \'ON\' : \'OFF\'}`;\n            btn.style.color = autoScrollEnabled ? \'var(--cyan)\' : \'var(--text-muted)\';\n        }\n\n        function copyTerminalLogs() {\n            const screen = document.getElementById(\'terminal-output\');\n            navigator.clipboard.writeText(screen.innerText).then(() => {\n                const btn = event.target;\n                const orig = btn.textContent;\n                btn.textContent = \'Copied!\';\n                setTimeout(() => { btn.textContent = orig; }, 1500);\n            });\n        }\n\n        function escapeHtml(str) {\n            return String(str).replace(/&/g, \'&amp;\').replace(/</g, \'&lt;\').replace(/>/g, \'&gt;\').replace(/"/g, \'&quot;\');\n        }\n\n        function cleanAnsi(str) {\n            return String(str)\n                .replace(/\\u001b\\[[0-9;]*[a-zA-Z]/g, \'\')\n                .replace(/\\[\\d+m/g, \'\')\n                .replace(/\\[0m/g, \'\')\n                .trim();\n        }\n\n        function formatLogMessage(text) {\n            let escaped = escapeHtml(text);\n\n            // Highlight [Thread X] or [Worker X]\n            escaped = escaped.replace(/(\\[(?:Thread|Worker)\\s+\\d+\\])/g, \'<span class="log-tag-thread">$1</span>\');\n\n            // Highlight joined/unlocked\n            escaped = escaped.replace(/(→\\s*Joined|→\\s*UNLOCKED|\\bJoined\\b(?=\\s*\\())/g, \'<span class="log-tag-joined">✔ Joined</span>\');\n\n            // Highlight locked\n            escaped = escaped.replace(/(→\\s*Account Locked|\\bAccount Locked\\b|\\bLOCKED\\b)/g, \'<span class="log-tag-locked">🔒 Locked</span>\');\n\n            // Highlight invalid\n            escaped = escaped.replace(/(→\\s*Invalid Token|\\bInvalid Token\\b|\\bINVALID\\b)/g, \'<span class="log-tag-invalid">✖ Invalid</span>\');\n\n            // Highlight skipped\n            escaped = escaped.replace(/(→\\s*Skipped[^\\(]*\\([^\\)]*\\)|\\bSkipped\\s*\\([^\\)]*\\))/g, \'<span class="log-tag-skipped">↷ $1</span>\');\n\n            // Highlight already member / in server\n            escaped = escaped.replace(/(→\\s*Already in Server|\\bAlready in Server\\b|\\bAlready Member\\b)/g, \'<span class="log-tag-already">ℹ Already in Server</span>\');\n\n            // Highlight challenge retry / backoff\n            escaped = escaped.replace(/(→\\s*Challenge Expired[^\\(]*\\([^\\)]*\\)|\\bChallenge Expired › Scheduled for retry\\b)/g, \'<span class="log-tag-skipped">↻ $1</span>\');\n\n            // Highlight captcha challenges\n            escaped = escaped.replace(/(\\bCaptcha challenge detected\\b)/g, \'<span class="log-tag-captcha">⚡ $1</span>\');\n            escaped = escaped.replace(/(\\b(?:Bit|Custom|Any)?\\s*Solver solved\\b|\\bCaptcha solved successfully(?:\\s+in\\s+[\\d\\.]+s)?\\b)/g, \'<span class="log-tag-solver">✔ $1</span>\');\n\n            // Highlight HTTP status codes e.g. (HTTP 204), (HTTP 200), (HTTP 403), [200]\n            escaped = escaped.replace(/\\((HTTP\\s+204)\\)/g, \'(<span class="log-http-code http-204">$1</span>)\');\n            escaped = escaped.replace(/\\((HTTP\\s+200)\\)/g, \'(<span class="log-http-code http-200">$1</span>)\');\n            escaped = escaped.replace(/\\((HTTP\\s+401)\\)/g, \'(<span class="log-http-code http-401">$1</span>)\');\n            escaped = escaped.replace(/\\((HTTP\\s+403)\\)/g, \'(<span class="log-http-code http-403">$1</span>)\');\n            escaped = escaped.replace(/\\((HTTP\\s+429)\\)/g, \'(<span class="log-http-code http-429">$1</span>)\');\n\n            // Highlight specific known parameters (token=..., target=..., proxy=..., sitekey=..., task=..., solve=..., status=...)\n            escaped = escaped.replace(/(\\btoken=)([a-zA-Z0-9_\\-\\.\\*]+)/g, \'<span class="log-param-key">$1</span><span class="log-token-val">$2</span>\');\n            escaped = escaped.replace(/(\\b(?:target|invite)=)([a-zA-Z0-9_\\-\\.]+)/g, \'<span class="log-param-key">$1</span><span class="log-invite-val">$2</span>\');\n            escaped = escaped.replace(/(\\b(?:proxy|sitekey|task|solve|status|round|reason|service)=)([^\\s\\(\\)<>]+)/g, \'<span class="log-param-key">$1</span><span class="log-param-val">$2</span>\');\n\n            // Highlight invite in parentheses e.g. (2E9GsVMuSG) or (f8BjDNv3uM)\n            escaped = escaped.replace(/\\(([a-zA-Z0-9]{5,16})\\)/g, \'(<span class="log-invite-val">$1</span>)\');\n\n            // Highlight timers e.g. "sleeping 215.6s", "warming presence for 83.5s", "Pausing 9.5s", "for 5.6m", "in 14.8s"\n            escaped = escaped.replace(/(\\b(?:sleeping|for|Pausing|warming presence for|in)\\s+)(\\d+(?:\\.\\d+)?[smh])/gi, \'$1<span class="log-timer-val">$2</span>\');\n\n            // Highlight symbols\n            escaped = escaped.replace(/(→|›|│)/g, \'<span class="log-symbol">$1</span>\');\n\n            return escaped;\n        }\n\n        function renderLogs() {\n            const screen = document.getElementById(\'terminal-output\');\n            const searchKeyword = document.getElementById(\'log-search\').value.toLowerCase();\n            const wasAtBottom = screen.scrollHeight - screen.clientHeight <= screen.scrollTop + 40;\n\n            screen.innerHTML = \'\';\n\n            rawLogs.forEach(line => {\n                let cleanLine = cleanAnsi(line);\n                if (!cleanLine) return;\n\n                let timeVal = "[00:00:00]";\n                let level = "INF";\n                let msg = cleanLine;\n\n                // Support separator: │ or |\n                const sep = cleanLine.includes(\'│\') ? \'│\' : (cleanLine.includes(\'|\') ? \'|\' : null);\n                if (sep) {\n                    const parts = cleanLine.split(sep);\n                    if (parts.length >= 3) {\n                        const rawTime = parts[0].trim();\n                        timeVal = `[${rawTime.includes(\' \') ? rawTime.split(\' \')[1] : rawTime}]`;\n                        level = parts[1].trim();\n                        msg = parts.slice(2).join(sep).trim();\n                    }\n                } else {\n                    const match = cleanLine.match(/^([A-Z]{3,7})\\s+(.*)$/);\n                    if (match) {\n                        level = match[1];\n                        msg = match[2];\n                    }\n                }\n\n                // Normalise level\n                let normLevel = level.toUpperCase();\n                if (normLevel === \'INFO\') normLevel = \'INF\';\n                if (normLevel === \'WARNING\' || normLevel === \'WARN\') normLevel = \'WRN\';\n                if (normLevel === \'ERROR\') normLevel = \'ERR\';\n                if (normLevel === \'DEBUG\') normLevel = \'DBG\';\n\n                // Filter logic\n                if (currentFilter === \'INF\' && normLevel !== \'INF\') return;\n                if (currentFilter === \'WRN\' && normLevel !== \'WRN\') return;\n                if (currentFilter === \'ERR\' && normLevel !== \'ERR\') return;\n\n                if (searchKeyword && !msg.toLowerCase().includes(searchKeyword)) return;\n\n                const row = document.createElement(\'div\');\n                row.className = \'log-row\';\n\n                let badgeClass = \'badge-sys\';\n                if (normLevel === \'INF\') badgeClass = \'badge-info\';\n                else if (normLevel === \'DBG\') badgeClass = \'badge-dbg\';\n                else if (normLevel === \'WRN\') badgeClass = \'badge-warn\';\n                else if (normLevel === \'ERR\') badgeClass = \'badge-err\';\n\n                row.innerHTML = `\n                    <span class="log-time">${escapeHtml(timeVal)}</span>\n                    <span class="log-badge ${badgeClass}">${escapeHtml(normLevel)}</span>\n                    <span class="log-text">${formatLogMessage(msg)}</span>\n                `;\n                screen.appendChild(row);\n            });\n\n            if (autoScrollEnabled && wasAtBottom) {\n                screen.scrollTop = screen.scrollHeight;\n            }\n        }\n\n        async function fetchLogs() {\n            try {\n                const res = await fetch(\'/api/logs\');\n                if (!res.ok) return;\n                const data = await res.json();\n                rawLogs = data.logs || [];\n                renderLogs();\n            } catch (err) {\n                console.error("Error fetching logs:", err);\n            }\n        }\n\n        // Periodic Live Polling\n        fetchStats();\n        fetchRecentJoins();\n        fetchLogs();\n\n        setInterval(fetchStats, 1500);\n        setInterval(fetchRecentJoins, 2500);\n        setInterval(fetchLogs, 1800);\n    </script>\n</body>\n</html>\n"""\n\ndef run_server(port):\n    t_tracker = threading.Thread(target=_record_cpm_tick, daemon=True)\n    t_tracker.start()\n\n    # ("", port) binds every interface. The dashboard exposes live token state\n    # and is guarded by one config password, so it defaulted to being reachable\n    # from the whole LAN while the log line below claimed localhost. Loopback\n    # unless the operator explicitly opts out.\n    host = str(load_config().get("dashboard_host", "127.0.0.1")).strip() or "127.0.0.1"\n    server_address = (host, port)\n    # Use ThreadingHTTPServer to handle concurrent dashboard UI polling without latency spikes\n    try:\n        httpd = http.server.ThreadingHTTPServer(server_address, DashboardHandler)\n    except AttributeError:\n        from socketserver import ThreadingMixIn\n        class ThreadingHTTPServerFallback(ThreadingMixIn, http.server.HTTPServer):\n            daemon_threads = True\n        httpd = ThreadingHTTPServerFallback(server_address, DashboardHandler)\n\n    httpd.daemon_threads = True\n    log.info(f"Dashboard Web {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Listening on {Fore.CYAN}http://{host}:{port}{Style.RESET_ALL}")\n    httpd.serve_forever()\n\ndef start_dashboard(port=5050):\n    t = threading.Thread(target=run_server, args=(port,), daemon=True)\n    t.start()\n    return t\n\n\ndef _input_post(self):\n    if not self._check_auth():\n        return\n    if self.path != "/api/inputs":\n        self.send_response(404)\n        self.end_headers()\n        return\n    try:\n        length = int(self.headers.get("Content-Length", "0"))\n        payload = json.loads(self.rfile.read(length).decode("utf-8"))\n        tokens = [line.strip() for line in str(payload.get("tokens", "")).splitlines() if line.strip()]\n        invites = [line.strip() for line in str(payload.get("invites", "")).splitlines() if line.strip()]\n        os.makedirs("input", exist_ok=True)\n        with open("input/tokens.txt", "w", encoding="utf-8") as handle:\n            handle.write("\\n".join(dict.fromkeys(tokens)) + ("\\n" if tokens else ""))\n        with open("input/invites.txt", "w", encoding="utf-8") as handle:\n            handle.write("\\n".join(dict.fromkeys(invites)) + ("\\n" if invites else ""))\n        body = json.dumps({"ok": True, "token_count": len(tokens), "invite_count": len(invites)}).encode("utf-8")\n        self.send_response(200)\n        self.send_header("Content-Type", "application/json")\n        self.send_header("Content-Length", str(len(body)))\n        self.end_headers()\n        self.wfile.write(body)\n    except (ValueError, TypeError, json.JSONDecodeError):\n        self.send_response(400)\n        self.end_headers()\n\n\nDashboardHandler.do_POST = _input_post\nHTML_CONTENT = r\'\'\'<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Join Dashboard</title><style>body{margin:0;background:#101417;color:#edf2ef;font:16px system-ui;max-width:1000px;padding:32px;margin:auto}main{display:grid;grid-template-columns:1fr 1fr;gap:16px}section{background:#1b2324;border:1px solid #374344;padding:18px}textarea{width:100%;min-height:220px;box-sizing:border-box;background:#101417;color:#edf2ef;border:1px solid #52605f;padding:12px;font:14px monospace}button{margin-top:16px;padding:10px 18px;background:#71d6a1;border:0;font-weight:700}@media(max-width:700px){main{grid-template-columns:1fr}}</style></head><body><h1>Join Dashboard</h1><p>Enter one value per line. Submitted values are stored in the local input queues.</p><form id="form"><main><section><h2>Tokens</h2><textarea id="tokens" placeholder="one token per line"></textarea></section><section><h2>Invites</h2><textarea id="invites" placeholder="one invite code or URL per line"></textarea></section></main><button>Update queues</button><span id="message"></span></form><script>form.onsubmit=async e=>{e.preventDefault();let r=await fetch(\'/api/inputs\',{method:\'POST\',headers:{\'Content-Type\':\'application/json\'},body:JSON.stringify({tokens:tokens.value,invites:invites.value})});let d=await r.json();message.textContent=d.ok?\' Queues updated\':\' Update failed\'};</script></body></html>\'\'\'',
    'utils.discord_bot': r'''# utils/discord_bot.py — Filler stats bot

import time
import threading
import asyncio
import discord
from discord import app_commands

from colorama import Fore, Style
from utils.core import STATS, START_TIME, get_cpm, setup_logger, write_json_atomic, update_config_keys
from config import load_config

log = setup_logger(__name__)

# ── Intents ──────────────────────────────────────────────────────────────────
intents = discord.Intents.default()
client  = discord.Client(intents=intents)
tree    = app_commands.CommandTree(client)

# The message that gets continuously edited for live stats
_live_message = None
_live_message_lock = threading.Lock()


# ── Helpers ───────────────────────────────────────────────────────────────────
def _make_progress_bar(percentage: float, length: int = 10) -> str:
    """Generate a modern high-contrast block progress bar string."""
    filled = int(round(length * (percentage / 100)))
    filled = max(0, min(length, filled))
    return "▰" * filled + "▱" * (length - filled)


def _build_embed() -> discord.Embed:
    import os
    cfg = load_config()
    elapsed = time.time() - START_TIME
    hours, rem = divmod(int(elapsed), 3600)
    mins,  sec = divmod(rem, 60)

    joined        = STATS.get("unlocked", 0)
    locked        = STATS.get("locked",   0)
    invalid       = STATS.get("invalid",  0)
    rate          = STATS.get("rate",     0)
    error         = STATS.get("error",    0)
    solves        = STATS.get("captcha_solves", 0)

    loaded_tokens = []
    if os.path.exists("input/tokens.txt"):
        try:
            with open("input/tokens.txt", "r", encoding="utf-8", errors="ignore") as f:
                loaded_tokens = [l.strip() for l in f if l.strip()]
        except Exception:
            pass

    token_count = STATS.get("total_tokens", len(loaded_tokens))
    if not token_count:
        token_count = len(loaded_tokens)

    invite_count = STATS.get("total_invites", 0)
    if not invite_count and os.path.exists("input/invites.txt"):
        try:
            with open("input/invites.txt", "r", encoding="utf-8", errors="ignore") as f:
                invite_count = sum(1 for line in f if line.strip())
        except Exception:
            invite_count = 0

    active_tok = STATS.get("active_tokens", token_count)
    if active_tok <= 0:
        active_tok = max(token_count, 1)

    in_use = STATS.get("tokens_in_use", 0)
    max_guild_limit = cfg.get("max_guild_limit", 80)
    cpm = get_cpm()

    total_processed = joined + locked + invalid
    success_pct = round(joined / total_processed * 100, 1) if total_processed else 0.0

    # Progress calculations
    total_target = max(joined + invite_count, 1)
    queue_pct = round(joined / total_target * 100, 1)
    queue_bar = _make_progress_bar(queue_pct, 10)

    # Accurate Token Capacity Progress (Strictly scoped to currently loaded token pool)
    guilds_db = {}
    if os.path.exists("output/joined_guilds.json"):
        try:
            import json
            with open("output/joined_guilds.json", "r", encoding="utf-8") as f:
                guilds_db = json.load(f)
        except Exception:
            pass

    if loaded_tokens:
        total_loaded_joins = sum(len(guilds_db.get(tok, [])) for tok in loaded_tokens)
        effective_count = len(loaded_tokens)
        avg_joins_per_token = round(total_loaded_joins / effective_count, 1)
    else:
        effective_count = max(active_tok, 1)
        avg_joins_per_token = round(joined / effective_count, 1)

    token_cap_pct = min(100.0, round((avg_joins_per_token / max_guild_limit) * 100, 1)) if max_guild_limit else 0.0
    token_cap_bar = _make_progress_bar(token_cap_pct, 10)

    success_bar = _make_progress_bar(success_pct, 10)

    solver_cfg = cfg.get("solver", {})
    solver_name = solver_cfg.get("type", "bitsolver").upper() if solver_cfg.get("enabled", True) else "DISABLED"
    threads_count = cfg.get("threads", 1)

    embed = discord.Embed(
        title="⚡  BIT FILLER • Live Automation Engine",
        description=(
            f"**Engine Status:** `🟢 Active` • **Threads:** `{threads_count}` • **Solver:** `{solver_name}`\n"
            f"━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        ),
        color=0x5865F2,
        timestamp=discord.utils.utcnow(),
    )

    # 1. Primary Metrics (ANSI Color Codeblocks)
    embed.add_field(
        name="🟢  Joined",
        value=f"```ansi\n\u001b[1;32m{joined:,}\u001b[0m\n```",
        inline=True,
    )
    embed.add_field(
        name="🔒  Locked (403)",
        value=f"```ansi\n\u001b[1;33m{locked:,}\u001b[0m\n```",
        inline=True,
    )
    embed.add_field(
        name="🔴  Invalid (401)",
        value=f"```ansi\n\u001b[1;31m{invalid:,}\u001b[0m\n```",
        inline=True,
    )

    cpm_display = f"{cpm:.2f}" if isinstance(cpm, float) else f"{cpm}"
    embed.add_field(
        name="⚡  Join Velocity",
        value=f"```ansi\n\u001b[1;36m{cpm_display} CPM\u001b[0m\n```",
        inline=True,
    )
    embed.add_field(
        name="⏱  Uptime",
        value=f"```ansi\n\u001b[1;35m{hours:02d}h {mins:02d}m {sec:02d}s\u001b[0m\n```",
        inline=True,
    )
    embed.add_field(
        name="🧩  Captcha Solves",
        value=f"```ansi\n\u001b[1;33m{solves:,} Solved\u001b[0m\n```",
        inline=True,
    )

    # 2. Visual Progress Bars
    embed.add_field(
        name="📊  Progress & Capacity",
        value=(
            f"**Queue:** `[{queue_bar}]` **{queue_pct}%** ({joined:,} joined)\n"
            f"**Token Capacity:** `[{token_cap_bar}]` **{token_cap_pct}%** ({avg_joins_per_token:.1f} / {max_guild_limit} guilds/token)\n"
            f"**Success:** `[{success_bar}]` **{success_pct}%** conversion"
        ),
        inline=False,
    )

    # 3. Token Pool State
    embed.add_field(
        name="🪙  Token Pool & Capacity",
        value=f"```yaml\nTotal Loaded: {token_count}  |  Active Pool: {active_tok}  |  In-Use: {in_use}\nMax Capacity: {max_guild_limit} guilds per token\n```",
        inline=False,
    )

    # 4. Recent Server Joins Feed
    recent_joins = []
    if os.path.exists("output/joined.txt"):
        try:
            with open("output/joined.txt", "r", encoding="utf-8", errors="ignore") as f:
                lines = [l.strip() for l in f if l.strip()]
                for line in lines[-4:]:
                    parts = [p.strip() for p in line.split("|")]
                    if len(parts) >= 3:
                        raw_tok = parts[0]
                        short_tok = raw_tok[:4] + "..." + raw_tok[-4:] if len(raw_tok) > 10 else raw_tok
                        gid = parts[1]
                        gname = parts[2]
                        recent_joins.append(f"• 🌐 **{gname}** (`{short_tok}`) • `{gid}`")
                    elif len(parts) == 1:
                        raw_tok = parts[0]
                        short_tok = raw_tok[:4] + "..." + raw_tok[-4:] if len(raw_tok) > 10 else raw_tok
                        recent_joins.append(f"• 🌐 **Joined Server** (`{short_tok}`)")
        except Exception:
            pass

    if recent_joins:
        embed.add_field(
            name="🎯  Recent Server Joins",
            value="\n".join(reversed(recent_joins)),
            inline=False,
        )

    embed.set_footer(
        text="Bit Filler v1.08 • Live 24/7 Engine Monitor • Auto-updates",
        icon_url="https://cdn.discordapp.com/emojis/1049964177583685652.webp?size=96&quality=lossless"
    )
    return embed


def _save_channel_and_msg_id(channel_id: str, message_id: str):
    """Persist both bot_stats_channel_id and bot_stats_message_id back into config.json."""
    try:
        update_config_keys({
            "bot_stats_channel_id": str(channel_id),
            "bot_stats_message_id": str(message_id),
        })
        log.info(f"Discord bot: saved channel_id={channel_id} and message_id={message_id} to config.json")
    except Exception as e:
        log.warning(f"Discord bot: failed to save stats IDs to config: {e}")


def _is_admin(interaction: discord.Interaction) -> bool:
    """Return True if user is listed in admin_user_ids or has Discord Administrator permissions."""
    cfg = load_config()
    allowed_ids = [str(uid).strip() for uid in cfg.get("admin_user_ids", []) if str(uid).strip()]
    user_id = str(interaction.user.id)

    # If explicit admin IDs are configured in config.json
    if allowed_ids:
        return user_id in allowed_ids

    # Fallback check: Discord guild Administrator permission
    if interaction.permissions and interaction.permissions.administrator:
        return True

    # Guild owner check
    if interaction.guild and interaction.guild.owner_id == interaction.user.id:
        return True

    return False


# ── Discord Bot Slash Commands for Remote Control ─────────────────────────────────

@tree.command(name="stats", description="Post the live stats panel in this channel.")
async def stats_cmd(interaction: discord.Interaction):
    global _live_message
    try:
        await interaction.response.send_message("📊 Posting live stats panel...", ephemeral=True)
        embed = await asyncio.to_thread(_build_embed)
        msg = await interaction.channel.send(embed=embed)
        _live_message = msg
        _save_channel_and_msg_id(str(interaction.channel_id), str(msg.id))
    except Exception as e:
        log.warning(f"Discord bot: error handling /stats command: {e}")


@tree.command(name="addtokens", description="[Admin Only] Add new tokens to input/tokens.txt.")
@app_commands.describe(tokens="One or more tokens (separated by spaces or newlines)")
async def addtokens_cmd(interaction: discord.Interaction, tokens: str):
    if not _is_admin(interaction):
        await interaction.response.send_message("⛔ You do not have permission to run this command.", ephemeral=True)
        return
    try:
        await interaction.response.defer(ephemeral=True)
        token_lines = [t.strip() for t in tokens.replace(",", " ").split() if t.strip()]
        if not token_lines:
            await interaction.followup.send("❌ No valid tokens provided.", ephemeral=True)
            return

        from utils.account import file_write_lock
        with file_write_lock:
            with open("input/tokens.txt", "a", encoding="utf-8") as f:
                for t in token_lines:
                    f.write(f"{t}\n")

        await interaction.followup.send(
            f"✅ Successfully appended **{len(token_lines)}** new token(s) to `input/tokens.txt`!\n"
            f"💡 Restart the joiner using `/restart` to load them into the running pool.",
            ephemeral=True
        )
        log.info(f"Discord bot: {interaction.user} added {len(token_lines)} token(s) via /addtokens.")
    except Exception as e:
        await interaction.followup.send(f"❌ Error adding tokens: {e}", ephemeral=True)


@tree.command(name="addinvites", description="[Admin Only] Add new invite codes/links to input/invites.txt.")
@app_commands.describe(invites="One or more invite links/codes (separated by spaces)")
async def addinvites_cmd(interaction: discord.Interaction, invites: str):
    if not _is_admin(interaction):
        await interaction.response.send_message("⛔ You do not have permission to run this command.", ephemeral=True)
        return
    try:
        await interaction.response.defer(ephemeral=True)
        invite_lines = [i.strip() for i in invites.replace(",", " ").split() if i.strip()]
        if not invite_lines:
            await interaction.followup.send("❌ No valid invites provided.", ephemeral=True)
            return

        from utils.account import file_write_lock
        with file_write_lock:
            with open("input/invites.txt", "a", encoding="utf-8") as f:
                for inv in invite_lines:
                    f.write(f"{inv}\n")

        await interaction.followup.send(
            f"✅ Successfully appended **{len(invite_lines)}** new invite(s) to `input/invites.txt`!\n"
            f"💡 Restart the joiner using `/restart` to process them.",
            ephemeral=True
        )
        log.info(f"Discord bot: {interaction.user} added {len(invite_lines)} invite(s) via /addinvites.")
    except Exception as e:
        await interaction.followup.send(f"❌ Error adding invites: {e}", ephemeral=True)


@tree.command(name="restart", description="[Admin Only] Restart the Filler joiner process.")
async def restart_cmd(interaction: discord.Interaction):
    if not _is_admin(interaction):
        await interaction.response.send_message("⛔ You do not have permission to run this command.", ephemeral=True)
        return
    try:
        await interaction.response.send_message("🔄 Restarting Filler process now...", ephemeral=True)
        log.info(f"Discord bot: restart command received from {interaction.user}. Triggering process restart...")
        import os, sys
        os.execv(sys.executable, [sys.executable] + sys.argv)
    except Exception as e:
        log.error(f"Discord bot: failed to restart: {e}")





async def _auto_update_loop():
    global _live_message

    # Wait until bot is ready
    await client.wait_until_ready()

    while not client.is_closed():
        try:
            cfg        = load_config()
            channel_id = cfg.get("bot_stats_channel_id", "").strip()
            message_id = cfg.get("bot_stats_message_id", "").strip()

            if not channel_id:
                # If channel ID isn't set yet, sleep 10s and check again
                await asyncio.sleep(10)
                continue

            # Fetch the channel
            channel = client.get_channel(int(channel_id))
            if channel is None:
                try:
                    channel = await client.fetch_channel(int(channel_id))
                except Exception as e:
                    log.warning(f"Discord bot: could not fetch stats channel {channel_id}: {e}")
                    await asyncio.sleep(30)
                    continue

            # Try to fetch existing message if _live_message is not set
            channel_name = getattr(channel, 'name', f"DM-{channel.id}")
            if _live_message is None and message_id:
                try:
                    _live_message = await channel.fetch_message(int(message_id))
                    log.info(f"Discord bot: resumed editing existing stats message (id={message_id}) in #{channel_name}")
                except discord.NotFound:
                    log.info("Discord bot: stored message ID not found — posting a new stats message.")
                    _live_message = None
                except Exception as e:
                    log.warning(f"Discord bot: error fetching stored message: {e}")
                    _live_message = None

            # Post a fresh message if we don't have one yet
            if _live_message is None:
                try:
                    embed = await asyncio.to_thread(_build_embed)
                    _live_message = await channel.send(embed=embed)
                    _save_channel_and_msg_id(str(channel.id), str(_live_message.id))
                    log.info(f"Discord bot: live stats panel posted in #{channel_name} (id={_live_message.id})")
                except Exception as e:
                    log.warning(f"Discord bot: failed to post initial stats: {e}")
                    await asyncio.sleep(30)
                    continue

            # Edit message with latest stats
            try:
                embed = await asyncio.to_thread(_build_embed)
                await _live_message.edit(embed=embed)
                log.debug("Discord bot: live stats panel updated.")
            except discord.NotFound:
                # Message was deleted — re-post and save new ID
                try:
                    embed = await asyncio.to_thread(_build_embed)
                    _live_message = await channel.send(embed=embed)
                    _save_channel_and_msg_id(str(channel.id), str(_live_message.id))
                    log.info(f"Discord bot: stats message re-posted (id={_live_message.id})")
                except Exception as ex:
                    log.warning(f"Discord bot: failed to re-post stats: {ex}")
            except Exception as e:
                log.warning(f"Discord bot: error updating stats panel: {e}")

        except Exception as e:
            log.warning(f"Discord bot: unexpected error in auto-update loop: {e}")

        # Sleep 30 seconds between auto-edits for snappy live updates
        await asyncio.sleep(30)


# ── Events ────────────────────────────────────────────────────────────────────
@client.event
async def on_ready():
    try:
        await tree.sync()
        log.info(f"Discord Bot {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Ready as {Fore.CYAN}{client.user}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}│{Style.RESET_ALL} Slash commands synced")
    except Exception as e:
        log.warning(f"Discord Bot {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Slash command sync failed: {e}")
    asyncio.ensure_future(_auto_update_loop())


# ── Public entry-point ────────────────────────────────────────────────────────
def start_bot():
    """Start the Discord bot in a background daemon thread. No-op if bot_token is not set."""
    cfg   = load_config()
    token = cfg.get("bot_token", "").strip()
    if not token:
        log.debug("bot_token not set in config.json — Discord bot disabled.")
        return

    def _run():
        asyncio.run(client.start(token))

    t = threading.Thread(target=_run, name="discord-bot", daemon=True)
    t.start()
    log.info(f"Discord Bot {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Starting background worker...")
''',
    'utils.gateway': r'''import json
import threading
import time
import zlib
import uuid
import random
import re

from curl_cffi.requests import Session as CurlSession, CurlWsFlag
from colorama import Fore, Style

from utils.core import setup_logger
from utils.build import CHROME_VERSION, pick_chrome_impersonation, chromium_major_from_profile
from utils.proxy import format_proxy_url

log = setup_logger(__name__)


class DiscordGateway:
    """Discord Gateway WebSocket client using curl_cffi (BoringSSL) for TLS parity
    with the REST API layer (StealthSession / curl_cffi).

    All WebSocket frames route through the same BoringSSL TLS stack and Chrome
    impersonation profile as HTTP REST requests, eliminating the dual TLS
    fingerprint split (JA3/JA4 mismatch) that occurs when using Python's
    standard `websocket-client` library (OpenSSL).
    """

    GATEWAY_URL = "wss://gateway.discord.gg/?v=9&encoding=json&compress=zlib-stream"

    def __init__(self, token, proxy=None, user_agent=None, build_num=502645, profile=None):
        self.token = token
        self.proxy = proxy
        self.build_num = build_num
        self.profile = profile
        if not self.profile:
            from utils.build import get_random_profile
            self.profile = get_random_profile(self.build_num)
        self.user_agent = user_agent or (self.profile.get("user_agent") if self.profile else None)
        self.ws = None
        self._curl_session = None
        self.alive = False
        self.heartbeat_thread = None
        self.receive_thread = None
        self.decompressor = None
        self.buffer = bytearray()
        self.sequence = None
        self.session_id = None
        self.analytics_token = None
        self._heartbeat_acked = True
        self.client_launch_id = (self.profile.get("client_launch_id") if self.profile else None) or str(uuid.uuid4())
        self.client_hb_session_id = str(uuid.uuid4())
        self.qos_seq = 0
        self._send_lock = threading.Lock()
        self._recv_lock = threading.Lock()

    # ── Internal Helpers ──────────────────────────────────────────────

    def _send_text(self, payload_dict):
        """Send a JSON payload as a WebSocket TEXT frame through BoringSSL."""
        if not self.ws:
            return
        # Compact separators to match the browser's JSON.stringify. Every gateway
        # frame a real client sends (IDENTIFY, heartbeats, opcodes) is space-free;
        # emitting `{"op": 2, "d": {...}}` instead of `{"op":2,"d":{...}}` makes
        # every single frame distinguishable from a browser's.
        data = json.dumps(payload_dict, separators=(",", ":")).encode("utf-8")
        with self._send_lock:
            self.ws.send(data, CurlWsFlag.TEXT)

    def _recv_payload(self):
        """Receive and decompress a single gateway payload safely under mutex."""
        with self._recv_lock:
            while self.alive:
                try:
                    data, flags = self.ws.recv()
                    if flags & CurlWsFlag.CLOSE:
                        self.alive = False
                        log.debug(f"Gateway connection closed by server for {self.token[:8]}...")
                        return None
                    if not data:
                        continue
                    self.buffer.extend(data)
                    # The marker has to be checked against the accumulated buffer, not
                    # the last recv chunk. A frame whose final chunk is under 4 bytes
                    # failed the length test, so it was never decompressed and the
                    # buffer grew without bound.
                    if len(self.buffer) >= 4 and self.buffer[-4:] == b'\x00\x00\xff\xff':
                        decompressed = self.decompressor.decompress(self.buffer)
                        self.buffer = bytearray()
                        return json.loads(decompressed.decode("utf-8"))
                except Exception as e:
                    self.alive = False
                    log.debug(f"Error receiving payload: {e}")
                    raise e
            return None

    # ── Connection Lifecycle ──────────────────────────────────────────

    def connect(self):
        """Establish a WebSocket connection to Discord Gateway using curl_cffi
        (BoringSSL) with dynamic TLS impersonation matching the profile."""

        # Select matching TLS impersonation profile for curl_cffi
        os_platform = self.profile.get("os", "Windows") if self.profile else "Windows"
        browser_type = self.profile.get("browser", "Chrome") if self.profile else "Chrome"
        # Read the Chromium major from the user agent, not browser_version: on a
        # desktop profile browser_version is the Electron version while the UA
        # carries the real Chromium, and the TLS profile must match the UA.
        major_ver = chromium_major_from_profile(self.profile) or 136

        if "Safari" in browser_type and ("Mac" in os_platform or os_platform == "macOS"):
            impersonate_target = "safari18_0"
        else:
            # The old ladder only knew 120-136 and fell through to chrome136 for
            # everything else, so a profile claiming Chrome 152 opened the socket
            # with a Chrome 136 handshake.
            impersonate_target = pick_chrome_impersonation(major_ver)

        session_kwargs = {"impersonate": impersonate_target}
        if self.proxy:
            proxy_url = format_proxy_url(self.proxy)
            if proxy_url:
                session_kwargs["proxy"] = proxy_url
                if "127.0.0.1" in proxy_url or "localhost" in proxy_url or "8080" in proxy_url:
                    session_kwargs["verify"] = False

        self._curl_session = CurlSession(**session_kwargs)

        try:
            log.debug(
                f"Connecting to Gateway {Fore.WHITE}→{Style.RESET_ALL} "
                f"token={Fore.CYAN}{self.token[:10]}...{Style.RESET_ALL} "
                f"tls={Fore.CYAN}{impersonate_target}{Style.RESET_ALL}"
            )
            self.ws = self._curl_session.ws_connect(self.GATEWAY_URL)
            self.alive = True
            self.decompressor = zlib.decompressobj()
            self.buffer = bytearray()

            # Read Hello (op 10)
            hello = self._recv_payload()
            if hello.get("op") == 10:
                interval = hello["d"]["heartbeat_interval"] / 1000.0

                # Start heartbeat thread
                self.heartbeat_thread = threading.Thread(
                    target=self._heartbeat, args=(interval,), daemon=True
                )
                self.heartbeat_thread.start()

                # Send identify (op 2)
                self.identify()

                # Resilient frame consumer: read until READY event (op 0, t=READY) or fatal reject
                start_wait = time.time()
                while not self.session_id and self.alive and (time.time() - start_wait < 30.0):
                    try:
                        msg = self._recv_payload()
                    except Exception:
                        break
                    if not msg:
                        continue
                    if msg.get("s") is not None:
                        self.sequence = msg["s"]
                    t = msg.get("t")
                    op = msg.get("op")
                    if t == "READY":
                        ready_data = msg.get("d", {})
                        self.session_id = ready_data.get("session_id")
                        self.analytics_token = ready_data.get("analytics_token")
                        log.debug(
                            f"Gateway connected {Fore.WHITE}→{Style.RESET_ALL} "
                            f"token={Fore.CYAN}{self.token[:10]}...{Style.RESET_ALL} "
                            f"status={Fore.GREEN}online{Style.RESET_ALL} "
                            f"session_id={Fore.CYAN}{self.session_id}{Style.RESET_ALL}"
                        )
                        break
                    elif op in (7, 9):
                        log.debug(f"Gateway rejected identify: op={op}")
                        break

                if self.session_id:
                    # Send post-READY client initializations (op 4, op 41, op 40)
                    self._send_post_ready_telemetry()

                    # Start background receive loop
                    self.receive_thread = threading.Thread(
                        target=self._receive_loop, daemon=True
                    )
                    self.receive_thread.start()

        except Exception as e:
            log.debug(f"Gateway connection error: {e}")
            self.alive = False

    # ── Opcode 2: Identify ────────────────────────────────────────────

    def identify(self):
        """Send op 2 (IDENTIFY) frame matching modern Discord Web client."""
        return self._send_identify()

    def _send_identify(self):
        """Send op 2 (IDENTIFY) frame matching modern Discord Web client."""
        props = self.profile.get("super_properties_raw")
        if not props or not isinstance(props, dict):
            props = self.profile.get("super_properties")
            if isinstance(props, str):
                try:
                    import base64
                    props = json.loads(base64.b64decode(props).decode("utf-8"))
                except Exception:
                    props = {}

        if not props or not isinstance(props, dict):
            props = {}

        installation_id = self.profile.get("installation_id") if self.profile else None
        if not installation_id:
            from utils.build import generate_installation_id
            installation_id = generate_installation_id()

        props = {
            "os": props.get("os", "Linux"),
            "browser": props.get("browser", "Chrome"),
            "device": "",
            "system_locale": props.get("system_locale", "en-US"),
            "has_client_mods": False,
            "browser_user_agent": self.user_agent or props.get("browser_user_agent", "Mozilla/5.0"),
            "browser_version": props.get("browser_version", f"{CHROME_VERSION}.0.0.0"),
            "os_version": props.get("os_version", ""),
            "referrer": self.profile.get("referrer", "https://discord.com/"),
            "referring_domain": self.profile.get("referring_domain", "discord.com"),
            "referrer_current": self.profile.get("referrer_current", ""),
            "referring_domain_current": self.profile.get("referring_domain_current", ""),
            "release_channel": "stable",
            "client_build_number": self.build_num,
            "client_event_source": None,
            "client_launch_id": self.client_launch_id,
            "is_fast_connect": True,
            "installation_id": installation_id,
        }

        payload = {
            "op": 2,
            "d": {
                "token": self.token,
                "capabilities": 1767421,
                "properties": props,
                "client_state": {
                    "guild_versions": {},
                },
            },
        }
        self._send_text(payload)

    # ── Post-READY Initialization (op 4) ──────────────────────────────

    def _send_post_ready_telemetry(self):
        """Send post-READY client initialization frames matching official web
        client connection sequence: voice state (op 4)."""
        try:
            # Op 4: Voice State Update (unmuted/undeafened by default)
            self._send_text({
                "op": 4,
                "d": {
                    "guild_id": None,
                    "channel_id": None,
                    # Capture sends self_mute true and flags 2.
                    "self_mute": True,
                    "self_deaf": False,
                    "self_video": False,
                    "flags": 2,
                },
            })

            # Op 40: QoS Telemetry (ver 31, foregrounded)
            self.send_qos_telemetry(active=True, reasons=["foregrounded"])

            # Op 41: App Skeleton Initialization Sync
            self.send_app_skeleton_sync()
        except Exception as e:
            log.debug(f"Post-READY initialization error: {e}")

    # ── Opcode 41: App Skeleton Session Sync ─────────────────────────

    def send_app_skeleton_sync(self):
        """Send op 41 (APP_SKELETON_SYNC) matching live web client post-READY initialization."""
        if not self.alive or not self.ws or not self.session_id:
            return
        try:
            self._send_text({
                "op": 41,
                "d": {
                    "initialization_timestamp": int(time.time() * 1000),
                    # Capture uses a fresh UUID here, distinct from the gateway
                    # session id (which is 32 hex chars with no dashes).
                    "session_id": str(uuid.uuid4()),
                    "client_launch_id": self.client_launch_id,
                },
            })
        except Exception as e:
            log.debug(f"APP_SKELETON_SYNC (op 41) error: {e}")

    # ── Opcode 40: QoS Telemetry ─────────────────────────────────────

    def send_qos_telemetry(self, active=True, reasons=None):
        """Send op 40 QoS state telemetry with an incrementing seq counter matching live ver 30."""
        if not self.alive or not self.ws:
            return
        try:
            self.qos_seq += 1
            if reasons is None:
                reasons = ["foregrounded"] if active else []
            self._send_text({
                "op": 40,
                "d": {
                    "seq": self.qos_seq,
                    "qos": {
                        "active": active,
                        "ver": 31,
                        "reasons": reasons,
                    },
                },
            })
        except Exception as e:
            log.debug(f"QoS telemetry error: {e}")

    # ── Opcode 13: Channel Select ────────────────────────────────────

    def select_channel(self, channel_id, guild_id=None):
        """Send op 13 (CHANNEL_SELECT) to register UI focus on a channel."""
        if not self.alive or not self.ws:
            return
        try:
            d_payload = {"channel_id": str(channel_id)}
            if guild_id:
                d_payload["guild_id"] = str(guild_id)
            self._send_text({
                "op": 13,
                "d": d_payload,
            })
        except Exception as e:
            log.debug(f"CHANNEL_SELECT (op 13) error: {e}")

    # ── Opcode 14: Guild Viewport Subscriptions ──────────────────────

    def subscribe_guild_ranges(self, guild_id, channel_id=None, ranges=None):
        """Send op 14 (GUILD_SUBSCRIPTIONS) to subscribe to member ranges in channel viewport."""
        if not self.alive or not self.ws:
            return
        try:
            channels_payload = {}
            if channel_id:
                channels_payload[str(channel_id)] = ranges if ranges is not None else [[0, 99]]
            self._send_text({
                "op": 14,
                "d": {
                    "guild_id": str(guild_id),
                    "channels": channels_payload,
                },
            })
        except Exception as e:
            log.debug(f"GUILD_SUBSCRIPTIONS (op 14) error: {e}")

    # ── Opcode 37: Guild Subscriptions ───────────────────────────────

    def subscribe_guild(self, guild_id, channel_id=None, channels_dict=None, ranges=None, minimal=False):
        """Send op 37 (GUILD_SUBSCRIPTIONS) to subscribe to guild events matching live client schema."""
        if not self.alive or not self.ws:
            return
        try:
            if minimal and (channel_id or channels_dict):
                channels_payload = channels_dict or {str(channel_id): ranges if ranges is not None else [[0, 99]]}
                self._send_text({
                    "op": 37,
                    "d": {
                        "subscriptions": {
                            str(guild_id): {
                                "channels": channels_payload
                            }
                        }
                    },
                })
                return

            channels_payload = channels_dict or {}
            if channel_id and not channels_dict:
                channels_payload[str(channel_id)] = ranges if ranges is not None else [[0, 99]]

            # The captured op 37 for a guild subscription is exactly these three
            # keys in this order. The members/member_updates/thread_member_lists
            # keys the client can send in other situations were being added to
            # every subscription, which the capture never shows.
            guild_sub = {
                "typing": True,
                "activities": True,
                "threads": True,
            }
            if channels_payload:
                guild_sub["channels"] = channels_payload

            self._send_text({
                "op": 37,
                "d": {
                    "subscriptions": {
                        str(guild_id): guild_sub
                    }
                },
            })

            # Op 43: Voice Channel Status & Voice Start Time Subscription
            self.subscribe_voice_channel_status(guild_id)
        except Exception as e:
            log.debug(f"GUILD_SUBSCRIPTIONS (op 37) error: {e}")

    # ── Opcode 43: Voice Channel Status Subscription ─────────────────

    def subscribe_voice_channel_status(self, guild_id, fields=None):
        """Send op 43 (VOICE_CHANNEL_STATUS_SUBSCRIBE) matching live client schema."""
        if not self.alive or not self.ws:
            return
        try:
            self._send_text({
                "op": 43,
                "d": {
                    "guild_id": str(guild_id),
                    "fields": fields if fields is not None else ["status", "voice_start_time"],
                },
            })
        except Exception as e:
            log.debug(f"VOICE_CHANNEL_STATUS_SUBSCRIBE (op 43) error: {e}")

    # ── Opcode 8: Request Guild Members ──────────────────────────────

    def request_guild_members(self, guild_id, query=None, limit=10, presences=False, user_ids=None):
        """Send op 8 (REQUEST_GUILD_MEMBERS) matching official client schema.

        All four op 8 frames in websocket_history.xml carry explicit user_ids with
        presences:false. The blank-query form is not something the observed client
        ever sends, so with neither ids nor a query there is nothing worth sending.
        """
        if not self.alive or not self.ws:
            return
        if user_ids is None and query is None:
            return
        try:
            # Key order follows the capture exactly: guild_id, user_ids, presences.
            # json.dumps preserves insertion order, and a client that serialises
            # the same fields in a different order is distinguishable from one
            # that does not.
            d_payload = {
                "guild_id": [str(guild_id)] if not isinstance(guild_id, list) else [str(g) for g in guild_id],
            }
            if user_ids is not None:
                d_payload["user_ids"] = [str(u) for u in user_ids] if isinstance(user_ids, list) else [str(user_ids)]
            else:
                d_payload["query"] = query if query is not None else ""
                d_payload["limit"] = limit
            d_payload["presences"] = presences

            self._send_text({
                "op": 8,
                "d": d_payload,
            })
        except Exception as e:
            log.debug(f"REQUEST_GUILD_MEMBERS (op 8) error: {e}")

    # ── Opcode 3: Presence Update (Custom Status) ────────────────────

    def update_presence(self, status="online", custom_status_text=None, emoji_name=None):
        """Send op 3 (PRESENCE_UPDATE) to update online status and custom status."""
        if not self.alive or not self.ws:
            return
        try:
            activities = []
            if custom_status_text:
                act = {
                    "name": "Custom Status",
                    "type": 4,
                    "state": str(custom_status_text),
                }
                if emoji_name:
                    act["emoji"] = {"name": emoji_name}
                activities.append(act)

            self._send_text({
                "op": 3,
                "d": {
                    "since": 0,
                    "activities": activities,
                    "status": status,
                    "afk": False,
                },
            })
        except Exception as e:
            log.debug(f"PRESENCE_UPDATE (op 3) error: {e}")

    # ── Background Receive Loop ──────────────────────────────────────

    def _receive_loop(self):
        """Background loop that processes incoming gateway events.
        Handles heartbeat ACKs, reconnect requests, and invalid sessions."""
        while self.alive:
            try:
                payload = self._recv_payload()
                if not payload:
                    continue

                # Update sequence number from every dispatch
                if payload.get("s") is not None:
                    self.sequence = payload["s"]

                op = payload.get("op")

                # Heartbeat ACK (op 11)
                if op == 11:
                    self._heartbeat_acked = True

                # Reconnect requested (op 7)
                elif op == 7:
                    log.debug(f"Gateway reconnect requested for {self.token[:8]}...")
                    self.alive = False
                    break

                # Invalid Session (op 9)
                elif op == 9:
                    resumable = payload.get("d", False)
                    log.debug(
                        f"Gateway invalid session for {self.token[:8]}... "
                        f"resumable={resumable}"
                    )
                    self.alive = False
                    break

                # Heartbeat request from server (op 1)
                elif op == 1:
                    try:
                        self._send_text({"op": 1, "d": self.sequence})
                    except Exception:
                        break

            except Exception as e:
                log.debug(f"Gateway receive error: {e}")
                self.alive = False
                break

    # ── Heartbeat ─────────────────────────────────────────────────────

    def _heartbeat(self, interval):
        # Initial jitter delay per Discord Gateway spec: heartbeat_interval * random(0.1, 0.4)
        time.sleep(interval * random.uniform(0.1, 0.4))
        while self.alive:
            try:
                self._send_text({"op": 1, "d": self.sequence})
                self._heartbeat_acked = False
            except Exception:
                break
            time.sleep(interval)

    # ── Close ─────────────────────────────────────────────────────────

    def close(self):
        self.alive = False
        if self.ws:
            try:
                self.ws.close()
            except Exception:
                pass
            log.debug(
                f"Gateway connection closed {Fore.WHITE}→{Style.RESET_ALL} "
                f"token={Fore.CYAN}{self.token[:10]}...{Style.RESET_ALL}"
            )
        if getattr(self, "_curl_session", None):
            try:
                self._curl_session.close()
            except Exception:
                pass
''',
    'utils.license': r'''"""Bit Joiner Hardware-Bound Cryptographic License Verification Module.

Authenticates client licenses against the Cloudflare Worker server using:
1. Multi-platform deterministic Hardware ID (HWID) generation.
2. Cryptographic RSA-SHA256 (RSASSA-PKCS1-v1_5) digital signature verification.
3. Expiration, tool type, and server-side revocation checks.
4. Background heartbeat verification thread.
"""

import os
import sys
import time
import json
import uuid
import base64
import hashlib
import platform
import subprocess
import threading
import urllib.request
import urllib.error

try:
    from colorama import Fore, Style
except ImportError:
    class _Empty:
        def __getattr__(self, name):
            return ""
    Fore = _Empty()
    Style = _Empty()

try:
    import requests
except ImportError:
    requests = None

try:
    from utils.core import setup_logger, write_json_atomic, update_config_keys
    log = setup_logger(__name__)
except Exception:
    import logging
    log = logging.getLogger(__name__)

    def write_json_atomic(path, obj, indent=2):
        # Fallback when utils.core is unavailable; same temp-file + replace contract.
        import json as _json, os as _os
        _dir = _os.path.dirname(path)
        if _dir:
            _os.makedirs(_dir, exist_ok=True)
        _tmp = f"{path}.tmp"
        with open(_tmp, "w", encoding="utf-8") as _f:
            _json.dump(obj, _f, indent=indent)
        _os.replace(_tmp, path)

    _fallback_config_lock = __import__("threading").Lock()

    def update_config_keys(updates, config_path="input/config.json"):
        # Fallback when utils.core is unavailable; same locked merge contract.
        import json as _json, os as _os
        with _fallback_config_lock:
            existing = {}
            if _os.path.exists(config_path):
                with open(config_path, "r", encoding="utf-8") as _f:
                    existing = _json.load(_f)
            if not isinstance(existing, dict):
                raise ValueError(f"{config_path} is not a JSON object")
            existing.update(updates)
            write_json_atomic(config_path, existing)
            return existing

# Cloudflare Worker default verification endpoint
DEFAULT_WORKER_URL = "https://licences.madejak222.workers.dev"

# How stale a signed licence response may be before it is treated as a replay.
# Wide enough to absorb ordinary clock drift between this machine and the worker,
# narrow enough that a captured response is worthless within the hour.
LICENSE_RESPONSE_MAX_AGE = 600  # seconds

# Server Public Key (JWK RS256 parameters)
RSA_PUBLIC_MODULUS_B64 = (
    "3zsG2cSNMz8VuWkR-yI7klawhersIrgntBvg2_4-lmGKg5wcj7Af0lfn_tEMKeWssHoW9E3wHzM4"
    "7V1JEbMatla8Zp4_ZLrM9AvpBU7tGLMSqWzWndvU9nbBY4UhH2DWG_unl9xS9oNCDv2XWTiDG3xn"
    "8i9a41I65s_il1oCKxta9KFrUDEIlzSGvca8yODGX_ahN997y0yKjQxjNHmWmlRw1W6p4M7RdPOv"
    "p6BhPDJiHEK--i6o2pWTGgQNI_thbsr3m-TDT_BxDk6LmeMlSF2hLzopYSx0KLnzYkckM8GRXgJr"
    "JYEz8B85zT2Djm1UVAWSXuZnE9O1kse6KWjwaw"
)
RSA_PUBLIC_EXPONENT_B64 = "AQAB"

# Global license session state
LICENSE_STATE = {
    "verified": False,
    "license_key": None,
    "hwid": None,
    "user": None,
    "type": "joiner",
    "expires": 0,
    "expires_str": "Lifetime",
}
_heartbeat_thread = None
_heartbeat_stop = threading.Event()


import hmac

try:
    from cryptography.hazmat.primitives.asymmetric import rsa, padding
    from cryptography.hazmat.primitives import hashes
    HAS_CRYPTOGRAPHY = True
except ImportError:
    HAS_CRYPTOGRAPHY = False


def _b64_to_int(b64_str: str) -> int:
    """Convert base64url string to big-endian integer."""
    rem = len(b64_str) % 4
    if rem > 0:
        b64_str += "=" * (4 - rem)
    raw = base64.urlsafe_b64decode(b64_str)
    return int.from_bytes(raw, "big")


def get_hwid() -> str:
    """Generate a stable, unique 64-character SHA-256 hardware identifier for the current machine."""
    components = []
    sys_os = platform.system().lower()

    try:
        if "win" in sys_os:
            out = subprocess.check_output(["wmic", "csproduct", "get", "uuid"], stderr=subprocess.DEVNULL).decode().strip()
            lines = [l.strip() for l in out.split("\n") if l.strip() and "uuid" not in l.lower()]
            if lines:
                components.append(lines[0])
            out_mb = subprocess.check_output(["wmic", "baseboard", "get", "serialnumber"], stderr=subprocess.DEVNULL).decode().strip()
            lines_mb = [l.strip() for l in out_mb.split("\n") if l.strip() and "serialnumber" not in l.lower()]
            if lines_mb:
                components.append(lines_mb[0])
        elif "linux" in sys_os:
            for p in ("/etc/machine-id", "/var/lib/dbus/machine-id", "/sys/class/dmi/id/product_uuid"):
                if os.path.exists(p):
                    try:
                        with open(p, "r") as f:
                            val = f.read().strip()
                            if val:
                                components.append(val)
                                break
                    except Exception:
                        pass
        elif "darwin" in sys_os:
            out = subprocess.check_output(["ioreg", "-rd1", "-c", "IOPlatformExpertDevice"], stderr=subprocess.DEVNULL).decode()
            for line in out.splitlines():
                if "UUID" in line or "serial-number" in line:
                    if "=" in line:
                        val = line.split("=")[-1].strip().strip('"')
                        if val:
                            components.append(val)
    except Exception:
        pass

    # Node/MAC and CPU platform fallbacks
    try:
        node_mac = str(uuid.getnode())
        components.append(node_mac)
        components.append(platform.processor() or "cpu")
        components.append(platform.machine() or "x86_64")
    except Exception:
        pass

    raw_seed = "|".join(components)
    return hashlib.sha256(raw_seed.encode("utf-8")).hexdigest()


def verify_rsa_signature(payload_str: str, signature_b64: str) -> bool:
    """Verify RSASSA-PKCS1-v1_5 SHA-256 digital signature in constant time."""
    try:
        n = _b64_to_int(RSA_PUBLIC_MODULUS_B64)
        e = _b64_to_int(RSA_PUBLIC_EXPONENT_B64)

        rem = len(signature_b64) % 4
        if rem > 0:
            signature_b64 += "=" * (4 - rem)
        try:
            signature_bytes = base64.urlsafe_b64decode(signature_b64)
        except Exception:
            signature_bytes = base64.b64decode(signature_b64)

        if HAS_CRYPTOGRAPHY:
            pub_numbers = rsa.RSAPublicNumbers(e, n)
            public_key = pub_numbers.public_key()
            public_key.verify(
                signature_bytes,
                payload_str.encode("utf-8"),
                padding.PKCS1v15(),
                hashes.SHA256()
            )
            return True

        sig_int = int.from_bytes(signature_bytes, "big")
        k = (n.bit_length() + 7) // 8
        if len(signature_bytes) != k:
            return False

        decrypted_int = pow(sig_int, e, n)
        em = decrypted_int.to_bytes(k, "big")

        # Constant-time PKCS#1 v1.5 comparison
        sha256_prefix = bytes.fromhex("3031300d060960864801650304020105000420")
        actual_hash = hashlib.sha256(payload_str.encode("utf-8")).digest()
        pad_len = k - 3 - len(sha256_prefix) - len(actual_hash)
        if pad_len < 8:
            return False

        expected_em = b"\x00\x01" + (b"\xff" * pad_len) + b"\x00" + sha256_prefix + actual_hash
        return hmac.compare_digest(em, expected_em)

    except Exception as err:
        log.debug(f"RSA signature verification error: {err}")
        return False


def verify_license(license_key: str, worker_url: str = DEFAULT_WORKER_URL, tool_type: str = "joiner") -> tuple[bool, str, dict]:
    """Verify a license key against the Cloudflare Worker server."""
    if not license_key or not license_key.strip():
        return False, "License key is empty.", {}

    license_key = license_key.strip()
    hwid = get_hwid()

    payload = {
        "licenseKey": license_key,
        "hwid": hwid,
        "type": tool_type,
        "toolType": tool_type,
    }

    try:
        data_bytes = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            f"{worker_url}/",
            data=data_bytes,
            headers={
                "Content-Type": "application/json",
                "User-Agent": "BitSuite/1.0",
            },
            method="POST",
        )

        try:
            with urllib.request.urlopen(req, timeout=12) as response:
                resp_text = response.read().decode("utf-8")
                body = json.loads(resp_text)
        except urllib.error.HTTPError as http_err:
            try:
                err_json = json.loads(http_err.read().decode("utf-8"))
                msg = err_json.get("error", str(http_err))
            except Exception:
                msg = str(http_err)
            return False, f"Server rejected license: {msg}", {}

        payload_str = body.get("payload")
        signature_b64 = body.get("signature")

        if not payload_str or not signature_b64:
            return False, "Malformed server response (missing signed payload/signature).", {}

        if not verify_rsa_signature(payload_str, signature_b64):
            return False, "Cryptographic RSA signature verification failed. Response may have been tampered with.", {}

        verified_data = json.loads(payload_str)

        if verified_data.get("licenseKey") != license_key:
            return False, "License key in signed payload does not match requested key.", {}

        # The worker signs the machine it bound the licence to, and the client
        # was ignoring it. A valid signature only proves the worker produced the
        # response at some point -- not that it produced it for this machine.
        # Without this, one customer could verify once, capture the signed bytes
        # and serve them from any host (license_worker_url is read from
        # config.json), and every other machine would accept them.
        signed_hwid = str(verified_data.get("hwid") or "")
        if signed_hwid and signed_hwid != hwid:
            return False, (
                "License is bound to a different machine. "
                "Contact support if you have changed hardware."
            ), {}

        # Same problem in the time dimension: a captured response stayed valid
        # forever. The worker stamps the payload, so anything older than the
        # window below is a replay rather than a live verification. The window is
        # generous because it is compared against the local clock, which can
        # legitimately drift.
        signed_at = verified_data.get("timestamp")
        if signed_at:
            try:
                age = int(time.time()) - int(signed_at)
            except (TypeError, ValueError):
                return False, "Malformed timestamp in signed payload.", {}
            if age > LICENSE_RESPONSE_MAX_AGE:
                return False, (
                    f"License response is {age // 60} minutes old; expected a live "
                    f"verification. Check this machine's clock, or a replayed response."
                ), {}
            if age < -LICENSE_RESPONSE_MAX_AGE:
                return False, "License response is dated in the future; check this machine's clock.", {}

        if verified_data.get("status") != "active":
            return False, f"License status is '{verified_data.get('status')}'.", {}

        server_type = str(verified_data.get("type", "")).lower()
        if tool_type == "joiner" and server_type not in ("joiner", "filler"):
            return False, f"License is registered for '{server_type}', not 'joiner'.", {}
        elif tool_type == "solver" and server_type != "solver":
            return False, f"License is registered for '{server_type}', not 'solver'.", {}

        expires = verified_data.get("expires", 0)
        now_sec = int(time.time())
        if expires and expires > 0 and now_sec > expires:
            return False, f"License expired on {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(expires))}.", {}

        if not expires or expires == 0:
            exp_str = "Permanent (Lifetime)"
        else:
            remaining_days = max(1, int((expires - now_sec) / 86400))
            date_str = time.strftime("%Y-%m-%d", time.localtime(expires))
            if remaining_days <= 7:
                exp_str = f"Weekly ({remaining_days}d left • {date_str})"
            elif remaining_days <= 31:
                exp_str = f"Monthly ({remaining_days}d left • {date_str})"
            else:
                exp_str = f"Active ({remaining_days}d left • {date_str})"

        LICENSE_STATE.update({
            "verified": True,
            "license_key": license_key,
            "hwid": hwid,
            "user": verified_data.get("user") or verified_data.get("userId") or "Authorized User",
            "type": tool_type,
            "expires": expires,
            "expires_str": exp_str,
        })

        return True, "License successfully verified.", verified_data

    except Exception as e:
        return False, f"License verification error: {e}", {}


# A heartbeat failure that is NOT a signed answer from the worker -- DNS blip,
# timeout, a Cloudflare 5xx page -- says nothing about the license. Only exit on
# a verified negative, or after this many consecutive unreachable checks.
HEARTBEAT_MAX_TRANSPORT_MISSES = 3
_TRANSPORT_FAILURE_PREFIXES = ("License verification error:", "Malformed server response")


def _heartbeat_loop(worker_url: str):
    """Periodic background thread to check license validity."""
    misses = 0
    while not _heartbeat_stop.is_set():
        if _heartbeat_stop.wait(timeout=1800):
            break
        if LICENSE_STATE.get("license_key"):
            ok, msg, _ = verify_license(LICENSE_STATE["license_key"], worker_url, tool_type=LICENSE_STATE.get("type", "joiner"))
            if ok:
                misses = 0
                continue
            if msg.startswith(_TRANSPORT_FAILURE_PREFIXES):
                misses += 1
                log.warning(
                    f"License heartbeat could not reach the license server "
                    f"({misses}/{HEARTBEAT_MAX_TRANSPORT_MISSES}): {msg}"
                )
                if misses < HEARTBEAT_MAX_TRANSPORT_MISSES:
                    continue
            log.error(f"{Fore.LIGHTRED_EX}Background license heartbeat failed: {msg}{Style.RESET_ALL}")
            LICENSE_STATE["verified"] = False
            print(f"\n{Fore.RED}[!] LICENSE REVOKED OR EXPIRED: {msg}{Style.RESET_ALL}")
            os._exit(1)


def start_heartbeat(worker_url: str = DEFAULT_WORKER_URL):
    """Start background license heartbeat thread."""
    global _heartbeat_thread
    if _heartbeat_thread and _heartbeat_thread.is_alive():
        return
    _heartbeat_stop.clear()
    _heartbeat_thread = threading.Thread(target=_heartbeat_loop, args=(worker_url,), daemon=True)
    _heartbeat_thread.start()


def ensure_license(config: dict = None) -> dict:
    """Ensure a valid Bit Joiner license is active before running the application."""
    cfg = config or {}
    worker_url = cfg.get("license_worker_url") or DEFAULT_WORKER_URL
    license_key = cfg.get("license_key", "").strip()

    if license_key:
        print(f"{Fore.CYAN}[*]{Style.RESET_ALL} Authenticating Bit Joiner license key...")
        ok, msg, data = verify_license(license_key, worker_url, tool_type="joiner")
        if ok:
            print(
                f"{Fore.GREEN}[+]{Style.RESET_ALL} License Verified {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} "
                f"Type={Fore.CYAN}Joiner{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}│{Style.RESET_ALL} "
                f"Plan={Fore.YELLOW}{LICENSE_STATE['expires_str']}{Style.RESET_ALL}"
            )
            start_heartbeat(worker_url)
            return LICENSE_STATE
        else:
            print(f"{Fore.RED}[-]{Style.RESET_ALL} Configured license invalid: {Fore.YELLOW}{msg}{Style.RESET_ALL}")

    hwid = get_hwid()
    print(f"\n{Fore.CYAN}======================================================{Style.RESET_ALL}")
    print(f"       🔑  {Fore.YELLOW}BIT JOINER LICENSE ACTIVATION{Style.RESET_ALL}")
    print(f"{Fore.CYAN}======================================================{Style.RESET_ALL}")
    print(f" {Fore.WHITE}HWID Fingerprint:{Style.RESET_ALL} {Fore.CYAN}{hwid[:16]}...{hwid[-16:]}{Style.RESET_ALL}")
    print(f" {Fore.WHITE}Support/Purchase:{Style.RESET_ALL} Discord / Reseller Portal")
    print(f"{Fore.CYAN}------------------------------------------------------{Style.RESET_ALL}\n")

    max_attempts = 3
    for attempt in range(1, max_attempts + 1):
        try:
            key_input = input(f"{Fore.GREEN}Enter License Key{Fore.LIGHTBLACK_EX} (Attempt {attempt}/{max_attempts}): {Style.RESET_ALL}").strip()
        except (KeyboardInterrupt, EOFError):
            print(f"\n{Fore.RED}[!] Activation aborted by user.{Style.RESET_ALL}")
            sys.exit(1)

        if not key_input:
            continue

        print(f"{Fore.CYAN}[*]{Style.RESET_ALL} Contacting authentication server...")
        ok, msg, data = verify_license(key_input, worker_url, tool_type="joiner")
        if ok:
            print(
                f"\n{Fore.GREEN}[+]{Style.RESET_ALL} License Activated Successfully! "
                f"{Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} Plan={Fore.YELLOW}{LICENSE_STATE['expires_str']}{Style.RESET_ALL}\n"
            )

            try:
                update_config_keys({"license_key": key_input})
                print(f"{Fore.GREEN}[+]{Style.RESET_ALL} License saved to input/config.json")
            except Exception as save_err:
                log.debug(f"Failed to save license key to config.json: {save_err}")

            start_heartbeat(worker_url)
            time.sleep(1.0)
            return LICENSE_STATE
        else:
            print(f"{Fore.RED}[-] Verification Failed: {msg}{Style.RESET_ALL}\n")

    print(f"{Fore.RED}[!] Exceeded maximum activation attempts. Exiting...{Style.RESET_ALL}")
    sys.exit(1)


def ensure_solver_license(config: dict = None) -> dict:
    """Ensure a valid Bit Solver license (type='solver') is active before starting solver service."""
    cfg = config or {}
    worker_url = cfg.get("license_worker_url") or DEFAULT_WORKER_URL

    solver_config_path = os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "Bit Solver", "config.json"
    )
    license_key = cfg.get("license_key", "").strip()
    if not license_key and os.path.exists(solver_config_path):
        try:
            with open(solver_config_path, "r", encoding="utf-8") as f:
                solver_cfg = json.load(f)
            license_key = solver_cfg.get("license_key", "").strip()
        except Exception:
            pass

    if license_key:
        print(f"{Fore.CYAN}[*]{Style.RESET_ALL} Authenticating Bit Solver license key...")
        ok, msg, data = verify_license(license_key, worker_url, tool_type="solver")
        if ok:
            print(
                f"{Fore.GREEN}[+]{Style.RESET_ALL} Solver License Verified "
                f"{Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} "
                f"Type={Fore.CYAN}Solver{Style.RESET_ALL} "
                f"{Fore.LIGHTBLACK_EX}│{Style.RESET_ALL} "
                f"Plan={Fore.YELLOW}{LICENSE_STATE['expires_str']}{Style.RESET_ALL}"
            )
            start_heartbeat(worker_url)
            return LICENSE_STATE
        else:
            print(f"{Fore.RED}[-]{Style.RESET_ALL} Saved solver license invalid: {Fore.YELLOW}{msg}{Style.RESET_ALL}")

    hwid = get_hwid()
    print(f"\n{Fore.CYAN}══════════════════════════════════════════════{Style.RESET_ALL}")
    print(f"       🔑  {Fore.YELLOW}BIT SOLVER LICENSE ACTIVATION{Style.RESET_ALL}")
    print(f"{Fore.CYAN}══════════════════════════════════════════════{Style.RESET_ALL}")
    print(f" {Fore.WHITE}HWID Fingerprint:{Style.RESET_ALL} {Fore.CYAN}{hwid[:16]}...{hwid[-16:]}{Style.RESET_ALL}")
    print(f" {Fore.WHITE}Requires:{Style.RESET_ALL}        A valid {Fore.YELLOW}Bit Solver{Style.RESET_ALL} license key")
    print(f" {Fore.WHITE}Purchase:{Style.RESET_ALL}        Discord / Reseller Portal")
    print(f"{Fore.CYAN}──────────────────────────────────────────────{Style.RESET_ALL}\n")

    max_attempts = 3
    for attempt in range(1, max_attempts + 1):
        try:
            key_input = input(
                f"{Fore.GREEN}Enter Bit Solver Key{Fore.LIGHTBLACK_EX} "
                f"(Attempt {attempt}/{max_attempts}): {Style.RESET_ALL}"
            ).strip()
        except (KeyboardInterrupt, EOFError):
            print(f"\n{Fore.RED}[!] Activation aborted.{Style.RESET_ALL}")
            sys.exit(1)

        if not key_input:
            continue

        print(f"{Fore.CYAN}[*]{Style.RESET_ALL} Contacting authentication server...")
        ok, msg, data = verify_license(key_input, worker_url, tool_type="solver")
        if ok:
            print(
                f"\n{Fore.GREEN}[+]{Style.RESET_ALL} Bit Solver Activated! "
                f"{Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} "
                f"Plan={Fore.YELLOW}{LICENSE_STATE['expires_str']}{Style.RESET_ALL}\n"
            )
            try:
                existing = {}
                if os.path.exists(solver_config_path):
                    with open(solver_config_path, "r", encoding="utf-8") as f:
                        existing = json.load(f)
                existing["license_key"] = key_input
                write_json_atomic(solver_config_path, existing)
                print(f"{Fore.GREEN}[+]{Style.RESET_ALL} License saved to Bit Solver/config.json")
            except Exception as save_err:
                log.debug(f"Failed to save solver license key: {save_err}")

            start_heartbeat(worker_url)
            time.sleep(1.0)
            return LICENSE_STATE
        else:
            print(f"{Fore.RED}[-] Verification Failed: {msg}{Style.RESET_ALL}\n")

    print(f"{Fore.RED}[!] Exceeded maximum activation attempts. Bit Solver will not start.{Style.RESET_ALL}")
    sys.exit(1)
''',
    'utils.profile_customizer': r'''import os
import time
import random
import struct
import zlib
import base64
import json
import requests

from utils.core import setup_logger, format_token_id

log = setup_logger(__name__)

# Curated list of realistic, natural Discord user bios
REALISTIC_BIOS = [
    "living in the moment ✨",
    "collecting memories, not things 🌌",
    "keep moving forward 🚀",
    "do what makes your soul shine 🌿",
    "lost in the right direction 🧭",
    "making my own magic ✨",
    "stay humble, stay curious.",
    "coffee, lo-fi, and good vibes ☕🎧",
    "casual gamer 🎮 | listening to spotify 🎧",
    "climbing ranked / casual vibes only",
    "just here for the games and memes",
    "gg wp 🎮",
    "offline most of the time",
    "playing games & sleeping",
    "building things on the web 💻",
    "code, sleep, repeat ⚡",
    "learning something new every day",
    "hi there 👋",
    "not much to see here :)",
    "peace & quiet 🌙",
    "student | tech enthusiast",
    "vibing ✌️",
    "music on, world off 🎵",
    "always learning, always improving 📈",
    "passionate about art and design 🎨",
    "night owl 🦉",
    "catching sunsets and good vibes 🌅",
    "chasing dreams one step at a time ✨",
]

# Curated list of natural custom status messages and matching emojis
REALISTIC_STATUSES = [
    ("listening to music 🎧", "🎧"),
    ("chilling ☕", "☕"),
    ("vibing ✨", "✨"),
    ("afk for a bit 💤", "💤"),
    ("gaming 🎮", "🎮"),
    ("studying 📚", "📚"),
    ("working on stuff 💻", "💻"),
    ("offline maybe 🌙", "🌙"),
    ("lo-fi & chill 🎵", "🎵"),
    ("enjoying the day 🌿", "🌿"),
    ("busy right now", "⏳"),
    ("grinding 🔥", "🔥"),
    ("eating snacks 🍕", "🍕"),
    ("reading 📖", "📖"),
    ("resting 🛌", "🛌"),
]

# Color palettes for local pure-Python PNG avatar generator
AVATAR_PALETTES = [
    ((88, 101, 242), (235, 69, 158)),   # Blurple to Neon Pink
    ((59, 165, 93), (88, 101, 242)),    # Green to Blurple
    ((237, 66, 69), (254, 231, 92)),    # Red to Yellow
    ((244, 127, 255), (114, 137, 218)), # Lavender to Soft Blurple
    ((32, 34, 37), (114, 137, 218)),    # Dark slate to Indigo
    ((87, 242, 135), (59, 165, 92)),    # Mint to Emerald
    ((254, 231, 92), (235, 69, 158)),   # Sunlight to Rose
    ((0, 180, 216), (114, 9, 183)),     # Cyan to Deep Violet
    ((247, 37, 133), (76, 201, 240)),   # Magenta to Sky Blue
    ((112, 224, 0), (0, 114, 0)),       # Lime to Forest
]


def _generate_local_avatar_png(width=128, height=128) -> str:
    """Generate an aesthetic geometric gradient avatar PNG purely using Python standard library."""
    c1, c2 = random.choice(AVATAR_PALETTES)
    style = random.choice(["radial", "diagonal", "circles"])

    raw_data = bytearray()
    cx, cy = width / 2.0, height / 2.0

    for y in range(height):
        raw_data.append(0)  # PNG filter type 0 (None)
        for x in range(width):
            if style == "radial":
                dist = ((x - cx) ** 2 + (y - cy) ** 2) ** 0.5
                t = min(1.0, max(0.0, dist / (width * 0.7)))
            elif style == "diagonal":
                t = min(1.0, max(0.0, (x + y) / (width + height)))
            else:
                dist = ((x - cx) ** 2 + (y - cy) ** 2) ** 0.5
                t = min(1.0, max(0.0, (dist % 24) / 24.0))

            r = int(c1[0] * (1.0 - t) + c2[0] * t)
            g = int(c1[1] * (1.0 - t) + c2[1] * t)
            b = int(c1[2] * (1.0 - t) + c2[2] * t)
            raw_data.extend([r, g, b])

    def chunk(tag, data):
        return struct.pack(">I", len(data)) + tag + data + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
    idat = zlib.compress(bytes(raw_data), 9)
    png_bytes = b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", ihdr) + chunk(b"IDAT", idat) + chunk(b"IEND", b"")
    return "data:image/png;base64," + base64.b64encode(png_bytes).decode("utf-8")


def _to_discord_avatar_data_uri(raw_bytes: bytes) -> str:
    """Normalize and convert any image bytes (WebP, PNG, JPEG, GIF, BMP) to a 100% Discord-compliant 256x256 JPEG data URI."""
    try:
        import io
        from PIL import Image
        img = Image.open(io.BytesIO(raw_bytes))
        if img.mode in ("RGBA", "LA", "P"):
            bg = Image.new("RGB", img.size, (255, 255, 255))
            if img.mode == "P":
                img = img.convert("RGBA")
            bg.paste(img, mask=img.split()[3] if len(img.split()) == 4 else None)
            img = bg
        else:
            img = img.convert("RGB")

        img = img.resize((256, 256), Image.Resampling.LANCZOS)
        buf = io.BytesIO()
        img.save(buf, format="JPEG", quality=90)
        b64 = base64.b64encode(buf.getvalue()).decode("utf-8")
        return f"data:image/jpeg;base64,{b64}"
    except Exception as e:
        log.debug(f"Pillow image conversion fallback: {e}")
        b64 = base64.b64encode(raw_bytes).decode("utf-8")
        return f"data:image/jpeg;base64,{b64}"


def generate_random_avatar(token: str = "") -> str:
    """Generate or fetch a real, authentic Discord profile picture (PFP).
    
    Priority:
    1. Local custom avatars folder: input/avatars/*.png, *.jpg, *.jpeg, *.webp
    2. Authentic web feeds: Real cats, dogs, aesthetic photography, nature/city crops
    3. Built-in gradient fallback (if offline)
    """
    import glob

    # 1. Check if user provided local custom avatar files in input/avatars/
    avatar_dir = "input/avatars"
    if os.path.exists(avatar_dir):
        local_files = []
        for ext in ("*.png", "*.jpg", "*.jpeg", "*.webp", "*.gif"):
            local_files.extend(glob.glob(os.path.join(avatar_dir, ext)))
            local_files.extend(glob.glob(os.path.join(avatar_dir, ext.upper())))

        if local_files:
            chosen = random.choice(local_files)
            try:
                with open(chosen, "rb") as f:
                    data = f.read()
                if len(data) > 100:
                    log.info(f"Loaded custom local avatar from {chosen}")
                    return _to_discord_avatar_data_uri(data)
            except Exception as e:
                log.debug(f"Failed to read local avatar {chosen}: {e}")

    # 2. Fetch authentic, human-like Discord PFPs from online feeds
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
    sources = ["cat", "dog", "aesthetic", "cat"]
    chosen_src = random.choice(sources)

    if chosen_src == "cat":
        try:
            r = requests.get("https://cataas.com/cat?width=256&height=256", headers=headers, timeout=4.0)
            if r.status_code == 200 and len(r.content) > 1000:
                return _to_discord_avatar_data_uri(r.content)
        except Exception:
            pass

    elif chosen_src == "dog":
        try:
            r_api = requests.get("https://dog.ceo/api/breeds/image/random", headers=headers, timeout=3.0)
            if r_api.status_code == 200:
                dog_url = r_api.json().get("message")
                if dog_url:
                    r_img = requests.get(dog_url, headers=headers, timeout=4.0)
                    if r_img.status_code == 200 and len(r_img.content) > 1000:
                        return _to_discord_avatar_data_uri(r_img.content)
        except Exception:
            pass

    elif chosen_src == "aesthetic":
        try:
            seed = token[-6:] if token else str(random.randint(100, 9999))
            r = requests.get(f"https://picsum.photos/seed/{seed}/256/256", headers=headers, timeout=4.0)
            if r.status_code == 200 and len(r.content) > 1000:
                return _to_discord_avatar_data_uri(r.content)
        except Exception:
            pass

    # 3. Fallback: Aesthetic photography or local gradient
    try:
        r = requests.get("https://picsum.photos/256/256", headers=headers, timeout=3.0)
        if r.status_code == 200 and len(r.content) > 1000:
            return _to_discord_avatar_data_uri(r.content)
    except Exception:
        pass

    return _generate_local_avatar_png()


def get_random_bio() -> str:
    """Select a realistic random bio for the account."""
    return random.choice(REALISTIC_BIOS)


def get_random_status() -> tuple:
    """Select a realistic random custom status and matching emoji."""
    return random.choice(REALISTIC_STATUSES)


def auto_customize_account_profile(session, token: str, gateway=None, force: bool = False) -> bool:
    """Disabled: Whole profile customization is currently disabled."""
    return True


def browser_edit_profile_in_client(page, token: str) -> bool:
    """Disabled: Whole profile customization is currently disabled."""
    return True

''',
    'utils.proxy': r'''import os, threading, random, hashlib
from colorama import Fore, Style
from config import load_config

from utils.core import setup_logger

log = setup_logger()

def format_proxy_url(proxy: str | None) -> str | None:
    """Normalize any proxy format into a standard URL (http://user:pass@host:port or http://host:port).
    Returns None for direct connections ("direct", "none", etc.).
    
    Supports:
    - direct / none       -> None (direct network connection)
    - host:port:user:pass -> http://user:pass@host:port
    - user:pass:host:port -> http://user:pass@host:port
    - user:pass@host:port -> http://user:pass@host:port
    - host:port           -> http://host:port
    - http(s)://...       -> http(s)://...
    - socks5(h)://...     -> socks5(h)://...
    """
    if not proxy or not isinstance(proxy, str):
        return None
    proxy = proxy.strip()
    if not proxy:
        return None

    # Handle direct connection strings
    if proxy.lower() in ("direct", "none", "localhost", "direct://", "direct:"):
        return None

    scheme = "http"
    if "://" in proxy:
        scheme, proxy = proxy.split("://", 1)

    if "@" in proxy:
        return f"{scheme}://{proxy}"

    # A password may itself contain a colon, so the field count is not a reliable
    # guide: split off only the fields whose position is fixed and let the
    # remainder be the password. The old code split on every colon and, for
    # anything it could not classify, returned the raw string with a scheme glued
    # on -- a malformed URL that curl then failed on in a way that looked like a
    # dead proxy rather than a parse error.
    parts = proxy.split(":")

    if len(parts) == 2:
        # host:port
        return f"{scheme}://{proxy}"

    if len(parts) >= 4:
        if parts[1].isdigit():
            # host:port:user:pass (password may contain further colons)
            host, port, user = parts[0], parts[1], parts[2]
            password = ":".join(parts[3:])
            return f"{scheme}://{user}:{password}@{host}:{port}"
        if parts[-1].isdigit():
            # user:pass:host:port (password may contain further colons)
            user = parts[0]
            host, port = parts[-2], parts[-1]
            password = ":".join(parts[1:-2])
            return f"{scheme}://{user}:{password}@{host}:{port}"

    # Nothing here matches a proxy shape. Returning a malformed URL would send a
    # broken address to curl; the caller can handle "no proxy" but not garbage.
    log.warning(f"Unrecognised proxy format, ignoring: {proxy.split(':')[0]}:...")
    return None


_timezone_cache = {}
_timezone_cache_lock = threading.Lock()


def get_system_timezone() -> str:
    """Detect local machine timezone dynamically."""
    try:
        if os.path.exists("/etc/timezone"):
            with open("/etc/timezone", "r", encoding="utf-8") as f:
                tz = f.read().strip()
                if tz:
                    return tz
        if os.path.islink("/etc/localtime"):
            target = os.readlink("/etc/localtime")
            parts = target.split("zoneinfo/")
            if len(parts) > 1:
                return parts[1]
    except Exception:
        pass
    try:
        import datetime
        tz = datetime.datetime.now().astimezone().tzinfo
        if hasattr(tz, "key") and tz.key:
            return tz.key
    except Exception:
        pass
    return "America/Los_Angeles"


def detect_timezone(proxy: str | None = None, user_agent: str | None = None) -> str:
    """
    Detects timezone matching the connection (direct IP or proxy IP).
    Caches results to prevent redundant network calls and rate limits.
    Falls back to local machine timezone if network detection is unavailable.
    """
    norm_proxy = format_proxy_url(proxy)
    cache_key = norm_proxy if norm_proxy else "DIRECT"

    with _timezone_cache_lock:
        if cache_key in _timezone_cache:
            return _timezone_cache[cache_key]

    detected = None
    headers = {"User-Agent": user_agent} if user_agent else {"User-Agent": "Mozilla/5.0"}
    proxies_dict = {"http": norm_proxy, "https": norm_proxy} if norm_proxy else None

    # Try ip-api.com first
    try:
        import requests as raw_requests
        r = raw_requests.get("http://ip-api.com/json/", proxies=proxies_dict, headers=headers, timeout=6)
        if r.status_code == 200:
            data = r.json()
            if data.get("status") == "success" and data.get("timezone"):
                detected = data["timezone"]
    except Exception:
        pass

    # Secondary fallback to ipapi.co
    if not detected:
        try:
            import requests as raw_requests
            r = raw_requests.get("https://ipapi.co/timezone/", proxies=proxies_dict, headers=headers, timeout=6)
            if r.status_code == 200 and r.text.strip():
                tz_text = r.text.strip()
                if "/" in tz_text:
                    detected = tz_text
        except Exception:
            pass

    # Tertiary fallback: system timezone for direct, or America/Los_Angeles for proxy
    if not detected:
        if not norm_proxy:
            detected = get_system_timezone()
        else:
            detected = "America/Los_Angeles"

    with _timezone_cache_lock:
        _timezone_cache[cache_key] = detected

    return detected


class ProxyManager:

    def __init__(self, file_path="input/proxies.txt"):
        self.file_path = file_path
        self.lock = threading.RLock()
        self.proxies = self._load_proxies()
        self.available_proxies = set(self.proxies)
        self.initial_load_time = self._get_file_modification_time()

    def _load_proxies(self):
        if not os.path.exists(self.file_path):
            log.warning(f"Warning: Proxy file not found at {self.file_path}. Returning empty list.")
            return []

        proxies = []
        with open(self.file_path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    if line.lower() in ("direct", "none", "localhost", "direct://", "direct:"):
                        proxies.append("direct")
                    else:
                        normalized = format_proxy_url(line)
                        if normalized:
                            proxies.append(normalized)
        return proxies

    def _get_file_modification_time(self):
        if os.path.exists(self.file_path):
            return os.path.getmtime(self.file_path)
        return 0

    def _is_healthy(self, proxy):
        if not proxy or (isinstance(proxy, str) and proxy.lower() in ("direct", "none", "localhost", "direct://", "direct:")):
            return True
        import requests
        proxy_url = format_proxy_url(proxy)
        if not proxy_url:
            return True
        proxies_dict = {"http": proxy_url, "https": proxy_url}
        try:
            # Use api.ipify.org instead of discord.com to prevent triggering bot flagging on Discord
            r = requests.get("https://api.ipify.org", proxies=proxies_dict, timeout=4)
            return True
        except Exception:
            return False

    def active_pool(self, limit=None):
        """The proxies in use, at most `limit` of them.

        A "thread" in this tool is one exit IP with a group of workers behind it,
        so the number of threads is bounded by how many proxies are loaded.
        """
        with self.lock:
            current_mod_time = self._get_file_modification_time()
            if current_mod_time > self.initial_load_time:
                self.reload()
                self.initial_load_time = current_mod_time
            pool = list(self.proxies)
        if limit is not None and limit > 0:
            pool = pool[:limit]
        return pool

    def thread_index_for_token(self, token, thread_count):
        """Which thread (and therefore which exit IP) this token belongs to.

        Derived from the token so the assignment survives restarts: an account
        that changes exit IP between runs also changes its reported timezone,
        which is the new-device signal all of this exists to avoid.
        """
        if thread_count <= 0:
            return 0
        digest = hashlib.sha256(str(token).encode("utf-8")).digest()
        return int.from_bytes(digest[:8], "big") % thread_count

    def get_proxy_for_token(self, token, thread_count=None):
        """The proxy this token always exits from.

        get_proxy() hands out whatever is next in the rotation, so a token could
        appear from a different country on every run -- and the reported timezone
        follows the proxy IP, so the account's clock moved with it. To Discord
        that is one account hopping between machines and regions, which is the
        single strongest new-device signal there is. Deriving the index from the
        token instead pins each account to one exit IP for as long as the proxy
        list is unchanged, with no state file to lose.
        """
        pool = self.active_pool(thread_count)
        if not pool:
            return None
        return pool[self.thread_index_for_token(token, len(pool))]

    def get_proxy(self):
        with self.lock:
            current_mod_time = self._get_file_modification_time()
            if current_mod_time > self.initial_load_time:
                log.debug(f"Proxy file '{self.file_path}' modified. Reloading proxies...")
                self.reload()
                self.initial_load_time = current_mod_time

            if not self.proxies:
                log.warning("No proxies loaded.")
                return None

            # Bug 8: Skip health check for ISP proxies to avoid unnecessary
            # pre-Discord traffic that creates a detectable fingerprint pattern.
            cfg = load_config()
            skip_health = cfg.get("skip_proxy_health_check", False)

            dead_proxies = set()
            while True:
                if not self.available_proxies:
                    log.debug("No available proxies left in current cycle. Resetting...")
                    # Reset, but exclude ones we already verified as dead in this call
                    remaining = set(self.proxies) - dead_proxies
                    if not remaining:
                        if dead_proxies:
                            log.warning("All loaded proxies failed the health check!")
                        return None
                    self.available_proxies = remaining

                proxy_method = cfg.get("proxy_method", "sequential")
                
                if proxy_method == "random" and self.available_proxies:
                    available_list = list(self.available_proxies)
                    proxy = random.choice(available_list)
                    self.available_proxies.remove(proxy)
                else:
                    proxy = self.available_proxies.pop()

                # If skip_proxy_health_check is enabled, return immediately
                if skip_health:
                    return proxy
                    
                if self._is_healthy(proxy):
                    return proxy
                
                clean_name = proxy.split("@")[-1] if "@" in proxy else proxy
                log.warning(f"Proxy failed health check {Fore.LIGHTBLACK_EX}›{Style.RESET_ALL} {Fore.CYAN}{clean_name}{Style.RESET_ALL} (Discarding)")
                dead_proxies.add(proxy)

    def reload(self):
        with self.lock:
            old_proxies = set(self.proxies)
            self.proxies = self._load_proxies()
            new_proxies = set(self.proxies)

            added = new_proxies - old_proxies
            removed = old_proxies - new_proxies

            if added or removed:
                log.debug(f"Reloaded proxies. Added: {len(added)}, Removed: {len(removed)}")
                # host:port only -- these lines reach log/logs.txt and the
                # dashboard's /api/logs, and the scrubber does not mask user:pass@.
                if added: log.debug(f"  New proxies: {', '.join(p.split('@')[-1] for p in added)}")
                if removed: log.debug(f"  Removed proxies: {', '.join(p.split('@')[-1] for p in removed)}")

            self.available_proxies = set(self.proxies)
            self.initial_load_time = self._get_file_modification_time()
            if not self.proxies:
                log.debug("Warning: Proxy file is empty or contains no valid proxies after reload.")''',
    'utils.telemetry': r'''"""Discord /api/v9/science telemetry manager.

Accumulates client interaction events in a thread-safe queue and
periodically flushes them to Discord's analytics endpoint using the
account's existing StealthSession (curl_cffi / BoringSSL).

Faithfully replicates Discord client hardware, viewport, and the exact
6-stage analytics sequence executed during invite acceptance and guild navigation:
  1. invite_opened
  2. invite_viewed
  3. invite_accept_button_rendered
  4. invite_embed_actioned
  5. invite_resolved
  6. guild_joined
"""

import json
import time
import random
import threading
import uuid
import os
import base64

from utils.core import setup_logger, write_json_atomic

log = setup_logger(__name__)

API = "https://discord.com/api/v9"


# Steam Hardware Survey weighted GPU Matrix (Full spectrum: Top, Mid, High-end, Budget & Legacy)
_REAL_GPUS = [
    # Top Mainstream & Modern GPUs (High chances: 30-75)
    {"brand": "NVIDIA GeForce RTX 3060", "vendor_id": 4318, "device_id": 9475, "vram_mb": 12288, "steam_share_weight": 75},
    {"brand": "NVIDIA GeForce RTX 4060", "vendor_id": 4318, "device_id": 10247, "vram_mb": 8192, "steam_share_weight": 52},
    {"brand": "NVIDIA GeForce GTX 1650", "vendor_id": 4318, "device_id": 8081, "vram_mb": 4096, "steam_share_weight": 41},
    {"brand": "NVIDIA GeForce RTX 3060 Ti", "vendor_id": 4318, "device_id": 9352, "vram_mb": 8192, "steam_share_weight": 38},
    {"brand": "NVIDIA GeForce RTX 2060", "vendor_id": 4318, "device_id": 7949, "vram_mb": 6144, "steam_share_weight": 35},
    {"brand": "NVIDIA GeForce RTX 3070", "vendor_id": 4318, "device_id": 9348, "vram_mb": 8192, "steam_share_weight": 34},
    {"brand": "NVIDIA GeForce RTX 4060 Ti", "vendor_id": 4318, "device_id": 10244, "vram_mb": 8192, "steam_share_weight": 31},
    {"brand": "NVIDIA GeForce GTX 1660 SUPER", "vendor_id": 4318, "device_id": 8588, "vram_mb": 6144, "steam_share_weight": 28},
    {"brand": "NVIDIA GeForce RTX 3080", "vendor_id": 4318, "device_id": 8704, "vram_mb": 10240, "steam_share_weight": 22},
    {"brand": "NVIDIA GeForce RTX 4070", "vendor_id": 4318, "device_id": 9924, "vram_mb": 12288, "steam_share_weight": 21},
    {"brand": "NVIDIA GeForce RTX 3050", "vendor_id": 4318, "device_id": 9480, "vram_mb": 8192, "steam_share_weight": 20},
    {"brand": "AMD Radeon RX 6700 XT", "vendor_id": 4098, "device_id": 29631, "vram_mb": 12288, "steam_share_weight": 18},
    {"brand": "AMD Radeon RX 6600", "vendor_id": 4098, "device_id": 29650, "vram_mb": 8192, "steam_share_weight": 17},
    {"brand": "NVIDIA GeForce RTX 4070 Ti", "vendor_id": 4318, "device_id": 9920, "vram_mb": 12288, "steam_share_weight": 15},
    {"brand": "AMD Radeon RX 7800 XT", "vendor_id": 4098, "device_id": 29904, "vram_mb": 16384, "steam_share_weight": 15},
    {"brand": "AMD Radeon RX 7700 XT", "vendor_id": 4098, "device_id": 29906, "vram_mb": 12288, "steam_share_weight": 12},
    {"brand": "NVIDIA GeForce RTX 4080", "vendor_id": 4318, "device_id": 9860, "vram_mb": 16384, "steam_share_weight": 11},
    {"brand": "AMD Radeon RX 7600", "vendor_id": 4098, "device_id": 29920, "vram_mb": 8192, "steam_share_weight": 11},
    {"brand": "NVIDIA GeForce RTX 4090", "vendor_id": 4318, "device_id": 9856, "vram_mb": 24576, "steam_share_weight": 10},
    {"brand": "NVIDIA GeForce RTX 3070 Ti", "vendor_id": 4318, "device_id": 9350, "vram_mb": 8192, "steam_share_weight": 10},
    {"brand": "AMD Radeon RX 6600 XT", "vendor_id": 4098, "device_id": 29648, "vram_mb": 8192, "steam_share_weight": 10},
    {"brand": "NVIDIA GeForce RTX 3080 Ti", "vendor_id": 4318, "device_id": 8710, "vram_mb": 12288, "steam_share_weight": 8},
    {"brand": "NVIDIA GeForce RTX 3090", "vendor_id": 4318, "device_id": 8708, "vram_mb": 24576, "steam_share_weight": 7},
    {"brand": "AMD Radeon RX 7900 XTX", "vendor_id": 4098, "device_id": 29888, "vram_mb": 24576, "steam_share_weight": 8},
    {"brand": "AMD Radeon RX 7900 XT", "vendor_id": 4098, "device_id": 29890, "vram_mb": 20480, "steam_share_weight": 6},

    # Mid & Enthusiast RTX 20/GTX 10 series (Medium-low chances: 4-8)
    {"brand": "NVIDIA GeForce GTX 1060 6GB", "vendor_id": 4318, "device_id": 7171, "vram_mb": 6144, "steam_share_weight": 8},
    {"brand": "NVIDIA GeForce GTX 1070", "vendor_id": 4318, "device_id": 7041, "vram_mb": 8192, "steam_share_weight": 6},
    {"brand": "NVIDIA GeForce GTX 1080", "vendor_id": 4318, "device_id": 7040, "vram_mb": 8192, "steam_share_weight": 5},
    {"brand": "NVIDIA GeForce RTX 2070", "vendor_id": 4318, "device_id": 7946, "vram_mb": 8192, "steam_share_weight": 6},
    {"brand": "NVIDIA GeForce RTX 2080 SUPER", "vendor_id": 4318, "device_id": 7810, "vram_mb": 8192, "steam_share_weight": 5},

    # Budget, Legacy & Integrated GPUs (Low chances: 1-4)
    {"brand": "AMD Radeon RX 580", "vendor_id": 4098, "device_id": 26591, "vram_mb": 8192, "steam_share_weight": 4},
    {"brand": "AMD Radeon RX 570", "vendor_id": 4098, "device_id": 26591, "vram_mb": 4096, "steam_share_weight": 3},
    {"brand": "NVIDIA GeForce GTX 1050 Ti", "vendor_id": 4318, "device_id": 7186, "vram_mb": 4096, "steam_share_weight": 4},
    {"brand": "Intel(R) Arc(TM) A770 Graphics", "vendor_id": 32902, "device_id": 22144, "vram_mb": 16384, "steam_share_weight": 3},
    {"brand": "Intel(R) Arc(TM) A750 Graphics", "vendor_id": 32902, "device_id": 22144, "vram_mb": 8192, "steam_share_weight": 2},
    {"brand": "Intel(R) UHD Graphics 770", "vendor_id": 32902, "device_id": 18001, "vram_mb": 2048, "steam_share_weight": 2},
    {"brand": "Intel(R) Iris(R) Xe Graphics", "vendor_id": 32902, "device_id": 39498, "vram_mb": 4096, "steam_share_weight": 2},
]

# Steam Hardware Survey weighted Intel CPUs (65% market share)
_REAL_CPUS_INTEL = [
    # Top 6-Core Mainstream (High chances: 25-45)
    {"brand": "12th Gen Intel(R) Core(TM) i5-12400F", "vendor": "GenuineIntel", "threads": 12, "weight": 45},
    {"brand": "13th Gen Intel(R) Core(TM) i5-13400F", "vendor": "GenuineIntel", "threads": 16, "weight": 38},
    {"brand": "Intel(R) Core(TM) i5-10400F CPU @ 2.90GHz", "vendor": "GenuineIntel", "threads": 12, "weight": 30},
    {"brand": "11th Gen Intel(R) Core(TM) i5-11400F @ 2.60GHz", "vendor": "GenuineIntel", "threads": 12, "weight": 28},
    {"brand": "13th Gen Intel(R) Core(TM) i5-13600K", "vendor": "GenuineIntel", "threads": 20, "weight": 28},
    {"brand": "14th Gen Intel(R) Core(TM) i5-14600K", "vendor": "GenuineIntel", "threads": 20, "weight": 22},
    # High Performance 8+ Core (Medium chances: 12-25)
    {"brand": "12th Gen Intel(R) Core(TM) i7-12700K", "vendor": "GenuineIntel", "threads": 20, "weight": 24},
    {"brand": "13th Gen Intel(R) Core(TM) i7-13700K", "vendor": "GenuineIntel", "threads": 24, "weight": 22},
    {"brand": "14th Gen Intel(R) Core(TM) i7-14700K", "vendor": "GenuineIntel", "threads": 28, "weight": 18},
    {"brand": "14th Gen Intel(R) Core(TM) i9-14900K", "vendor": "GenuineIntel", "threads": 32, "weight": 14},
    {"brand": "13th Gen Intel(R) Core(TM) i9-13900K", "vendor": "GenuineIntel", "threads": 32, "weight": 12},
    {"brand": "12th Gen Intel(R) Core(TM) i9-12900K", "vendor": "GenuineIntel", "threads": 24, "weight": 10},
    # Budget, Entry & Legacy Core CPUs (Low chances: 3-8)
    {"brand": "12th Gen Intel(R) Core(TM) i3-12100F", "vendor": "GenuineIntel", "threads": 8, "weight": 8},
    {"brand": "10th Gen Intel(R) Core(TM) i3-10100F", "vendor": "GenuineIntel", "threads": 8, "weight": 6},
    {"brand": "Intel(R) Core(TM) i7-10700K CPU @ 3.80GHz", "vendor": "GenuineIntel", "threads": 16, "weight": 8},
    {"brand": "Intel(R) Core(TM) i7-9700K CPU @ 3.60GHz", "vendor": "GenuineIntel", "threads": 8, "weight": 5},
    {"brand": "Intel(R) Core(TM) i7-8700K CPU @ 3.70GHz", "vendor": "GenuineIntel", "threads": 12, "weight": 4},
]

# Steam Hardware Survey weighted AMD CPUs (35% market share)
_REAL_CPUS_AMD = [
    # Top 6-Core Mainstream (High chances: 25-50)
    {"brand": "AMD Ryzen 5 5600X 6-Core Processor", "vendor": "AuthenticAMD", "threads": 12, "weight": 50},
    {"brand": "AMD Ryzen 5 3600 6-Core Processor", "vendor": "AuthenticAMD", "threads": 12, "weight": 38},
    {"brand": "AMD Ryzen 5 5600 6-Core Processor", "vendor": "AuthenticAMD", "threads": 12, "weight": 32},
    {"brand": "AMD Ryzen 5 7600X 6-Core Processor", "vendor": "AuthenticAMD", "threads": 12, "weight": 26},
    # Top 8-Core Gaming (Medium chances: 15-38)
    {"brand": "AMD Ryzen 7 7800X3D 8-Core Processor", "vendor": "AuthenticAMD", "threads": 16, "weight": 38},
    {"brand": "AMD Ryzen 7 5800X 8-Core Processor", "vendor": "AuthenticAMD", "threads": 16, "weight": 32},
    {"brand": "AMD Ryzen 7 5800X3D 8-Core Processor", "vendor": "AuthenticAMD", "threads": 16, "weight": 28},
    {"brand": "AMD Ryzen 7 7700X 8-Core Processor", "vendor": "AuthenticAMD", "threads": 16, "weight": 22},
    {"brand": "AMD Ryzen 9 5900X 12-Core Processor", "vendor": "AuthenticAMD", "threads": 24, "weight": 16},
    {"brand": "AMD Ryzen 9 7950X3D 16-Core Processor", "vendor": "AuthenticAMD", "threads": 32, "weight": 10},
    # Budget, Entry & Legacy Ryzen CPUs (Low chances: 3-8)
    {"brand": "AMD Ryzen 5 2600 Six-Core Processor", "vendor": "AuthenticAMD", "threads": 12, "weight": 7},
    {"brand": "AMD Ryzen 7 2700X Eight-Core Processor", "vendor": "AuthenticAMD", "threads": 16, "weight": 5},
    {"brand": "AMD Ryzen 3 3100 4-Core Processor", "vendor": "AuthenticAMD", "threads": 8, "weight": 4},
]

# Apple Silicon Matrix
_REAL_CPUS_MAC = [
    {"brand": "Apple M2", "vendor": "Apple", "threads": 8, "gpu_brand": "Apple M2", "vendor_id": 4172, "device_id": 0, "vram_mb": 16384, "weight": 35},
    {"brand": "Apple M1", "vendor": "Apple", "threads": 8, "gpu_brand": "Apple M1", "vendor_id": 4172, "device_id": 0, "vram_mb": 8192, "weight": 30},
    {"brand": "Apple M3", "vendor": "Apple", "threads": 8, "gpu_brand": "Apple M3", "vendor_id": 4172, "device_id": 0, "vram_mb": 16384, "weight": 25},
    {"brand": "Apple M2 Pro", "vendor": "Apple", "threads": 10, "gpu_brand": "Apple M2 Pro", "vendor_id": 4172, "device_id": 0, "vram_mb": 16384, "weight": 15},
    {"brand": "Apple M1 Pro", "vendor": "Apple", "threads": 10, "gpu_brand": "Apple M1 Pro", "vendor_id": 4172, "device_id": 0, "vram_mb": 16384, "weight": 15},
    {"brand": "Apple M3 Pro", "vendor": "Apple", "threads": 12, "gpu_brand": "Apple M3 Pro", "vendor_id": 4172, "device_id": 0, "vram_mb": 18432, "weight": 12},
    {"brand": "Apple M3 Max", "vendor": "Apple", "threads": 16, "gpu_brand": "Apple M3 Max", "vendor_id": 4172, "device_id": 0, "vram_mb": 36864, "weight": 8},
    {"brand": "Apple M1 Max", "vendor": "Apple", "threads": 10, "gpu_brand": "Apple M1 Max", "vendor_id": 4172, "device_id": 0, "vram_mb": 32768, "weight": 6},
]

# Steam Hardware Survey exact resolution share:
# Full spectrum including Ultrawide, Laptops, 4K, 5K with authentic proportional chances
_STEAM_RESOLUTIONS = [
    (1920, 1080),   # 1080p (Standard Mainstream): ~58%
    (2560, 1440),   # 1440p 2K (High-End Gaming): ~20%
    (3840, 2160),   # 4K UHD: ~4%
    (3440, 1440),   # 21:9 Ultrawide 1440p: ~3%
    (2560, 1080),   # 21:9 Ultrawide 1080p: ~2%
    (1366, 768),    # 768p (Laptops / Budget): ~4%
    (1600, 900),    # 900p: ~2%
    (1440, 900),    # 16:10 Laptop/Mac: ~2%
    (1680, 1050),   # 16:10 Desktop: ~2%
    (1920, 1200),   # 16:10 1200p: ~2%
    (5120, 1440),   # 32:9 Super Ultrawide: ~1%
]
_STEAM_RESOLUTION_WEIGHTS = [58, 20, 4, 3, 2, 4, 2, 2, 2, 2, 1]

# Steam Hardware Survey exact system RAM share:
# Full spectrum: 4GB to 64GB
_STEAM_RAM_SIZES = [
    16384,  # 16 GB: ~48%
    32768,  # 32 GB: ~32%
    8192,   # 8 GB: ~10%
    65536,  # 64 GB: ~5%
    12288,  # 12 GB: ~3%
    4096,   # 4 GB: ~2%
]
_STEAM_RAM_WEIGHTS = [48, 32, 10, 5, 3, 2]


import os, re

HARDWARE_DB_FILE = "input/hardware_database.json"
_hw_db_lock = threading.Lock()
_last_hw_sync = 0

_DEFAULT_HARDWARE_DB = {
    "gpus": _REAL_GPUS,
    "cpus_intel": _REAL_CPUS_INTEL,
    "cpus_amd": _REAL_CPUS_AMD,
    "cpus_mac": _REAL_CPUS_MAC,
    "resolutions": _STEAM_RESOLUTIONS,
    "ram_sizes": _STEAM_RAM_SIZES,
    "last_updated": 0,
}

_ACTIVE_HARDWARE_DB = _DEFAULT_HARDWARE_DB


def _parse_pci_ids_text(text):
    """Dynamically parse raw pci.ids database text into structured GPU entries with Steam popularity weights."""
    gpus = []
    current_vendor = None

    def get_weight(name):
        if "RTX 3060" in name and "Ti" not in name: return 75
        if "RTX 4060" in name and "Ti" not in name: return 52
        if "GTX 1650" in name: return 41
        if "RTX 3060 Ti" in name: return 38
        if "RTX 2060" in name: return 35
        if "RTX 3070" in name: return 34
        if "RTX 4060 Ti" in name: return 31
        if "GTX 1660" in name: return 28
        if "RTX 3080" in name: return 22
        if "RTX 4070" in name: return 21
        if "RTX 3050" in name: return 20
        if "RX 6700" in name: return 18
        if "RX 6600" in name: return 17
        if "RX 7800" in name: return 15
        if "RTX 4080" in name: return 11
        if "RTX 4090" in name: return 10
        if "RTX 40" in name or "RTX 30" in name or "RX 7" in name or "RX 6" in name: return 10
        if "RTX 20" in name or "GTX 16" in name or "GTX 10" in name: return 5
        return 2

    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        if not line.startswith("\t"):
            parts = line.strip().split("  ", 1)
            if len(parts) == 2:
                current_vendor = parts[0].strip().lower()
        elif line.startswith("\t") and not line.startswith("\t\t") and current_vendor in ["10de", "1002", "8086"]:
            parts = line.strip().split("  ", 1)
            if len(parts) == 2:
                dev_id_hex, raw_name = parts[0].strip(), parts[1].strip()
                clean_name = raw_name
                if "[" in raw_name and "]" in raw_name:
                    m = re.search(r"\[([^\]]+)\]", raw_name)
                    if m: clean_name = m.group(1)

                if any(k in clean_name for k in ["GeForce", "Radeon", "Arc", "Iris", "UHD Graphics", "HD Graphics"]):
                    try:
                        vendor_id = int(current_vendor, 16)
                        dev_id = int(dev_id_hex, 16)
                    except ValueError:
                        continue

                    prefix = "NVIDIA " if current_vendor == "10de" and not clean_name.startswith("NVIDIA") else (
                        "AMD " if current_vendor == "1002" and not clean_name.startswith("AMD") else ""
                    )
                    brand = f"{prefix}{clean_name}"

                    vram_mb = 8192
                    if any(k in brand for k in ["4090", "3090", "7900 XTX"]): vram_mb = 24576
                    elif any(k in brand for k in ["4080", "7800 XT", "6800"]): vram_mb = 16384
                    elif any(k in brand for k in ["4070", "3060", "6700"]): vram_mb = 12288
                    elif any(k in brand for k in ["1650", "1050", "570", "UHD Graphics", "HD Graphics"]): vram_mb = 4096
                    elif any(k in brand for k in ["1660", "1060", "2060"]): vram_mb = 6144

                    gpus.append({
                        "brand": brand,
                        "vendor_id": vendor_id,
                        "device_id": dev_id,
                        "vram_mb": vram_mb,
                        "steam_share_weight": get_weight(brand),
                    })
    return gpus


def sync_hardware_database(force=False):
    """Download and dynamically parse live hardware data every 24 hours, caching to input/hardware_database.json."""
    global _ACTIVE_HARDWARE_DB, _last_hw_sync
    with _hw_db_lock:
        now = time.time()
        os.makedirs("input", exist_ok=True)

        file_exists = os.path.exists(HARDWARE_DB_FILE)
        file_age = (now - os.path.getmtime(HARDWARE_DB_FILE)) if file_exists else 999999

        if file_exists and file_age < 86400 and not force:
            try:
                with open(HARDWARE_DB_FILE, "r", encoding="utf-8") as f:
                    _ACTIVE_HARDWARE_DB = json.load(f)
                _last_hw_sync = now
                return _ACTIVE_HARDWARE_DB
            except Exception as e:
                log.debug(f"Failed to read local hardware database cache: {e}")

        log.info(f"Downloading & dynamically compiling 24-hour hardware database {HARDWARE_DB_FILE}...")
        db_to_save = dict(_DEFAULT_HARDWARE_DB)
        db_to_save["last_updated"] = int(now)

        PCI_MAIN_URL = "https://pci-ids.ucw.cz/v2.2/pci.ids"
        PCI_GITHUB_URL = "https://raw.githubusercontent.com/pciutils/pciids/master/pci.ids"

        import requests as raw_req
        live_gpus = []
        for src_name, url in [("Official Main Registry", PCI_MAIN_URL), ("GitHub Mirror", PCI_GITHUB_URL)]:
            try:
                res = raw_req.get(url, timeout=8)
                if res.status_code == 200 and len(res.text) > 100000:
                    live_gpus = _parse_pci_ids_text(res.text)
                    if live_gpus:
                        log.info(f"Dynamically parsed {len(live_gpus)} live GPUs from {src_name}.")
                        db_to_save["gpus"] = live_gpus
                        break
            except Exception as e:
                log.debug(f"{src_name} download/parse error: {e}")

        if not live_gpus:
            log.info("Live download unreachable; falling back to embedded hardware matrix.")

        try:
            write_json_atomic(HARDWARE_DB_FILE, db_to_save)
            _ACTIVE_HARDWARE_DB = db_to_save
            _last_hw_sync = now
            log.info(f"Hardware database successfully saved to {HARDWARE_DB_FILE} (Valid for 24h).")
        except Exception as e:
            log.debug(f"Failed to write hardware database cache: {e}")

        return _ACTIVE_HARDWARE_DB


try:
    sync_hardware_database()
except Exception:
    pass


# A WebGL renderer string is one of the strongest signals hCaptcha scores, and
# two kinds of entry in the hardware database make an account stand out rather
# than blend in.
#
# Pre-production parts were never sold. An "Engineering Sample" renderer belongs
# to a handful of machines worldwide, so reporting one is closer to a unique
# identifier than to camouflage.
#
# Cards from before roughly 2012 are the opposite problem: they are real, but a
# machine running current Chrome with a Direct3D11 ANGLE backend on a GeForce
# 6250 is not a combination that occurs. Software renderers are excluded for the
# same reason -- they say "no GPU present", which is what a headless browser
# farm looks like.
_IMPLAUSIBLE_GPU = re.compile(
    r"engineering sample|prototype|pre-?release|\bES\b|\bQS\b|"
    r"reference design|generic|standard vga|basic display|"
    r"llvmpipe|softpipe|swiftshader|software (adapter|renderer)|"
    r"microsoft basic|virtualbox|vmware|parallels|remote display|"
    # Datacenter and virtualised parts. These are real silicon, but they are
    # compute accelerators with no display output, or GPUs carved up for VDI.
    # A consumer browser never reports one, so it says "server, not desktop".
    r"instinct|\bMI[0-9]{2,3}\b|arcturus|aldebaran|tesla [KMPVA][0-9]|"
    r"\b[AHVPK](100|40|30|10|80)\b|GRID|vGPU|"
    # Internal codenames that ship in some database rows instead of the retail
    # name. A driver reports the marketing name, not the silicon codename.
    r"GeForce4|GeForce [23] ",
    re.I,
)
_OBSOLETE_GPU = re.compile(
    r"GeForce (6|7|8|9)[0-9]{3}\b|"
    r"GeForce (GT|GTX) ?[1-4][0-9]{2}\b|"
    r"GeForce (FX|4 |2 |3 )|"
    r"Radeon HD [2-6][0-9]{3}\b|Radeon HD [2-6][0-9]{2}\b|"
    r"Radeon (X[0-9]{3,4}|9[0-9]{3})\b|"
    r"Quadro (FX|NVS)|FirePro|"
    r"Intel.*(GMA|G31|G41|Q35|945|965|X3100|HD Graphics [23]000)",
    re.I,
)

_gpu_pool_cache = {}


def plausible_gpus(gpus):
    """Drop pre-production, software and pre-2012 cards from a GPU pool.

    Falls back to the unfiltered pool if the filter would empty it, so a database
    shape this does not anticipate degrades to the old behaviour instead of
    crashing the solver.
    """
    key = id(gpus)
    cached = _gpu_pool_cache.get(key)
    if cached is not None and len(cached[0]) == len(gpus):
        return cached[1]
    kept = [
        g for g in gpus
        if not _IMPLAUSIBLE_GPU.search(str(g.get("brand", "")))
        and not _OBSOLETE_GPU.search(str(g.get("brand", "")))
    ]
    result = kept or list(gpus)
    _gpu_pool_cache[key] = (gpus, result)
    return result


def hardware_seed(value):
    """A stable integer seed from a proxy URL, IP or any other string."""
    import hashlib
    if not value:
        return None
    return int.from_bytes(
        hashlib.sha256(str(value).encode("utf-8")).digest()[:8], "big"
    )



def generate_dynamic_hardware_profile(os_platform="Windows", seed=None):
    """Procedurally synthesize a hardware profile weighted by Steam Hardware Survey popularity.

    `seed` pins the result: passing the proxy makes every account behind one
    exit IP report the same machine, which is what a real household does.
    Drawing fresh every time made one account present a different graphics
    card, and often a different GPU vendor, on every captcha it solved.
    """
    rng = random.Random(seed) if seed is not None else random
    global _ACTIVE_HARDWARE_DB
    if time.time() - _last_hw_sync > 86400:
        sync_hardware_database()

    db = _ACTIVE_HARDWARE_DB or _DEFAULT_HARDWARE_DB
    cpus_mac = db.get("cpus_mac", _REAL_CPUS_MAC)
    cpus_intel = db.get("cpus_intel", _REAL_CPUS_INTEL)
    cpus_amd = db.get("cpus_amd", _REAL_CPUS_AMD)
    gpus = plausible_gpus(db.get("gpus", _REAL_GPUS))

    if "Mac" in os_platform or os_platform == "macOS":
        weights = [c.get("weight", 10) for c in cpus_mac]
        choice = rng.choices(cpus_mac, weights=weights, k=1)[0]
        cpu_brand = choice["brand"]
        cpu_vendor = choice["vendor"]
        threads = choice["threads"]
        gpu_brand = choice["gpu_brand"]
        gpu_vendor_id = choice["vendor_id"]
        gpu_device_id = choice["device_id"]
        gpu_vram = choice["vram_mb"]
        ram_total = gpu_vram
        ram_avail = int(ram_total * rng.uniform(0.48, 0.78))
    elif "Linux" in os_platform:
        all_cpus = cpus_intel + cpus_amd
        weights = [c.get("weight", 10) for c in all_cpus]
        cpu_choice = rng.choices(all_cpus, weights=weights, k=1)[0]
        cpu_brand = cpu_choice["brand"]
        cpu_vendor = cpu_choice["vendor"]
        threads = cpu_choice["threads"]

        gpu_weights = [g.get("steam_share_weight", 10) for g in gpus]
        gpu = rng.choices(gpus, weights=gpu_weights, k=1)[0]
        gpu_brand = f"Mesa {gpu['brand']}"
        gpu_vendor_id = gpu["vendor_id"]
        gpu_device_id = gpu["device_id"]
        gpu_vram = gpu["vram_mb"]

        ram_total = rng.choices(_STEAM_RAM_SIZES, weights=_STEAM_RAM_WEIGHTS, k=1)[0]
        ram_avail = int(ram_total * rng.uniform(0.45, 0.75))
    else:  # Windows (80%+ of users)
        # Steam CPU share: ~65% Intel, ~35% AMD
        if rng.random() < 0.65:
            weights = [c.get("weight", 10) for c in cpus_intel]
            cpu_choice = rng.choices(cpus_intel, weights=weights, k=1)[0]
        else:
            weights = [c.get("weight", 10) for c in cpus_amd]
            cpu_choice = rng.choices(cpus_amd, weights=weights, k=1)[0]

        cpu_brand = cpu_choice["brand"]
        cpu_vendor = cpu_choice["vendor"]
        threads = cpu_choice["threads"]

        # Steam GPU market share weights (RTX 3060 #1, RTX 4060 #2, GTX 1650 #3, etc.)
        gpu_weights = [g.get("steam_share_weight", 10) for g in gpus]
        gpu = rng.choices(gpus, weights=gpu_weights, k=1)[0]
        gpu_brand = gpu["brand"]
        gpu_vendor_id = gpu["vendor_id"]
        gpu_device_id = gpu["device_id"]
        gpu_vram = gpu["vram_mb"]

        # Steam RAM distribution (~49% 16GB, ~32% 32GB, ~9% 8GB, ~4% 64GB)
        ram_total = rng.choices(_STEAM_RAM_SIZES, weights=_STEAM_RAM_WEIGHTS, k=1)[0]
        ram_avail = int(ram_total * rng.uniform(0.42, 0.72))

    # Steam Resolution distribution (~59% 1080p, ~20% 1440p, ~4% 4K)
    res = rng.choices(_STEAM_RESOLUTIONS, weights=_STEAM_RESOLUTION_WEIGHTS, k=1)[0]

    return {
        "cpu_brand": cpu_brand,
        "cpu_vendor": cpu_vendor,
        "hardware_concurrency": threads,
        "system_memory_total": ram_total,
        "system_memory_available": ram_avail,
        "gpu_brand": gpu_brand,
        "gpu_device_vendor_id": gpu_vendor_id,
        "gpu_device_device_id": gpu_device_id,
        "gpu_memory": gpu_vram * 1024,
        "gpu_dedicated_memory": [gpu_vram],
        "screen_width": res[0],
        "screen_height": res[1],
    }


class ScienceTelemetry:
    """Background telemetry manager for /api/v9/science with hardware and event simulation."""

    FLUSH_INTERVAL_MIN = 25.0  # seconds
    FLUSH_INTERVAL_MAX = 50.0  # seconds

    def __init__(self, session, token=None, profile=None, timezone=None, analytics_token=None):
        """
        Args:
            session: The account's StealthSession (curl_cffi) for HTTP requests.
            token: Discord auth token (used for the authorization header).
            profile: Browser/OS profile dict (from utils.build.get_random_profile).
            timezone: Detected proxy timezone.
            analytics_token: Analytics token received from Gateway READY payload.
        """
        self.session = session
        self.token = token
        self.analytics_token = analytics_token
        self.profile = profile or {}
        self.timezone = timezone or "America/Los_Angeles"
        self._events = []
        self._lock = threading.Lock()
        self._stop_event = threading.Event()
        self._running = False
        self._flush_thread = None
        # 16-byte persistent session seed for deterministic client_uuid generation matching live browser
        self._uuid_seed = os.urandom(16)
        self._uuid_counter = 0
        self._session_id = str(uuid.uuid4())
        self._app_state = "focused"
        self._sequence_number = 0
        self._start_time = time.time()

        # Dynamically generate a 100% unique procedural hardware & viewport profile
        os_platform = self.profile.get("os", "Windows")
        self.hw = generate_dynamic_hardware_profile(os_platform)

        self.screen_width = self.hw["screen_width"]
        self.screen_height = self.hw["screen_height"]
        self.hardware_concurrency = self.hw["hardware_concurrency"]
        self._ad_session_id = str(uuid.uuid4())
        self._start_time_ms = int(self._start_time * 1000)

    def set_analytics_token(self, token):
        """Update analytics token received from Gateway READY event."""
        self.analytics_token = token

    def _generate_client_uuid(self):
        """Generate authentic 24-byte Base64 token with session seed and monotonic sequence counter."""
        self._uuid_counter += 1
        counter_bytes = (self._uuid_counter - 1).to_bytes(4, byteorder="big")
        raw_uuid = self._uuid_seed + b"\xa0\x01" + counter_bytes + b"\x00\x00"
        return base64.b64encode(raw_uuid).decode("utf-8")

    def _get_base_properties(self):
        """Standard Discord Web/Desktop client base properties matching live Burp capture."""
        now_ms = int(time.time() * 1000)
        heartbeat_id = self.profile.get("client_heartbeat_session_id") or self._session_id
        launch_sig = self.profile.get("launch_signature") or str(uuid.uuid4())
        self._sequence_number += 1

        return {
            "client_track_timestamp": now_ms,
            "client_heartbeat_session_id": heartbeat_id,
            "event_sequence_number": self._sequence_number,
            # client_ad_session_id / client_heartbeat_initialization_timestamp /
            # client_heartbeat_version appear on ~2% of captured events (specific
            # types), not on every event; stamping them on all of them was a
            # shape no real client produces.
            "client_performance_memory": 0,
            "accessibility_features": 524544,
            "rendered_locale": "en-US",
            "uptime_app": max(0, int(time.time() - self._start_time)),
            "launch_signature": launch_sig,
            "client_rtc_state": "DISCONNECTED",
            "client_app_state": self._app_state,
            "client_viewport_width": self.screen_width,
            "client_viewport_height": self.screen_height,
            "client_uuid": self._generate_client_uuid(),
            "client_send_timestamp": now_ms,
        }

    def start(self):
        """Start the background flush loop."""
        if self._running:
            return
        self._running = True
        self._stop_event.clear()
        self._flush_thread = threading.Thread(target=self._flush_loop, daemon=True)
        self._flush_thread.start()

    def stop(self):
        """Flush remaining events and stop the background thread immediately."""
        self._running = False
        self._stop_event.set()
        self.flush()

    def track(self, event_type, properties=None):
        """Queue a telemetry event with standard client track metadata."""
        base_props = self._get_base_properties()
        if properties:
            base_props.update(properties)

        event = {
            "type": event_type,
            "properties": base_props,
        }
        with self._lock:
            # Enforce max buffer cap to prevent unbounded memory leaks if network stalls
            if len(self._events) >= 500:
                self._events = self._events[-250:]
            self._events.append(event)

    def track_metrics_v2(self, metric_name="notification_sound_playback_attempt", metric_type="count", tags=None, build_number="599735", built_at="1787095329146"):
        """Dispatches count/distribution metrics to /api/v9/metrics/v2."""
        if not self.session:
            return
        if tags is None:
            tags = ["design_id:2", "reason:played", "platform:web", "release_channel:stable"]
        payload = {
            "metrics": [{"name": metric_name, "type": metric_type, "tags": tags}],
            "client_info": {"built_at": built_at, "build_number": str(build_number)},
        }
        try:
            self.session.post(f"{API}/metrics/v2", json=payload)
        except Exception:
            pass

    def track_channel_opened(self, channel_id, guild_id=None, channel_type=0, channel_was_unread=True, guild_was_unread=True, guild_metadata=None):
        """Emits channel_opened telemetry matching official client schema."""
        props = {
            "channel_id": str(channel_id),
            "channel_was_unread": channel_was_unread,
            "channel_mention_count": 0,
            "channel_is_muted": False,
            "channel_is_nsfw": False,
            "channel_is_spoiler": False,
            "channel_resolved_unread_setting": 1,
            "channel_preset": "custom",
            "channel_type": channel_type,
            "channel_size_total": 0,
            "channel_member_perms": "211662467565057",
            "channel_hidden": False,
            "is_app_dm": guild_id is None,
            "selected_guild_id": str(guild_id) if guild_id else None,
            "guild_id": str(guild_id) if guild_id else None,
            "guild_was_unread": guild_was_unread,
            "guild_mention_count": 0,
            "guild_is_muted": False,
            "guild_resolved_unread_setting": 1,
            "guild_preset": "custom",
            "has_pending_member_action": False,
            "can_send_message": True,
        }
        if guild_metadata:
            props.update(guild_metadata)
        self.track("channel_opened", props)

    def track_guild_viewed(self, guild_id, channel_id, num_unread_channels=0, unread_channel_ids=None, guild_metadata=None):
        """Emits guild_viewed telemetry matching official client schema."""
        props = {
            "postable_channels": 4,
            "premium_progress_bar_enabled": False,
            "viewing_all_channels": False,
            "num_recent_channels": 0,
            "num_unread_channels": num_unread_channels,
            "unread_channel_ids": unread_channel_ids or [],
            "guild_theme_enabled": False,
            "guild_theme_is_custom": False,
            "guild_id": str(guild_id),
            "channel_id": str(channel_id),
            "channel_type": 0,
            "channel_size_total": 0,
            "channel_member_perms": "211662467565057",
            "channel_hidden": False,
        }
        if guild_metadata:
            props.update(guild_metadata)
        self.track("guild_viewed", props)

    def track_member_list_viewed(self, guild_id, channel_id, num_users_visible=14, guild_metadata=None):
        """Emits member_list_viewed telemetry matching official client schema."""
        props = {
            "num_users_visible": num_users_visible,
            "num_users_visible_with_mobile_indicator": 1,
            "num_users_visible_with_game_activity": 4,
            "num_users_visible_with_activity": 6,
            "num_users_visible_with_avatar_decoration": 3,
            "num_users_visible_with_nameplate": 2,
            "guild_id": str(guild_id),
            "channel_id": str(channel_id),
            "channel_type": 0,
            "channel_size_total": 0,
            "channel_member_perms": "211662467565057",
            "channel_hidden": False,
        }
        if guild_metadata:
            props.update(guild_metadata)
        self.track("member_list_viewed", props)

    def track_ack_messages(self, channel_id, guild_id=None, guild_unread_statuses=None, guild_metadata=None):
        """Emits ack_messages telemetry matching official client schema."""
        props = {
            "channel_id": str(channel_id),
            "guild_id": str(guild_id) if guild_id else None,
            "guild_unread_statuses": guild_unread_statuses or [],
            "channel_type": 0 if guild_id else 1,
            "channel_size_total": 0,
            "channel_member_perms": "211662467565057" if guild_id else "0",
            "channel_hidden": False,
            "location_section": "Channel",
            "location_object": "Ack - Incoming Message",
            "location_object_type": "ack_automatic",
        }
        if guild_metadata:
            props.update(guild_metadata)
        self.track("ack_messages", props)

    def track_impression_invite_embed(self, invite_code, guild_id, channel_id, current_channel_id, message_id):
        """Emits impression_invite_embed telemetry matching official client schema."""
        props = {
            "impression_type": "view",
            "channel_id": str(current_channel_id),
            "channel_type": 1,
            "channel_size_total": 1,
            "channel_member_perms": "0",
            "channel_hidden": False,
            "invite_code": str(invite_code),
            "invite_guild_id": str(guild_id),
            "invite_channel_id": str(channel_id),
            "invite_instance_id": f"{message_id}:{invite_code}",
            "invite_channel_type": 0,
            "embed_type": "guild_invite_v2",
            "location_stack": ["invite embed"],
            "location": "impression_guild_channel",
            "location_page": "impression_guild_channel",
            "location_section": "impression_invite_embed",
        }
        self.track("impression_invite_embed", props)

    def track_app_startup(self, is_fast_connect=False):
        """Emits application startup telemetry sequence."""
        self.track("app_opened", {
            "is_fast_connect": is_fast_connect,
            "client_launch_id": self.profile.get("client_launch_id", str(uuid.uuid4())),
        })
        self.track("session_start_client", {
            "is_fast_connect": is_fast_connect,
        })
        self.track("app_ui_viewed", {
            "tab": "friends",
            "section": "all",
        })

    def track_invite_opened(self, invite_code, load_time=None, location="Accept Invite Page"):
        """Emits invite_opened event matching web landing/modal schema."""
        props = {
            "invite_code": str(invite_code),
            "location": location,
        }
        if load_time is not None:
            props["load_time"] = int(load_time)
        self.track("invite_opened", props)

    def track_invite_viewed(self, invite_code, location="Accept Invite Page"):
        """Emits invite_viewed telemetry."""
        self.track("invite_viewed", {
            "invite_code": str(invite_code),
            "location": location,
        })

    def track_invite_sequence_start(self, invite_code, metadata=None, location="Accept Invite Page"):
        """Emits authentic invite page pre-join telemetry sequence."""
        load_time = random.randint(1200, 2400)
        self.track_invite_opened(invite_code, load_time=load_time, location=location)
        self.track_invite_viewed(invite_code, location=location)

    def track_invite_resolved_full(self, invite_code, metadata=None, location="Accept Invite Page"):
        """Emits network_action_invite_resolve and resolve_invite matching live captures."""
        guild = (metadata or {}).get("guild", {})
        channel = (metadata or {}).get("channel", {})
        inviter = (metadata or {}).get("inviter", {})
        size_total = (metadata or {}).get("approximate_member_count", 1000)
        size_online = (metadata or {}).get("approximate_presence_count", 250)
        
        self.track_network_action_invite_resolve(
            code=invite_code,
            guild_id=guild.get("id"),
            channel_id=channel.get("id"),
            inviter_id=inviter.get("id"),
            size_total=size_total,
            size_online=size_online,
            location=location,
        )
        self.track_resolve_invite(
            code=invite_code,
            guild_id=guild.get("id"),
            channel_id=channel.get("id"),
            inviter_id=inviter.get("id"),
            size_total=size_total,
            size_online=size_online,
            location=location,
        )

    def track_invite_actioned(self, invite_code, guild_id=None, location="Accept Invite Page"):
        """Emits invite accept CTA and action triggers."""
        self.track("invite_cta_clicked", {
            "action": "accept_invite",
            "invite_code": str(invite_code),
            "guild_id": str(guild_id) if guild_id else None,
        })
        self.track("invite_embed_actioned", {
            "action": "accept",
            "invite_code": str(invite_code),
            "guild_id": str(guild_id) if guild_id else None,
        })

    def track_guild_joined(self, invite_code, guild_id, channel_id=None, location="Accept Invite Page"):
        """Emits stage 6 of the invite lifecycle:
        guild_joined + initial guild_viewed
        """
        self.track("guild_joined", {
            "invite_code": str(invite_code),
            "guild_id": str(guild_id),
            "channel_id": str(channel_id) if channel_id else None,
            "location": location,
            "acquisition_source": "invite_link",
        })
        self.track("guild_viewed", {
            "guild_id": str(guild_id),
            "total_channels": 10,
            "has_unread": True,
        })

    def track_network_action_invite_resolve(self, code, guild_id=None, channel_id=None, inviter_id=None, size_total=1000, size_online=250, location="Accept Invite Page"):
        """Emits network_action_invite_resolve matching official client schema."""
        self.track("network_action_invite_resolve", {
            "status_code": 200,
            "url": f"/invites/{code}",
            "request_method": "get",
            "resolved": True,
            "guild_id": str(guild_id) if guild_id else None,
            "channel_id": str(channel_id) if channel_id else None,
            "channel_type": 0,
            "inviter_id": str(inviter_id) if inviter_id else None,
            "code": str(code),
            "authenticated": True,
            "size_total": size_total,
            "size_online": size_online,
            "invite_type": "Server Invite",
            "user_banned": False,
            "user_is_member": False,
            "location": location,
        })

    def track_resolve_invite(self, code, guild_id=None, channel_id=None, inviter_id=None, size_total=1000, size_online=250, location="Accept Invite Page"):
        """Emits resolve_invite matching official client schema."""
        self.track("resolve_invite", {
            "resolved": True,
            "guild_id": str(guild_id) if guild_id else None,
            "channel_id": str(channel_id) if channel_id else None,
            "channel_type": 0,
            "inviter_id": str(inviter_id) if inviter_id else None,
            "code": str(code),
            "authenticated": True,
            "size_total": size_total,
            "size_online": size_online,
            "destination_user_id": None,
            "invite_type": "Server Invite",
            "user_is_member": False,
            "invite_instance_id": None,
            "location": location,
        })

    def track_ready_payload_received(self, compressed_size=12000, uncompressed_size=750000, num_guilds=10):
        """Emits ready_payload_received matching official client schema."""
        self.track("ready_payload_received", {
            "compressed_byte_size": compressed_size,
            "uncompressed_byte_size": uncompressed_size,
            "compression_algorithm": "zlib-stream",
            "packing_algorithm": "json",
            "unpack_duration_ms": random.randint(15, 45),
            "identify_total_server_duration_ms": random.randint(150, 350),
            "num_guilds": num_guilds,
            "is_reconnect": False,
            "is_fast_connect": True,
            "had_cache_at_startup": True,
            "used_cache_at_startup": True,
        })

    def track_libdiscore_loaded(self):
        """Emits libdiscore_loaded telemetry event."""
        self.track("libdiscore_loaded", {
            "success": True,
            "experimental_features": [],
        })

    def track_client_ad_heartbeat(self):
        """Emits client_ad_heartbeat telemetry event matching live web capture."""
        self.track("client_ad_heartbeat")

    def pending_count(self):
        """Return the number of queued events."""
        with self._lock:
            return len(self._events)

    def _build_payload(self):
        """Build the /science POST payload from queued events matching official Discord schema."""
        with self._lock:
            if not self._events:
                return None
            events = self._events.copy()
            self._events.clear()

        now_ms = int(time.time() * 1000)
        events_payload = []
        for ev in events:
            props = dict(ev["properties"])
            # Every captured event ends with client_send_timestamp (766/766);
            # re-setting an existing key keeps its old position, so pop first.
            props.pop("client_send_timestamp", None)
            props["client_send_timestamp"] = now_ms
            events_payload.append({
                "type": ev["type"],
                "properties": props,
            })

        return {
            "token": self.analytics_token,
            "events": events_payload,
        }

    def flush(self):
        """Immediately flush all queued events to /api/v9/science."""
        if not self.session or not self.analytics_token:
            return

        payload = self._build_payload()
        if not payload:
            return

        try:
            headers = {
                "Content-Type": "application/json",
            }
            if self.profile and self.profile.get("user_agent"):
                headers["User-Agent"] = self.profile["user_agent"]

            r = self.session.post(
                f"{API}/science",
                json=payload,
                headers=headers,
            )
            if r.status_code in (200, 204):
                log.debug(
                    f"Science telemetry flushed: {len(payload['events'])} events "
                    f"(HTTP {r.status_code})"
                )
            elif r.status_code == 401:
                # Token unauthorized/locked; stop background telemetry loop for this token
                self._running = False
            else:
                log.debug(
                    f"Science telemetry flush status: HTTP {r.status_code}"
                )
            return r.status_code
        except Exception as e:
            log.debug(f"Science telemetry flush error: {e}")
            return None

    def _flush_loop(self):
        """Background thread that periodically flushes accumulated events with crash resilience."""
        while self._running and not self._stop_event.is_set():
            try:
                interval = random.uniform(self.FLUSH_INTERVAL_MIN, self.FLUSH_INTERVAL_MAX)
                if self._stop_event.wait(timeout=interval):
                    break
                if self._running:
                    # Add natural app focus state micro-jitter
                    if random.random() < 0.2:
                        self._app_state = random.choice(["focused", "focused", "unfocused"])
                    if self.pending_count() > 0:
                        self.flush()
            except Exception as e:
                log.debug(f"Telemetry flush loop handled error: {e}")
                time.sleep(2)

''',
    'utils.version': r'''__version__ = "1.08"''',
}

_DASHBOARD_HTML = r'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Join Dashboard</title>
<style>
body{margin:0;background:#101417;color:#edf2ef;font:16px system-ui;max-width:1100px;padding:32px;margin:auto}
h1{margin-top:0}main{display:grid;grid-template-columns:1fr 1fr;gap:16px}section{background:#1b2324;border:1px solid #374344;padding:18px}
textarea{width:100%;min-height:190px;box-sizing:border-box;background:#101417;color:#edf2ef;border:1px solid #52605f;padding:12px;font:14px monospace}
button{margin-top:16px;padding:10px 18px;background:#71d6a1;border:0;font-weight:700;cursor:pointer}
#logs{height:280px;overflow:auto;white-space:pre-wrap;background:#0b0e10;border:1px solid #374344;padding:12px;font:12px/1.5 Consolas,monospace;color:#b9c5c1}
.metrics{display:grid;grid-template-columns:repeat(5,1fr);gap:10px;margin:20px 0}.metric{background:#1b2324;border:1px solid #374344;padding:14px}.metric b{display:block;font-size:26px;color:#71d6a1}.metric span{color:#9da7a5;font-size:12px}
.meta{color:#9da7a5;font-size:13px}.ok{color:#71d6a1}.error{color:#ee827b}@media(max-width:700px){main{grid-template-columns:1fr}}
@media(max-width:700px){.metrics{grid-template-columns:repeat(2,1fr)}}
</style>
</head>
<body>
<h1>Join Dashboard</h1>
<p class="meta">Enter one value per line. Runtime logs update automatically below.</p>
<div class="metrics">
<div class="metric"><b id="joined-count">0</b><span>Successfully joined</span></div>
<div class="metric"><b id="failed-count">0</b><span>Failed / invalid</span></div>
<div class="metric"><b id="invalid-count">0</b><span>Invalid tokens</span></div>
<div class="metric"><b id="total-count">0</b><span>Total tokens</span></div>
<div class="metric"><b id="captcha-count">0</b><span>Captcha solved</span></div>
</div>
<form id="form">
<main>
<section><h2>Tokens</h2><textarea id="tokens" placeholder="one token per line"></textarea></section>
<section><h2>Invites</h2><textarea id="invites" placeholder="one invite code or URL per line"></textarea></section>
<section style="grid-column:1/-1"><h2>Live logs <span id="log-count" class="meta"></span></h2><div id="logs">Waiting for logs...</div></section>
</main>
<button>Update queues</button> <span id="message" class="meta"></span>
</form>
<script>
const $=id=>document.getElementById(id);
async function refreshStats(){try{const [statsResponse,dataResponse]=await Promise.all([fetch('/api/stats',{cache:'no-store'}),fetch('/api/data',{cache:'no-store'})]);const stats=await statsResponse.json();const data=await dataResponse.json();$('joined-count').textContent=stats.unlocked||0;$('failed-count').textContent=stats.invalid||0;$('invalid-count').textContent=stats.invalid||0;$('total-count').textContent=stats.total_tokens||0;$('captcha-count').textContent=stats.captcha_solves||0;}catch(e){}}
async function refreshLogs(){try{const r=await fetch('/api/logs',{cache:'no-store'});const d=await r.json();const logs=d.logs||[];$('logs').textContent=logs.join('\n');$('log-count').textContent=logs.length+' entries';$('logs').scrollTop=$('logs').scrollHeight;}catch(e){$('logs').textContent='Unable to read logs.';}}
form.onsubmit=async e=>{e.preventDefault();let r=await fetch('/api/inputs',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({tokens:tokens.value,invites:invites.value})});let d=await r.json();message.textContent=d.ok?'Queues updated':'Update failed';message.className=d.ok?'ok':'error';refreshLogs();};
refreshStats();refreshLogs();setInterval(refreshStats,1500);setInterval(refreshLogs,1500);
</script>
</body>
</html>'''

_NOPECHA_CLASS_SOURCE = '''
class DisabledChallengeClient:
    def __init__(self, *args, **kwargs):
        self._solver_type = args[0] if len(args) > 0 else None
        self._website_url = args[1] if len(args) > 1 else "https://discord.com/"
        self._api_key = args[2] if len(args) > 2 else None
        self._extra_proxy = args[3] if len(args) > 3 else None

    def solve(self, *args, **kwargs):
        try:
            import nopecha
        except ImportError:
            log.warning("nopecha library not installed - pip install nopecha")
            return None
        api_key = self._api_key or kwargs.get("api_key")
        if not api_key:
            log.warning("No NopeCHA API key configured")
            return None
        sitekey = kwargs.get("sitekey")
        rqdata = kwargs.get("rqdata") or None
        user_agent = kwargs.get("user_agent")
        proxy = kwargs.get("proxy") or self._extra_proxy
        url = self._website_url or "https://discord.com/"
        if not sitekey:
            log.warning("NopeCHA: missing sitekey")
            return None
        try:
            nopecha.api_key = api_key
            params = {
                "type": "hcaptcha",
                "sitekey": sitekey,
                "url": url,
            }
            if rqdata:
                params["data"] = rqdata
            if user_agent:
                params["useragent"] = user_agent
            if proxy:
                params["proxy"] = proxy
            result = nopecha.Token.solve(**params)
            if isinstance(result, str) and result:
                return result
            log.warning(f"NopeCHA returned unexpected result: {type(result).__name__}")
            return None
        except Exception as exc:
            log.warning(f"NopeCHA solve failed: {type(exc).__name__}: {exc}")
            return None
'''

_ORIGINAL_DISABLED_CLIENT = (
    "class DisabledChallengeClient:\n"
    "    def __init__(self, *args, **kwargs):\n"
    "        pass\n\n"
    "    def solve(self, *args, **kwargs):\n"
    "        return None"
)

class _BundledLoader(importlib.abc.Loader):
    def create_module(self, spec):
        return None

    def exec_module(self, module):
        module.__file__ = ""
        source = _BUNDLED_MODULES[module.__name__]

        if module.__name__ == "utils.account":
            if _ORIGINAL_DISABLED_CLIENT in source:
                source = source.replace(_ORIGINAL_DISABLED_CLIENT, _NOPECHA_CLASS_SOURCE)
            source = source.replace(
                "                _clear_captcha_headers(session)\n"
                "                log.warning(\n"
                "                    f\"Captcha solving failed or secondary captcha required for token {format_token_id(token)} on invite {invite_code}. \"\n"
                "                    f\"Skipping this token... (reason codes logged to log/captcha_debug.log)\"\n"
                "                )",
                "                _clear_captcha_headers(session)\n"
                "                log.warning(\n"
                "                    f\"Captcha solving failed for token {format_token_id(token)} on invite {invite_code}. \"\n"
                "                    f\"Requeueing invite for another token.\"\n"
                "                )",
            )

        if module.__name__ == "utils.build":
            source = source.replace("\nsync_hardware_database()\n", "\n")

        if module.__name__ == "utils.dashboard":
            source = source.replace(
                'host = str(load_config().get("dashboard_host", "127.0.0.1")).strip() or "127.0.0.1"',
                'host = "0.0.0.0" if os.environ.get("PORT") else str(load_config().get("dashboard_host", "127.0.0.1")).strip() or "127.0.0.1"',
            )

        exec(source, module.__dict__)

        if module.__name__ == "utils.dashboard":
            module.HTML_CONTENT = _DASHBOARD_HTML

class _BundledFinder(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname in _BUNDLED_MODULES:
            return importlib.util.spec_from_loader(fullname, _BundledLoader())
        return None

if 'utils' not in sys.modules:
    package = types.ModuleType('utils')
    package.__path__ = []
    sys.modules['utils'] = package

sys.meta_path.insert(0, _BundledFinder())

import asyncio, sys, random, time, threading, os, string, requests, json, signal
from pathlib import Path
from colorama import Fore, Style

from utils.account import (
    join_server as _real_join_server,
    load_guilds_db,
    close_all_gateways,
    mark_token_invalid_attempt,
    clear_token_invalid_attempts,
    INVALID_RETIRE_THRESHOLD,
)
from utils.dashboard import (
    start_dashboard,
    init_token_core_workers,
    set_worker_state,
    push_token_core_log,
    update_token_core_telemetry,
)

def _sanitize_join_status(status):
    if status is None:
        return None
    normalized = str(status).strip()
    key = normalized.lower().replace("_", " ").replace("-", " ")
    if "captcha retired" in key or key == "captcha_retired":
        return "failed"
    return status

def join_server(*args, **kwargs):
    status = _real_join_server(*args, **kwargs)
    return _sanitize_join_status(status)

from utils.discord_bot import start_bot
from utils.core import (
    update_title,
    load_config,
    setup_logger,
    show_banner,
    system,
    STATS,
    get_cpm,
    write_text_atomic
)
from utils.proxy import ProxyManager
from utils.version import __version__

log = setup_logger(__name__)

CURRENT_VERSION = __version__

file_lock = asyncio.Lock()

def title_loop():
    while True:
        update_title()
        time.sleep(0.5)

config = load_config()

SOLVER_TYPE = None
SOLVER_API_KEY = None
gen_count = 0

system(cmd="clear")

SOLVERS = {
    "nopecha": {"name": "nopecha", "key": "nopecha_api_key"},
    "anysolver": {"name": "anysolver", "key": "anysolver_api_key"},
    "custom": {"name": "custom", "key": "custom_api_key"},
    "bitsolver": {"name": "bitsolver", "key": "bitsolver_api_key"},
}

def parse_invite(invite: str) -> str:
    invite = invite.strip()
    if "/" in invite:
        invite = invite.split("/")[-1]
    return invite

def check_structure():
    required_folders = ["input", "output"]

    default_config = """{
  "verification": {
    "enabled": false
  },
  "solver": {
    "enabled": true,
    "provider": "nopecha",
    "nopecha": {
      "api_key": "",
      "base_url": ""
    },
    "api_key": ""
  },
  "join_engine_mode": "fleet",
  "token_join_limit": 12,
  "min_dispatcher_delay": 22,
  "max_dispatcher_delay": 38,
  "captcha_timeout": 180,
  "max_captcha_rounds": 6,
  "threads": 2,
  "max_guild_limit": 40,
  "min_member_count": 50,
  "min_join_delay": 220,
  "max_join_delay": 320,
  "min_warmup_delay": 30,
  "max_warmup_delay": 75,
  "min_batch_joins": 15,
  "max_batch_joins": 25,
  "min_batch_delay": 180,
  "max_batch_delay": 260,
  "min_token_join_gap": 180,
  "max_token_join_gap": 280,
  "join_method": "normal",
  "browser_headless": false,
  "browser_timeout": 90,
  "browser_extension": "captchasonic",
  "dashboard_port": 5050,
  "dashboard_host": "127.0.0.1",
  "early_guild_check": true,
  "proxy_method": "random",
  "skip_proxy_health_check": false,
  "debug": false,
  "dashboard_password": "",
  "bot_token": "",
  "bot_stats_channel_id": "",
  "bot_stats_message_id": "",
  "max_captcha_solves": "all",
  "min_captcha_before_skip": 25,
  "max_captcha_before_skip": 40,
  "remove_captcha_invites": false,
  "admin_user_ids": [],
  "license_key": "",
  "workers_per_thread": 12,
  "token_failure_threshold": 5,
  "token_failure_cooldown_seconds": 3600,
  "max_invite_attempts": 4,
  "request_timeout": 30,
  "send_guild_member_ranges": false
}"""

    required_files = {
        "input/tokens.txt": "",
        "input/invites.txt": "",
        "input/proxies.txt": "",
        "output/joined.txt": "",
        "output/locked.txt": "",
        "output/invalid.txt": "",
        "output/failed_invites.txt": "",
        "output/captchaed.txt": "",
        "input/config.json": default_config,
    }

    for folder in required_folders:
        if not os.path.exists(folder):
            os.makedirs(folder, exist_ok=True)

    for file_path, default_content in required_files.items():
        if not os.path.exists(file_path):
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(default_content)

check_structure()

def select_solver():
    solver_cfg = config.get("solver", {})
    if not solver_cfg.get("enabled", True):
        log.info(f"Solver Engine {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Disabled by config")
        return None, None

    provider = str(solver_cfg.get("provider", "nopecha")).lower().strip()
    if provider != "nopecha":
        log.warning(f"Solver Engine {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Unsupported provider '{provider}', disabling")
        return None, None

    nopecha_cfg = solver_cfg.get("nopecha", {}) or {}
    api_key = (
        nopecha_cfg.get("api_key")
        or solver_cfg.get("api_key")
        or config.get("nopecha_api_key")
        or ""
    ).strip()

    if not api_key:
        log.warning(f"Solver Engine {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} NopeCHA enabled but no API key set - captchas will fail")
        return None, None

    try:
        import nopecha
        try:
            nopecha.api_key = api_key
        except Exception:
            pass
        log.info(f"Solver Engine {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} {Fore.GREEN}NopeCHA enabled{Style.RESET_ALL}")
        return "nopecha", api_key
    except ImportError:
        log.error(f"Solver Engine {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} nopecha package not installed. Run: pip install nopecha")
        return None, None

def captcha_skip_disabled(status):
    return status

def normalize_join_status(status):
    known_statuses = {
        "Already Member", "invalid_invite", "min_members_limit", "Joined",
        "Joined_Captcha_Exhausted", "failed", "invalid", "locked", "limited",
        "quarantined", "action_blocked", "captcha_retry", "captcha_skip",
        "Captcha Timeout", "captcha_retired", "captcha_retired_final",
        "retry", "backing_off",
    }
    if status not in known_statuses:
        return "failed"
    return status

async def remove_invite_from_file(invite_code: str):
    async with file_lock:
        invites_file = Path("input/invites.txt")
        if not invites_file.exists():
            return
        try:
            lines = invites_file.read_text(encoding="utf-8").splitlines()
            new_lines = []
            removed = False
            for line in lines:
                parsed = parse_invite(line)
                if parsed == invite_code and not removed:
                    removed = True
                    continue
                new_lines.append(line)
            write_text_atomic(invites_file, "\n".join(new_lines) + ("\n" if new_lines else ""))
        except Exception as e:
            log.error(f"Failed to remove invite {invite_code} from file: {e}")

async def remove_token_from_file(token_str: str):
    async with file_lock:
        tokens_file = Path("input/tokens.txt")
        if not tokens_file.exists():
            return
        try:
            lines = tokens_file.read_text(encoding="utf-8").splitlines()
            new_lines = []
            removed = False
            for line in lines:
                token_val = line.split(":")[-1].strip() if ":" in line else line.strip()
                if token_val == token_str and not removed:
                    removed = True
                    continue
                new_lines.append(line)
            write_text_atomic(tokens_file, "\n".join(new_lines) + ("\n" if new_lines else ""))
            log.info(f"Removed token {token_str[:4]}...{token_str[-4:]} from input/tokens.txt")
        except Exception as e:
            log.error(f"Failed to remove token from input/tokens.txt: {e}")

async def requeue_or_drop_invite(invites, attempts, worker, invite, status, max_attempts, lock=None):
    attempts[invite] = attempts.get(invite, 0) + 1
    if attempts[invite] >= max_attempts:
        log.warning(
            f"T{worker.id} Invite {Fore.YELLOW}{invite}{Style.RESET_ALL} failed "
            f"{attempts[invite]}x (last status={status}). Dropping it."
        )
        try:
            push_token_core_log(
                f"T{worker.id}: Invite {invite} failed {attempts[invite]}x - dropped", "error"
            )
        except Exception:
            pass
        try:
            os.makedirs("output", exist_ok=True)
            with open("output/failed_invites.txt", "a", encoding="utf-8") as f:
                f.write(f"{invite}\n")
        except Exception as e:
            log.warning(f"Could not record failed invite {invite}: {e}")
        await remove_invite_from_file(invite)
        return
    if lock is not None:
        async with lock:
            invites.append(invite)
    else:
        invites.append(invite)
    worker.proxy = None
    worker.proxy_token = None

async def move_token_to_captchaed(token_str: str):
    await move_token_to_file(token_str, "output/captchaed.txt")

async def move_token_to_quarantined(token_str: str):
    await move_token_to_file(token_str, "output/quarantined.txt")

async def move_token_to_file(token_str: str, dest: str):
    async with file_lock:
        try:
            os.makedirs("output", exist_ok=True)
            tokens_file = Path("input/tokens.txt")
            matched = token_str
            kept, removed = [], False
            if tokens_file.exists():
                lines = tokens_file.read_text(encoding="utf-8").splitlines()
                for line in lines:
                    val = line.split(":")[-1].strip() if ":" in line else line.strip()
                    if val == token_str and not removed:
                        matched = line
                        removed = True
                        continue
                    kept.append(line)
            with open(dest, "a", encoding="utf-8") as f:
                f.write(f"{matched}\n")
            if removed:
                write_text_atomic(tokens_file, "\n".join(kept) + ("\n" if kept else ""))
            log.info(f"Token {token_str[:4]}...{token_str[-4:]} moved to {dest}")
        except Exception as e:
            log.error(f"Failed to move token to {dest}: {e}")

async def move_token_to_end_of_file(token_str: str):
    async with file_lock:
        tokens_file = Path("input/tokens.txt")
        if not tokens_file.exists():
            return
        try:
            lines = tokens_file.read_text(encoding="utf-8").splitlines()
            matched_line = None
            remaining_lines = []
            for line in lines:
                token_val = line.split(":")[-1].strip() if ":" in line else line.strip()
                if token_val == token_str and matched_line is None:
                    matched_line = line
                    continue
                remaining_lines.append(line)
            if matched_line:
                remaining_lines.append(matched_line)
                write_text_atomic(tokens_file, "\n".join(remaining_lines) + ("\n" if remaining_lines else ""))
                log.info(f"Moved token {token_str[:4]}...{token_str[-4:]} to bottom of input/tokens.txt")
        except Exception as e:
            log.error(f"Failed to move token to end of input/tokens.txt: {e}")

def go_offline_safe(token):
    """Close a token's gateway/session so the next attempt starts from a fresh IDENTIFY.

    Wrapper around utils.account.go_offline that never raises — a failed
    teardown must not take down the dispatcher thread.
    """
    try:
        from utils.account import go_offline
        go_offline(token)
    except Exception:
        pass


async def main():
    global SOLVER_TYPE, SOLVER_API_KEY, gen_count

    dashboard_port = int(os.environ.get("PORT", config.get("dashboard_port", 5050)))
    try:
        start_dashboard(dashboard_port)
    except Exception as e:
        log.warning(f"Could not start dashboard: {e}")

    shutdown_requested = False
    scheduler_task = None

    def handle_shutdown(sig, frame):
        nonlocal shutdown_requested
        if shutdown_requested:
            log.warning("Force exiting immediately...")
            os._exit(1)
        log.warning("Ctrl+C / termination signal received! Initiating graceful shutdown...")
        log.info("Finishing active tasks, no new tasks will be scheduled. Press Ctrl+C again to force exit.")
        shutdown_requested = True
        if scheduler_task and not scheduler_task.done():
            scheduler_task.cancel()

    signal.signal(signal.SIGINT, handle_shutdown)
    signal.signal(signal.SIGTERM, handle_shutdown)

    try:
        start_bot()
    except Exception as e:
        log.warning(f"Could not start Discord bot: {e}")

    proxy_manager = ProxyManager()

    SOLVER_TYPE, SOLVER_API_KEY = select_solver()

    try:
        from utils.account import seed_output_file_caches
        seed_output_file_caches()
    except Exception:
        pass

    invites_file = Path("input/invites.txt")
    tokens_file = Path("input/tokens.txt")
    invites = []
    tokens = []
    last_input_notice = 0.0
    while not invites or not tokens:
        invites = [
            parse_invite(line)
            for line in invites_file.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ] if invites_file.exists() else []
        tokens = [
            line.strip()
            for line in tokens_file.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ] if tokens_file.exists() else []

        if not invites:
            fallback_invite = config.get("invite", {}).get("invite", "")
            if fallback_invite:
                invites = [parse_invite(fallback_invite)]
        if invites and tokens:
            break
        if time.time() - last_input_notice >= 10:
            log.info("Waiting for tokens and invites from the dashboard on port %s", dashboard_port)
            last_input_notice = time.time()
        await asyncio.sleep(1)

    raw_lines = tokens
    tokens = []
    for line in raw_lines:
        if ":" in line:
            parts = line.split(":")
            tokens.append(parts[-1].strip())
        else:
            tokens.append(line)
    before = len(tokens)
    tokens = list(dict.fromkeys(tokens))
    if len(tokens) != before:
        log.warning(f"Dropped {before - len(tokens)} duplicate token line(s) from input/tokens.txt")

    max_guild_limit = int(config.get("max_guild_limit", 40) or 40)
    guilds_db = load_guilds_db()

    invites_to_process = list(invites)
    active_tokens = list(tokens)
    STATS["total_tokens"] = len(tokens)
    STATS["active_tokens"] = len(active_tokens)
    STATS["tokens_in_use"] = 0
    STATS["total_invites"] = len(invites)
    STATS["max_guild_limit"] = max_guild_limit
    token_last_use_time = {}
    token_failure_counts = {}
    token_failure_cooldown = {}
    invalid_token_ids = set()
    current_token_index = 0
    token_proxies = {}

    token_lock = asyncio.Lock()
    invite_lock = asyncio.Lock()

    tokens_in_use = set()
    invites_in_use = set()

    NUM_THREADS = int(config.get("threads", 2))
    solver_name = SOLVER_TYPE if SOLVER_TYPE else "disabled"
    log.info(
        f"Engine Ready {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} "
        f"Threads: {Fore.CYAN}{NUM_THREADS}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
        f"Tokens: {Fore.CYAN}{len(tokens)}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
        f"Invites: {Fore.YELLOW}{len(invites)}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
        f"Solver: {Fore.GREEN}{solver_name}{Style.RESET_ALL}"
    )

    threading.Thread(target=title_loop, daemon=True).start()

    exhausted_tokens = set()

    async def worker_loop(thread_id: int):
        nonlocal current_token_index
        global gen_count
        min_batch = int(config.get("min_batch_joins", 15))
        max_batch = int(config.get("max_batch_joins", 25))
        if min_batch > max_batch:
            min_batch, max_batch = max_batch, min_batch
        joins_in_batch = 0
        batch_target = random.randint(min_batch, max_batch)

        while True:
            if shutdown_requested:
                break

            invite = None
            async with invite_lock:
                if not invites_to_process:
                    break
                for inv in list(invites_to_process):
                    if inv not in invites_in_use:
                        invite = inv
                        invites_in_use.add(inv)
                        invites_to_process.remove(inv)
                        break

            if not invite:
                await asyncio.sleep(1.0)
                async with invite_lock:
                    if not invites_to_process and not invites_in_use:
                        break
                continue

            token = None
            while True:
                if shutdown_requested:
                    break
                async with token_lock:
                    current_time = time.time()
                    join_method = config.get("join_method", "normal")

                    if join_method == "cycle" and active_tokens:
                        if current_token_index >= len(active_tokens):
                            current_token_index = 0

                        found_token = None
                        for i in range(len(active_tokens)):
                            idx = (current_token_index + i) % len(active_tokens)
                            t = active_tokens[idx]
                            if t in exhausted_tokens:
                                continue
                            if t in tokens_in_use:
                                continue
                            cooldown_until = token_failure_cooldown.get(t, 0)
                            if cooldown_until and current_time < cooldown_until:
                                continue
                            if current_time - token_last_use_time.get(t, 0) < 180.0:
                                continue
                            joins = len(guilds_db.get(t, []))
                            if joins < max_guild_limit:
                                found_token = t
                                current_token_index = (idx + 1) % len(active_tokens)
                                break

                        if found_token:
                            token = found_token
                            tokens_in_use.add(token)
                            STATS["tokens_in_use"] = len(tokens_in_use)
                            if token not in guilds_db:
                                guilds_db[token] = []
                            guilds_db[token].append("placeholder_guild_id")
                    else:
                        for t in active_tokens:
                            if t in exhausted_tokens or t in tokens_in_use:
                                continue
                            cooldown_until = token_failure_cooldown.get(t, 0)
                            if cooldown_until and time.time() < cooldown_until:
                                continue
                            joins = len(guilds_db.get(t, []))
                            if joins >= max_guild_limit:
                                exhausted_tokens.add(t)
                                continue
                            token = t
                            tokens_in_use.add(t)
                            STATS["tokens_in_use"] = len(tokens_in_use)
                            if t not in guilds_db:
                                guilds_db[t] = []
                            guilds_db[t].append("placeholder_guild_id")
                            break
                if token:
                    break

                async with token_lock:
                    any_slots_left = any(len(guilds_db.get(t, [])) < max_guild_limit for t in active_tokens if t not in exhausted_tokens)
                    if not any_slots_left:
                        break

                await asyncio.sleep(0.5)

            if not token:
                async with invite_lock:
                    invites_to_process.append(invite)
                    invites_in_use.discard(invite)
                break

            try:
                async with token_lock:
                    if token not in token_proxies:
                        token_proxies[token] = await asyncio.to_thread(
                            proxy_manager.get_proxy_for_token, token
                        )
                    proxy = token_proxies[token]
                max_guild_limit_val = int(config.get("max_guild_limit", 40) or 40)
                min_member_count = int(config.get("min_member_count", 0) or 0)

                current_num = thread_id

                try:
                    status = await asyncio.to_thread(
                        join_server,
                        token,
                        invite,
                        proxy,
                        current_num,
                        SOLVER_TYPE,
                        SOLVER_API_KEY,
                        3,
                        max_guild_limit_val,
                        min_member_count,
                    )
                except asyncio.CancelledError:
                    raise
                except Exception as e:
                    log.error(f"join_server crashed for invite={invite}: {e}", exc_info=True)
                    status = "failed"

                status = normalize_join_status(status)

                if status in ("Joined", "Joined_Captcha_Exhausted"):
                    await remove_invite_from_file(invite)
                    joins_in_batch += 1

                    if joins_in_batch >= batch_target:
                        min_batch_pause = int(config.get("min_batch_delay", 180))
                        max_batch_pause = int(config.get("max_batch_delay", 260))
                        if min_batch_pause > max_batch_pause:
                            min_batch_pause, max_batch_pause = max_batch_pause, min_batch_pause
                        delay_secs = random.randint(min_batch_pause, max_batch_pause)
                        log.info(
                            f"Batch complete ({joins_in_batch} joins) {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} "
                            f"Pausing thread for {delay_secs / 60:.1f}m..."
                        )
                        await asyncio.sleep(delay_secs)
                        joins_in_batch = 0
                        batch_target = random.randint(min_batch, max_batch)
                        log.info(f"Cooldown finished {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Resuming joins.")

                elif status == "Already Member":
                    await remove_invite_from_file(invite)
                    async with token_lock:
                        if token in guilds_db and guilds_db[token]:
                            guilds_db[token].pop()
                elif status in ("invalid_invite", "min_members_limit"):
                    await remove_invite_from_file(invite)

                if status in ("invalid", "locked", "Joined_Captcha_Exhausted", "limited"):
                    if status in ("invalid", "locked", "limited") and token not in invalid_token_ids:
                        invalid_token_ids.add(token)
                        STATS["invalid"] = int(STATS.get("invalid", 0)) + 1
                    if status == "invalid":
                        await remove_token_from_file(token)
                        async with token_lock:
                            exhausted_tokens.add(token)
                            if token in active_tokens:
                                active_tokens.remove(token)
                                STATS["active_tokens"] = len(active_tokens)
                                token_proxies.pop(token, None)
                        continue
                    failure_threshold = int(config.get("token_failure_threshold", 5) or 5)
                    failure_cooldown = float(config.get("token_failure_cooldown_seconds", 3600) or 3600)
                    token_failure_counts[token] = token_failure_counts.get(token, 0) + 1
                    token_failure_cooldown[token] = time.time() + failure_cooldown
                    if token_failure_counts[token] >= failure_threshold:
                        await remove_token_from_file(token)
                        async with token_lock:
                            exhausted_tokens.add(token)
                            if token in active_tokens:
                                active_tokens.remove(token)
                                STATS["active_tokens"] = len(active_tokens)
                                token_proxies.pop(token, None)
                                log.warning(f"Token pool updated {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} token={Fore.CYAN}{token[:4]}...{token[-4:]}{Style.RESET_ALL} status={Fore.LIGHTYELLOW_EX}{status}{Style.RESET_ALL}")
                        continue
                    else:
                        log.warning(f"Token cooldown triggered {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} token={Fore.CYAN}{token[:4]}...{token[-4:]}{Style.RESET_ALL} failures={token_failure_counts[token]}/{failure_threshold}")

                if status in ("invalid", "locked", "limited", "captcha_skip", "min_members_limit", "failed", "action_blocked", "captcha_retry", "Captcha Timeout"):
                    async with token_lock:
                        if token in guilds_db and guilds_db[token]:
                            guilds_db[token].pop()
                        if status == "action_blocked":
                            await move_token_to_end_of_file(token)
                            if token in active_tokens and len(active_tokens) > 1:
                                active_tokens.remove(token)
                                active_tokens.append(token)
                                log.info(f"Token rotated {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} token={Fore.CYAN}{token[:4]}...{token[-4:]}{Style.RESET_ALL} status=action_blocked")
                    if status in ("invalid", "locked", "limited", "captcha_skip", "action_blocked", "captcha_retry", "Captcha Timeout"):
                        async with invite_lock:
                            invites_to_process.append(invite)

            finally:
                if token:
                    async with token_lock:
                        tokens_in_use.discard(token)
                        STATS["tokens_in_use"] = len(tokens_in_use)
                        token_last_use_time[token] = time.time()
                async with invite_lock:
                    invites_in_use.discard(invite)

    class TokenCoreWorker:
        def __init__(self, worker_id: int, token: str, limit: int):
            self.id = worker_id
            self.token = token
            self.joins = 0
            self.limit = limit
            self.status = "Idle"
            self.current_invite = "\u2014"
            self.proxy = None
            self.proxy_token = None
            self.retired = False
            self.thread_id = 0
            self.next_join_ok = 0.0

    async def run_token_core_engine():
        nonlocal shutdown_requested
        workers_per_thread = max(1, int(config.get("workers_per_thread", 12)))
        proxy_pool = proxy_manager.active_pool()
        requested_threads = max(1, int(NUM_THREADS))
        thread_count = min(requested_threads, len(proxy_pool)) if proxy_pool else 1
        if proxy_pool and requested_threads > len(proxy_pool):
            log.warning(
                f"threads={requested_threads} but only {len(proxy_pool)} "
                f"{'proxy is' if len(proxy_pool) == 1 else 'proxies are'} loaded; "
                f"running {thread_count} thread(s)."
            )

        engine_workers_count = min(thread_count * workers_per_thread, len(tokens))
        if engine_workers_count <= 0:
            log.warning("No tokens available to initialize the Fleet engine.")
            return

        token_join_limit = int(config.get("token_join_limit", 12))
        min_disp_delay = float(config.get("min_dispatcher_delay", 22))
        max_disp_delay = float(config.get("max_dispatcher_delay", 38))
        if min_disp_delay > max_disp_delay:
            min_disp_delay, max_disp_delay = max_disp_delay, min_disp_delay

        _full_gap_lo = workers_per_thread * min_disp_delay
        _full_gap_hi = workers_per_thread * max_disp_delay
        min_token_gap = float(config.get("min_token_join_gap", _full_gap_lo))
        max_token_gap = float(config.get("max_token_join_gap", _full_gap_hi))
        if min_token_gap > max_token_gap:
            min_token_gap, max_token_gap = max_token_gap, min_token_gap

        min_member_count = int(config.get("min_member_count", 0) or 0)
        max_guild_limit = int(config.get("max_guild_limit", 40) or 40)

        admin_id = 0
        if config.get("admin_user_ids"):
            try:
                admin_id = int(config.get("admin_user_ids")[0])
            except Exception:
                admin_id = 0

        by_thread = {t: [] for t in range(thread_count)}
        for tok in tokens:
            by_thread[proxy_manager.thread_index_for_token(tok, thread_count)].append(tok)

        workers = []
        by_worker_thread = {}
        standby_by_thread = {}
        for t in range(thread_count):
            group = by_thread[t]
            slots = min(workers_per_thread, len(group))
            by_worker_thread[t] = []
            for k in range(slots):
                w = TokenCoreWorker(len(workers) + 1, group[k], token_join_limit)
                w.thread_id = t
                w.proxy = proxy_pool[t] if proxy_pool else None
                w.proxy_token = group[k]
                workers.append(w)
                by_worker_thread[t].append(w)
            standby_by_thread[t] = group[slots:]

        engine_workers_count = len(workers)
        standby_tokens = [tok for t in range(thread_count) for tok in standby_by_thread[t]]
        total_tokens_count = len(tokens)
        tokens_retired_count = 0

        init_token_core_workers(num_workers=engine_workers_count, limit=token_join_limit)
        for w in workers:
            set_worker_state(w.id, token=w.token, invite="\u2014", joins=0, limit=token_join_limit, status="Idle")

        update_token_core_telemetry(
            session_created=STATS.get("unlocked", 0),
            captcha_fails=STATS.get("captcha_fails", 0),
            invalid_tokens=STATS.get("invalid", 0) + STATS.get("locked", 0),
            tokens_left=len(standby_tokens),
            invites_left=len(invites_to_process),
            session_stopped=False,
            user_id=admin_id,
            total_tokens=total_tokens_count,
            tokens_retired=tokens_retired_count,
        )

        log.info(
            f"Fleet Dispatcher Ready {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} "
            f"{Fore.CYAN}{thread_count}{Style.RESET_ALL} thread(s) x "
            f"{Fore.CYAN}{workers_per_thread}{Style.RESET_ALL} workers = "
            f"{Fore.CYAN}{len(workers)}{Style.RESET_ALL} active {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
            f"Limit/Token: {Fore.YELLOW}{token_join_limit}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
            f"Standby: {Fore.CYAN}{len(standby_tokens)}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
            f"Pacing: {Fore.GREEN}{min_disp_delay:.0f}-{max_disp_delay:.0f}s{Style.RESET_ALL}"
        )

        invite_attempts = {}
        MAX_INVITE_ATTEMPTS = int(config.get("max_invite_attempts", 4))

        async def run_thread(thread_id, workers, standby_by_thread):
            nonlocal tokens_retired_count
            standby_tokens = standby_by_thread[thread_id]
            current_idx = 0
            while not shutdown_requested and invites_to_process:
                active_workers = [w for w in workers if not w.retired]
                if not active_workers:
                    log.warning("All Fleet workers have retired and standby token pool is exhausted.")
                    break

                now = time.time()
                ready = [w for w in active_workers if w.next_join_ok <= now]
                if not ready:
                    wake = min(w.next_join_ok for w in active_workers)
                    nap = max(1.0, min(wake - now, 300.0))
                    try:
                        await asyncio.sleep(nap)
                    except asyncio.CancelledError:
                        break
                    continue

                worker = workers[current_idx % len(workers)]
                current_idx += 1

                if worker.retired or worker.next_join_ok > time.time():
                    continue

                if not worker.proxy or worker.proxy_token != worker.token:
                    fresh = proxy_manager.active_pool()
                    worker.proxy = (fresh[worker.thread_id]
                                    if worker.thread_id < len(fresh)
                                    else (proxy_pool[worker.thread_id] if proxy_pool else None))
                    worker.proxy_token = worker.token

                turn_completed = False
                while not shutdown_requested and invites_to_process and not turn_completed:
                    async with invite_lock:
                        if not invites_to_process:
                            break
                        invite = invites_to_process.pop(0)
                    worker.current_invite = invite
                    worker.status = "Joining"
                    set_worker_state(worker.id, invite=invite, status="Joining")
                    update_token_core_telemetry(tokens_left=len(standby_tokens), invites_left=len(invites_to_process))

                    log.info(
                        f"T{worker.id} Dispatching {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} "
                        f"token={Fore.CYAN}{worker.token[:4]}...{worker.token[-4:]}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
                        f"target={Fore.YELLOW}discord.gg/{invite}{Style.RESET_ALL} {Fore.LIGHTBLACK_EX}\u2502{Style.RESET_ALL} "
                        f"joins={Fore.GREEN}{worker.joins}/{worker.limit}{Style.RESET_ALL}"
                    )

                    try:
                        status = await asyncio.to_thread(
                            join_server,
                            worker.token,
                            invite,
                            worker.proxy,
                            worker.id,
                            SOLVER_TYPE,
                            SOLVER_API_KEY,
                            3,
                            max_guild_limit,
                            min_member_count,
                        )
                    except asyncio.CancelledError:
                        raise
                    except Exception as e:
                        log.error(
                            f"T{worker.id} join_server crashed for invite={invite}: {e}",
                            exc_info=True,
                        )
                        push_token_core_log(f"T{worker.id}: join crashed ({type(e).__name__}) - invite requeued", "error")
                        status = "failed"

                    status = normalize_join_status(status)

                    if status == "Already Member":
                        push_token_core_log(f"T{worker.id}: Server already joined (discord.gg/{invite}) - next invite", "info")
                        log.info(f"T{worker.id} Server Already Joined {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} discord.gg/{invite} already joined. Trying next server...")
                        await remove_invite_from_file(invite)
                        update_token_core_telemetry(invites_left=len(invites_to_process))
                        continue

                    elif status in ("invalid_invite", "min_members_limit"):
                        push_token_core_log(f"T{worker.id}: Invite {status} (discord.gg/{invite}) - next invite", "error")
                        log.info(f"T{worker.id} Invite {status} {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Removing discord.gg/{invite} and trying next...")
                        await remove_invite_from_file(invite)
                        update_token_core_telemetry(invites_left=len(invites_to_process))
                        continue

                    elif status in ("Joined", "Joined_Captcha_Exhausted"):
                        worker.joins += 1
                        worker.status = "Joined"
                        clear_token_invalid_attempts(worker.token)
                        worker.next_join_ok = time.time() + random.uniform(min_token_gap, max_token_gap)
                        set_worker_state(worker.id, joins=worker.joins, status="Joined")
                        await remove_invite_from_file(invite)
                        push_token_core_log(f"T{worker.id}: Joined discord.gg/{invite} joins={worker.joins}", "success")
                        log.info(f"T{worker.id} Join Success {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} joins={worker.joins}/{worker.limit}")

                        if worker.joins >= worker.limit:
                            tokens_retired_count += 1
                            log.info(f"T{worker.id} Quota Reached {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Token reached join limit ({worker.joins}/{worker.limit}). Retiring.")
                            push_token_core_log(f"T{worker.id}: Token reached limit ({worker.limit} joins) - retired", "info")
                            if standby_tokens:
                                new_tok = standby_tokens.pop(0)
                                worker.token = new_tok
                                worker.joins = 0
                                worker.proxy = proxy_pool[worker.thread_id] if proxy_pool else None
                                worker.proxy_token = new_tok
                                worker.status = "Standby Active"
                                set_worker_state(worker.id, token=worker.token, joins=0, status="Standby Active")
                                push_token_core_log(f"T{worker.id}: Assigned fresh standby token {worker.token[:4]}...", "info")
                                log.info(f"T{worker.id} Token Rotated {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Standby token assigned ({len(standby_tokens)} left)")
                            else:
                                worker.retired = True
                                worker.status = "Retired"
                                set_worker_state(worker.id, status="Retired")
                        turn_completed = True

                    elif status == "captcha_retry":
                        worker.status = "captcha_retry"
                        set_worker_state(worker.id, status="captcha_retry")
                        push_token_core_log(f"T{worker.id}: Captcha retry scheduled - keeping invite", "info")
                        await requeue_or_drop_invite(invites_to_process, invite_attempts, worker,
                                                     invite, status, MAX_INVITE_ATTEMPTS,
                                                     lock=invite_lock)
                        turn_completed = True

                    elif status == "Captcha Timeout":
                        worker.status = "Captcha Timeout"
                        set_worker_state(worker.id, status="Captcha Timeout")
                        push_token_core_log(f"T{worker.id}: Captcha timeout - invite requeued", "error")
                        await requeue_or_drop_invite(invites_to_process, invite_attempts, worker,
                                                     invite, status, MAX_INVITE_ATTEMPTS,
                                                     lock=invite_lock)
                        turn_completed = True

                    elif status == "failed":
                        worker.status = "failed"
                        set_worker_state(worker.id, status="failed")
                        push_token_core_log(f"T{worker.id}: invite failed", "error")
                        await requeue_or_drop_invite(invites_to_process, invite_attempts, worker,
                                                     invite, status, MAX_INVITE_ATTEMPTS,
                                                     lock=invite_lock)
                        turn_completed = True

                    elif status in ("invalid", "locked", "limited"):
                        attempt_no = mark_token_invalid_attempt(worker.token)
                        if attempt_no < INVALID_RETIRE_THRESHOLD:
                            worker.status = f"{status} ({attempt_no}/{INVALID_RETIRE_THRESHOLD})"
                            set_worker_state(worker.id, status=worker.status)
                            push_token_core_log(
                                f"T{worker.id}: token {status} ({attempt_no}/{INVALID_RETIRE_THRESHOLD}) "
                                f"— cooling down, NOT retiring",
                                "warn",
                            )
                            async with invite_lock:
                                invites_to_process.append(invite)
                            token_failure_cooldown[worker.token] = time.time() + random.uniform(900, 1800)
                            await asyncio.to_thread(go_offline_safe, worker.token)
                            turn_completed = True
                        else:
                            clear_token_invalid_attempts(worker.token)
                            if worker.token not in invalid_token_ids:
                                invalid_token_ids.add(worker.token)
                                STATS["invalid"] = int(STATS.get("invalid", 0)) + 1
                            tokens_retired_count += 1
                            worker.status = status
                            set_worker_state(worker.id, status=status)
                            push_token_core_log(
                                f"T{worker.id}: token {status} after {INVALID_RETIRE_THRESHOLD} checks — retiring",
                                "error",
                            )
                            async with invite_lock:
                                invites_to_process.append(invite)
                            if status == "limited":
                                await move_token_to_quarantined(worker.token)
                            else:
                                await remove_token_from_file(worker.token)
                            if standby_tokens:
                                new_tok = standby_tokens.pop(0)
                                worker.token = new_tok
                                worker.joins = 0
                                worker.proxy = proxy_pool[worker.thread_id] if proxy_pool else None
                                worker.proxy_token = new_tok
                                worker.status = "Standby Active"
                                set_worker_state(worker.id, token=worker.token, joins=0, status="Standby Active")
                            else:
                                worker.retired = True
                                worker.status = "Retired"
                                set_worker_state(worker.id, status="Retired")
                            turn_completed = True

                    elif status in ("quarantined", "action_blocked"):
                        if worker.token not in invalid_token_ids:
                            invalid_token_ids.add(worker.token)
                            STATS["invalid"] = int(STATS.get("invalid", 0)) + 1
                        tokens_retired_count += 1
                        worker.status = status
                        set_worker_state(worker.id, status=status)
                        push_token_core_log(f"T{worker.id}: Token {status} - rotating from pool", "error")
                        async with invite_lock:
                            invites_to_process.append(invite)
                        await move_token_to_quarantined(worker.token)
                        if standby_tokens:
                            new_tok = standby_tokens.pop(0)
                            worker.token = new_tok
                            worker.joins = 0
                            worker.proxy = proxy_pool[worker.thread_id] if proxy_pool else None
                            worker.proxy_token = new_tok
                            worker.status = "Standby Active"
                            set_worker_state(worker.id, token=worker.token, joins=0, status="Standby Active")
                        else:
                            worker.retired = True
                            worker.status = "Retired"
                            set_worker_state(worker.id, status="Retired")
                        turn_completed = True

                    else:
                        worker.status = status
                        set_worker_state(worker.id, status=status)
                        await requeue_or_drop_invite(invites_to_process, invite_attempts, worker,
                                                     invite, status, MAX_INVITE_ATTEMPTS,
                                                     lock=invite_lock)
                        turn_completed = True

                update_token_core_telemetry(
                    session_created=STATS.get("unlocked", 0),
                    captcha_fails=STATS.get("captcha_fails", 0),
                    invalid_tokens=STATS.get("invalid", 0) + STATS.get("locked", 0),
                    tokens_left=len(standby_tokens),
                    invites_left=len(invites_to_process),
                    total_tokens=total_tokens_count,
                    tokens_retired=tokens_retired_count,
                )

                if not shutdown_requested and invites_to_process:
                    stagger = random.uniform(min_disp_delay, max_disp_delay)
                    approx_cycle = ((min_token_gap + max_token_gap) / 2.0) / 60.0
                    log.info(
                        f"Queue Pacing {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} "
                        f"Next worker in {Fore.CYAN}{stagger:.1f}s{Style.RESET_ALL} "
                        f"{Fore.LIGHTBLACK_EX}(per-token cooldown ~{approx_cycle:.1f}m){Style.RESET_ALL}"
                    )
                    try:
                        await asyncio.sleep(stagger)
                    except asyncio.CancelledError:
                        break

        thread_tasks = [
            asyncio.create_task(run_thread(t, by_worker_thread[t], standby_by_thread))
            for t in sorted(by_worker_thread)
            if by_worker_thread[t]
        ]
        if not thread_tasks:
            log.warning('No Fleet threads could be started.')
            return
        log.info(
            f"Fleet Threads {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} running {Fore.CYAN}{len(thread_tasks)}{Style.RESET_ALL} independent dispatcher(s)"
        )
        await asyncio.gather(*thread_tasks, return_exceptions=True)

    engine_mode = str(config.get("join_engine_mode", "fleet")).lower().strip()
    if engine_mode in ("fleet", "token_core"):
        log.info(f"Engine Dispatcher {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Operating in {Fore.GREEN}Fleet Mode{Style.RESET_ALL}")
        scheduler_task = asyncio.create_task(run_token_core_engine())
        try:
            await scheduler_task
        except asyncio.CancelledError:
            log.info("Fleet dispatcher stopped by shutdown request.")
        finally:
            update_token_core_telemetry(session_stopped=True)
            log.info(f"Gateway cleanup {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Closing all WebSocket connections...")
            await asyncio.to_thread(close_all_gateways)
    else:
        log.info(f"Engine Dispatcher {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Operating in {Fore.CYAN}Classic Concurrent Mode{Style.RESET_ALL}")
        worker_tasks = [asyncio.create_task(worker_loop(i + 1)) for i in range(NUM_THREADS)]
        try:
            await asyncio.gather(*worker_tasks, return_exceptions=True)
        except asyncio.CancelledError:
            log.info("Threads stopped by shutdown request.")
        finally:
            log.info(f"Gateway cleanup {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} Closing all WebSocket connections...")
            await asyncio.to_thread(close_all_gateways)

    log.info(f"Session finished {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} All server join tasks completed or tokens exhausted!")
    log.info(f"Discord Bot & Dashboard {Fore.LIGHTBLACK_EX}\u203a{Style.RESET_ALL} 24/7 online.")

    def input_signature(path):
        if not path.exists():
            return (0, 0)
        stat = path.stat()
        return (stat.st_mtime_ns, stat.st_size)

    input_signatures = {
        path: input_signature(path)
        for path in (tokens_file, invites_file)
    }
    while True:
        await asyncio.sleep(2)
        current_signatures = {
            path: input_signature(path)
            for path in (tokens_file, invites_file)
        }
        changed = any(
            current_signatures[path] != input_signatures[path]
            for path in input_signatures
        )
        if changed:
            has_tokens = tokens_file.exists() and any(
                line.strip() for line in tokens_file.read_text(encoding="utf-8").splitlines()
            )
            has_invites = invites_file.exists() and any(
                line.strip() for line in invites_file.read_text(encoding="utf-8").splitlines()
            )
            if has_tokens and has_invites:
                log.info("New dashboard queues detected; restarting the engine.")
                os.execv(sys.executable, [sys.executable] + sys.argv)
            input_signatures = current_signatures

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        pass
    except Exception:
        import traceback
        traceback.print_exc()
        try:
            input("\nAn unexpected error occurred. Press Enter to exit...")
        except Exception:
            pass
        sys.exit(1)