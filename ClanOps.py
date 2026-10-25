"""
ClanOps - free Discord bot for Clash Royale clan leaders.

Needs a .env file next to this script with:
    DISCORD_TOKEN=your discord bot token
    CR_API_KEY=your Clash Royale API key (RoyaleAPI proxy key)

IMPORTANT: this bot uses the "Server Members Intent". Enable it in the Discord Developer Portal
(Bot -> Privileged Gateway Intents -> SERVER MEMBERS INTENT) BEFORE starting, or the bot will crash on start.
The bot also needs the Manage Roles permission, and its own role must sit ABOVE your
Leader / Co-Leader / Elder / Member roles in Server Settings -> Roles.
"""
import os
import sys
import time
import asyncio
import sqlite3
import logging
from contextlib import contextmanager
from datetime import datetime, timezone, time as dtime, timedelta, date
from collections import defaultdict
from typing import Optional

import aiohttp
import discord
from discord import app_commands
from discord.ext import commands, tasks
from dotenv import load_dotenv

load_dotenv()

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("clanops")

# ---------------- SETTINGS ----------------
DISCORD_TOKEN = os.environ.get("DISCORD_TOKEN", "").strip()
CR_API_KEY = os.environ.get("CR_API_KEY", "").strip()
if not DISCORD_TOKEN or not CR_API_KEY:
    sys.exit("ClanOps cannot start: put DISCORD_TOKEN and CR_API_KEY in your .env file.")

BASE = "https://proxy.royaleapi.dev/v1"
# the database always lives next to this script, no matter where you start it from
DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "clanops.db")

IST = timezone(timedelta(hours=5, minutes=30))

COLOR_MAIN = 0x1ABC9C
COLOR_JOIN = 0x2ECC71
COLOR_LEAVE = 0xE74C3C
COLOR_PROMO = 0xF1C40F
COLOR_DEMO = 0xE67E22
COLOR_SETTINGS = 0x3498DB
COLOR_WARN = 0x95A5A6
COLOR_ALERT = 0xFF0000

ROLE_ORDER = ["leader", "coLeader", "elder", "member"]
ROLE_LABEL = {"leader": "👑 LEADER", "coLeader": "🥇 CO-LEADER", "elder": "🥈 ELDER", "member": "🔹 MEMBER"}
ROLE_ICON = {"member": "🔹", "elder": "🥈", "coLeader": "🥇", "leader": "👑"}
ROLE_TEXT = {"leader": "Leader", "coLeader": "Co-Leader", "elder": "Elder", "member": "Member"}
ROLE_MAP = {"Leader": "leader", "Co-Leader": "coLeader", "Elder": "elder", "Member": "member"}
# Discord role names the bot understands (case-insensitive) -> in-game role
DISCORD_ROLE_NAMES = {"leader": "leader", "co-leader": "coLeader", "coleader": "coLeader",
                      "co leader": "coLeader", "elder": "elder", "member": "member"}

# score weights (used by /playerreview and /playerperformance)
WEIGHTS = {"medals": 0.35, "tenure": 0.25, "donations": 0.20, "activity": 0.12, "decks": 0.08}
MIN_TENURE_DAYS = 30

# ---- verdict rules ----
ELDER_PROMOTE_SCORE = 60        # Member -> Elder (also needs MIN_TENURE_DAYS in the clan)
ELDER_DEMOTE_SCORE = 30         # Elder -> Member
COLEADER_PROMOTE_SCORE = None   # Elder -> Co-Leader. ON HOLD: set a number (e.g. 70) when you decide.
COLEADER_DEMOTE_SCORE = None    # Co-Leader -> Elder. ON HOLD: set a number (e.g. 30) when you decide.
KICK_INACTIVE_DAYS = 5          # kick candidate = not seen for this many days (everyone except the Leader)

MASS_KICK_THRESHOLD = 5
MEMBER_DISPLAY_DAYS = 90
MEMBERS_CACHE_SECONDS = 20

# ---- timing ----
POLL_SECONDS = 30               # how often the clan is checked (members + settings, one API call)
SLOW_POLL_SECONDS = 60          # used automatically if the API answers 429 (too many requests)
CLEAN_CYCLES_TO_SPEED_UP = 20   # clean checks in a row before going back to POLL_SECONDS
OFFLINE_NOTICE_SECONDS = 120    # if the bot was down longer than this, post an "offline from X to Y" notice
HISTORY_DAYS = 180              # daily stats and weekly donation history are kept this long
FLAG_REMINDER_HOURS = 24        # an open flag is repeated this often until it is resolved

HTTP: Optional[aiohttp.ClientSession] = None

# commands the owner / clan Leader can hand out with /grant
GRANTABLE = ["currentriverrace", "riverhistory", "inactive", "donations",
             "member", "seniority", "playerreview", "playerperformance"]


# ---------------- BOT ----------------
class ClanOpsBot(commands.Bot):
    def __init__(self):
        intents = discord.Intents.default()
        intents.members = True  # privileged: must also be enabled in the Developer Portal
        super().__init__(
            command_prefix=commands.when_mentioned,
            intents=intents,
            allowed_mentions=discord.AllowedMentions.none(),  # player names can never ping anyone
        )

    async def setup_hook(self):
        global HTTP
        init_db()
        HTTP = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15))
        await self.tree.sync()

    async def close(self):
        if HTTP is not None and not HTTP.closed:
            await HTTP.close()
        await super().close()


bot = ClanOpsBot()

_prev_candidates = {}     # guild_id -> events seen on the previous check (an event must appear twice in a row)
_expected_edits = {}      # (guild_id, user_id) -> time of a role change made by the bot itself
_sync_warned = set()      # avoid repeating the same role-sync warning every 30 seconds
_slow_mode = False
_clean_cycles = 0
_started = False


# ---------------- DATABASE ----------------
@contextmanager
def dbc():
    """Open a connection, commit on success, roll back on error, always close."""
    conn = sqlite3.connect(DB_PATH, timeout=30)
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def init_db():
    with dbc() as c:
        c.execute("""CREATE TABLE IF NOT EXISTS guild_config (
            guild_id INTEGER PRIMARY KEY, clan_tag TEXT, log_channel_id INTEGER, alert_channel_id INTEGER
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS members_snapshot (
            guild_id INTEGER, tag TEXT, name TEXT, role TEXT, donations INTEGER, last_seen TEXT,
            PRIMARY KEY (guild_id, tag)
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS clan_settings_snapshot (
            guild_id INTEGER PRIMARY KEY,
            description TEXT, type TEXT, required_trophies INTEGER, war_frequency TEXT
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS daily_history (
            date TEXT, guild_id INTEGER, tag TEXT, name TEXT, decks_used INTEGER, medals INTEGER,
            donations INTEGER, donations_received INTEGER, trophies INTEGER,
            PRIMARY KEY (date, guild_id, tag)
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS weekly_donations (
            week_end TEXT, guild_id INTEGER, tag TEXT, name TEXT, donated INTEGER, received INTEGER,
            PRIMARY KEY (week_end, guild_id, tag)
        )""")
        # one row per stay in the clan, so leaving and rejoining keeps the old time and the gap
        c.execute("""CREATE TABLE IF NOT EXISTS stays (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            guild_id INTEGER, tag TEXT, name TEXT, joined_at TEXT, left_at TEXT, baseline INTEGER DEFAULT 0
        )""")
        c.execute("CREATE INDEX IF NOT EXISTS idx_stays ON stays (guild_id, tag)")
        c.execute("""CREATE TABLE IF NOT EXISTS role_history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            guild_id INTEGER, tag TEXT, name TEXT,
            event TEXT, old_role TEXT, new_role TEXT, changed_at TEXT
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS links (
            guild_id INTEGER, discord_id INTEGER, tag TEXT, name TEXT, linked_at TEXT,
            PRIMARY KEY (guild_id, discord_id),
            UNIQUE (guild_id, tag)
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS grants (
            guild_id INTEGER, kind TEXT, target_id INTEGER, command TEXT,
            PRIMARY KEY (guild_id, kind, target_id, command)
        )""")
        c.execute("""CREATE TABLE IF NOT EXISTS flags (
            guild_id INTEGER, kind TEXT, discord_id INTEGER, tag TEXT, name TEXT,
            wanted_role TEXT, text TEXT, created_at TEXT, last_reminded TEXT,
            PRIMARY KEY (guild_id, kind, discord_id)
        )""")
        c.execute("CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT)")


def get_config(guild_id):
    """-> (clan_tag, log_channel_id, alert_channel_id) or None"""
    with dbc() as c:
        return c.execute("SELECT clan_tag, log_channel_id, alert_channel_id FROM guild_config "
                         "WHERE guild_id = ?", (guild_id,)).fetchone()


def get_clan_tag(guild_id):
    cfg = get_config(guild_id)
    return cfg[0] if cfg else None


def get_all_configs():
    with dbc() as c:
        return c.execute("SELECT guild_id, clan_tag, log_channel_id, alert_channel_id FROM guild_config").fetchall()


def get_link(guild_id, discord_id):
    """-> (tag, name) or None"""
    with dbc() as c:
        return c.execute("SELECT tag, name FROM links WHERE guild_id = ? AND discord_id = ?",
                         (guild_id, discord_id)).fetchone()


def get_link_by_tag(guild_id, tag):
    with dbc() as c:
        row = c.execute("SELECT discord_id FROM links WHERE guild_id = ? AND tag = ?", (guild_id, tag)).fetchone()
    return row[0] if row else None


def delete_link(guild_id, discord_id):
    with dbc() as c:
        c.execute("DELETE FROM links WHERE guild_id = ? AND discord_id = ?", (guild_id, discord_id))


def snapshot_role(guild_id, tag):
    with dbc() as c:
        row = c.execute("SELECT role FROM members_snapshot WHERE guild_id = ? AND tag = ?", (guild_id, tag)).fetchone()
    return row[0] if row else None


def snapshot_name(guild_id, tag):
    with dbc() as c:
        row = c.execute("SELECT name FROM members_snapshot WHERE guild_id = ? AND tag = ?", (guild_id, tag)).fetchone()
    return row[0] if row else None


# ---------------- FLAGS (things a human must do in the game) ----------------
def upsert_flag(guild_id, kind, discord_id, tag, name, text, wanted_role=None):
    now = datetime.now(timezone.utc).isoformat()
    with dbc() as c:
        c.execute("INSERT OR REPLACE INTO flags (guild_id, kind, discord_id, tag, name, wanted_role, text, "
                  "created_at, last_reminded) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                  (guild_id, kind, discord_id, tag, name, wanted_role, text, now, now))


def delete_flag(guild_id, kind, discord_id):
    with dbc() as c:
        c.execute("DELETE FROM flags WHERE guild_id = ? AND kind = ? AND discord_id = ?", (guild_id, kind, discord_id))


def load_flags(guild_id):
    with dbc() as c:
        rows = c.execute("SELECT kind, discord_id, tag, name, wanted_role, text, last_reminded "
                         "FROM flags WHERE guild_id = ?", (guild_id,)).fetchall()
    keys = ["kind", "discord_id", "tag", "name", "wanted_role", "text", "last_reminded"]
    return [dict(zip(keys, r)) for r in rows]


def touch_flag_reminder(guild_id, kind, discord_id):
    with dbc() as c:
        c.execute("UPDATE flags SET last_reminded = ? WHERE guild_id = ? AND kind = ? AND discord_id = ?",
                  (datetime.now(timezone.utc).isoformat(), guild_id, kind, discord_id))


FLAG_TITLE = {
    "role_change": "🔁 Change needed in Clash Royale",
    "left_server": "🚪 Left the Discord server — remove in-game",
    "left_clan": "🚪 Left the clan — remove from the server",
}


def flag_embed(f, reminder=False):
    title = ("🔔 Reminder: " if reminder else "") + FLAG_TITLE.get(f["kind"], "Action needed")
    return base_embed(title, f["text"], COLOR_ALERT if f["kind"] != "role_change" else COLOR_PROMO)


# ---------------- STAYS / TENURE ----------------
def load_stays(guild_id):
    with dbc() as c:
        rows = c.execute("SELECT tag, joined_at, left_at, baseline FROM stays WHERE guild_id = ? "
                         "ORDER BY joined_at, id", (guild_id,)).fetchall()
    by_tag = defaultdict(list)
    for tag, joined, left, baseline in rows:
        by_tag[tag].append((joined, left, baseline))
    return by_tag


def open_stay(c, guild_id, tag, name, day, baseline=0):
    """Start a stay unless this player already has one open."""
    c.execute("""INSERT INTO stays (guild_id, tag, name, joined_at, left_at, baseline)
                 SELECT ?, ?, ?, ?, NULL, ?
                 WHERE NOT EXISTS (SELECT 1 FROM stays WHERE guild_id = ? AND tag = ? AND left_at IS NULL)""",
              (guild_id, tag, name, day, baseline, guild_id, tag))


def stay_summary(stays, today):
    """stays: list of (joined, left, baseline), oldest first. today: a date (IST)."""
    if not stays:
        return {"has": False, "since": None, "current": 0, "before": 0, "gap": None, "baseline": False}
    *past, cur = stays
    cur_joined = date.fromisoformat(cur[0])
    current = (today - cur_joined).days if cur[1] is None else 0
    before = sum((date.fromisoformat(l) - date.fromisoformat(j)).days for j, l, _ in past if l)
    gap = None
    if past and past[-1][1]:
        gap = (cur_joined - date.fromisoformat(past[-1][1])).days
    return {"has": True, "since": cur[0], "current": current, "before": before, "gap": gap, "baseline": bool(cur[2])}


def fmt_days(d):
    d = max(int(d), 0)
    years, rest = divmod(d, 365)
    months, days = divmod(rest, 30)
    parts = []
    if years:
        parts.append(f"{years}y")
    if months:
        parts.append(f"{months}mo")
    if days or not parts:
        parts.append(f"{days}d")
    return " ".join(parts)


# ---------------- CLASH ROYALE API ----------------
async def api(clan_tag, path, retries=3):
    """GET a clan endpoint. Retries on 429 / 5xx / network errors. Autocomplete passes retries=0."""
    url = f"{BASE}/clans/%23{clan_tag}{path}"
    for attempt in range(retries + 1):
        try:
            async with HTTP.get(url, headers={"Authorization": f"Bearer {CR_API_KEY}"}) as r:
                if r.status in (429, 500, 502, 503, 504, 520, 521, 522, 523, 524, 525, 526, 527) and attempt < retries:
                    try:
                        wait = float(r.headers.get("Retry-After", ""))
                    except ValueError:
                        wait = 2 ** attempt
                    await asyncio.sleep(min(max(wait, 1), 10))
                    continue
                r.raise_for_status()
                return await r.json()
        except (aiohttp.ClientConnectionError, asyncio.TimeoutError):
            if attempt < retries:
                await asyncio.sleep(2 ** attempt)
                continue
            raise


_members_cache = {}


async def get_members_cached(clan_tag):
    """Short cache so autocomplete (fires on every keystroke) doesn't hammer the API."""
    hit = _members_cache.get(clan_tag)
    if hit and time.time() - hit[0] < MEMBERS_CACHE_SECONDS:
        return hit[1]
    data = await api(clan_tag, "/members", retries=0)
    _members_cache[clan_tag] = (time.time(), data["items"])
    return data["items"]


def parse_seen(s):
    return datetime.strptime(s, "%Y%m%dT%H%M%S.%fZ").replace(tzinfo=timezone.utc)


# ---------------- HELPERS ----------------
def base_embed(title, description="", color=COLOR_MAIN):
    e = discord.Embed(title=title, description=description or None, color=color)
    e.set_footer(text=f"ClanOps • {datetime.now(IST).strftime('%d %b %Y, %H:%M IST')}")
    return e


def clip(text: str, limit: int = 4000) -> str:
    """Keep text under Discord's 4096-character embed limit."""
    return text if len(text) <= limit else text[:limit - 20].rstrip() + "\n… (truncated)"


async def send_long(send_func, text, code=True):
    """Send long text in Discord-sized pieces (code blocks keep alignment; plain keeps **bold**)."""
    if code:
        text = text.replace("**", "").replace("```", "'''")
    while text:
        chunk, text = text[:1900], text[1900:]
        if text and "\n" in chunk:
            cut = chunk.rfind("\n")
            if cut > 0:
                text = chunk[cut + 1:] + text
                chunk = chunk[:cut]
        if chunk.strip():
            await send_func(f"```\n{chunk}\n```" if code else chunk)


async def send_grouped_embed(interaction, title, body, color=COLOR_MAIN, extra_field=None):
    """Grouped roster embed; overflows into plain messages if too long for one embed."""
    if extra_field:
        extra_field = (extra_field[0], clip(extra_field[1], 1024))
    if len(body) <= 4000:
        e = base_embed(title, body, color)
        if extra_field:
            e.add_field(name=extra_field[0], value=extra_field[1], inline=False)
        return await interaction.followup.send(embed=e)
    e = base_embed(title, "This result is long — sent in full below.", color)
    if extra_field:
        e.add_field(name=extra_field[0], value=extra_field[1], inline=False)
    await interaction.followup.send(embed=e)
    await send_long(lambda t: interaction.followup.send(t), body, code=False)


async def post_alert(guild_id, embed):
    """Flags go to the private alert channel; if none is set they fall back to the clan-log channel."""
    cfg = get_config(guild_id)
    if not cfg:
        return
    channel_id = cfg[2] or cfg[1]
    channel = bot.get_channel(channel_id) if channel_id else None
    if channel is None:
        return
    try:
        await channel.send(embed=embed)
    except discord.HTTPException:
        log.warning("Could not post an alert in guild %s (missing permissions?)", guild_id)


# ---------------- PERMISSIONS ----------------
def is_owner(interaction: discord.Interaction) -> bool:
    return interaction.guild is not None and interaction.user.id == interaction.guild.owner_id


def is_clan_leader(guild_id, user_id) -> bool:
    """A Discord user linked to the player who is currently the clan's Leader."""
    with dbc() as c:
        row = c.execute("SELECT 1 FROM links l JOIN members_snapshot m "
                        "ON m.guild_id = l.guild_id AND m.tag = l.tag "
                        "WHERE l.guild_id = ? AND l.discord_id = ? AND m.role = 'leader'",
                        (guild_id, user_id)).fetchone()
    return row is not None


def is_admin(interaction: discord.Interaction) -> bool:
    return is_owner(interaction) or is_clan_leader(interaction.guild.id, interaction.user.id)


def can_use(interaction: discord.Interaction, command: str) -> bool:
    if interaction.guild is None:
        return False
    if is_admin(interaction):
        return True
    role_ids = [r.id for r in getattr(interaction.user, "roles", [])]
    with dbc() as c:
        if c.execute("SELECT 1 FROM grants WHERE guild_id = ? AND kind = 'user' AND target_id = ? AND command = ?",
                     (interaction.guild.id, interaction.user.id, command)).fetchone():
            return True
        if role_ids:
            marks = ",".join("?" * len(role_ids))
            if c.execute(f"SELECT 1 FROM grants WHERE guild_id = ? AND kind = 'role' AND command = ? "
                         f"AND target_id IN ({marks})", (interaction.guild.id, command, *role_ids)).fetchone():
                return True
    return False


async def deny(interaction):
    await interaction.response.send_message(
        embed=base_embed("⛔ Not allowed",
                         "You don't have permission to use this command. Ask the server owner or the clan Leader.",
                         COLOR_WARN),
        ephemeral=True)


async def not_set_up(interaction):
    return await interaction.followup.send(embed=base_embed("⚠️ Not set up", "Run `/setup` first.", COLOR_WARN))


def norm_tag(s: str) -> str:
    return "#" + s.strip().lstrip("#").upper()


def is_player(p: dict, query: str) -> bool:
    """Match a row (needs 'tag' and 'name') against a tag or name typed/picked by the user."""
    q = query.strip()
    return p["tag"].upper() == norm_tag(q) or p["name"].lower() == q.lower()


def resolve_player(guild_id, items, query):
    """Find (tag, name) among current members, falling back to past members stored in the DB."""
    q = query.strip()
    if not q:
        return None, None
    for m in items:
        if is_player(m, q):
            return m["tag"], m["name"]
    with dbc() as c:
        row = c.execute("SELECT tag, name FROM role_history WHERE guild_id = ? "
                        "AND (tag = ? OR LOWER(name) = LOWER(?)) ORDER BY id DESC LIMIT 1",
                        (guild_id, norm_tag(q), q)).fetchone()
    return (row[0], row[1]) if row else (None, None)


def group_by_role(items, role_key="role"):
    grouped = {r: [] for r in ROLE_ORDER}
    for it in items:
        grouped.setdefault(it[role_key], []).append(it)
    return grouped


def render_grouped(grouped, line_func):
    parts = []
    for role in ROLE_ORDER:
        entries = grouped.get(role, [])
        if not entries:
            continue
        lines = [f"{i + 1}. {line_func(e)}" for i, e in enumerate(entries)]
        parts.append(f"**{ROLE_LABEL[role]}**\n" + "\n".join(lines))
    return "\n\n".join(parts) if parts else "No data."


def _rank(role):
    return {"member": 0, "elder": 1, "coLeader": 2, "leader": 3}.get(role, 0)


# ---------------- AUTOCOMPLETE ----------------
async def player_autocomplete(interaction: discord.Interaction, current: str):
    tag = get_clan_tag(interaction.guild.id) if interaction.guild else None
    if not tag:
        return []
    try:
        items = await get_members_cached(tag)
    except Exception:
        return []
    typed = current.strip()
    q = typed.lower()
    q_tag = typed.lstrip("#").upper()
    # only match tags when the person is clearly typing a tag (starts with # or 3+ characters)
    match_tags = typed.startswith("#") or len(q_tag) >= 3
    starts, contains = [], []
    for m in items:
        name_l = m["name"].lower()
        if not q or name_l.startswith(q):
            starts.append(m)
        elif q in name_l or (match_tags and q_tag in m["tag"]):
            contains.append(m)
    out = []
    for m in (starts + contains)[:25]:
        # the value is the player TAG (unique; names can change or collide)
        out.append(app_commands.Choice(name=f"{m['name']} ({m['tag']})"[:100], value=m["tag"]))
    return out


# ---------------- SCORING + VERDICTS (shared by /playerreview and /playerperformance) ----------------
async def compute_scores(guild_id, tag):
    members = await api(tag, "/members")
    race_log = await api(tag, "/riverracelog")

    medal_totals, decks_totals = defaultdict(int), defaultdict(int)
    recent_wars = race_log["items"][:4]
    for race in recent_wars:
        for st in race["standings"]:
            if st["clan"]["tag"].replace("#", "") == tag:
                for p in st["clan"]["participants"]:
                    medal_totals[p["tag"]] += p["fame"]
                    decks_totals[p["tag"]] += p["decksUsed"]
    max_decks = 16 * len(recent_wars)  # 4 decks x 4 war days per war; only count wars that exist

    stays = load_stays(guild_id)
    today = datetime.now(IST).date()
    now = datetime.now(timezone.utc)
    rows = []
    for m in members["items"]:
        t = m["tag"]
        summ = stay_summary(stays.get(t, []), today)
        rows.append({
            "tag": t, "name": m["name"], "role": m["role"],
            "medals": medal_totals.get(t, 0), "decks": decks_totals.get(t, 0),
            "donations": m["donations"], "inactivity": (now - parse_seen(m["lastSeen"])).days,
            "tenure": summ["current"], "stay": summ,
        })

    if not rows:
        return rows, max_decks

    def norm(values, value, invert=False):
        lo, hi = min(values), max(values)
        if hi == lo:
            return 100.0
        pct = (value - lo) / (hi - lo) * 100
        return 100 - pct if invert else pct

    medals_l = [r["medals"] for r in rows]
    tenures = [r["tenure"] for r in rows]
    donos = [r["donations"] for r in rows]
    inacts = [r["inactivity"] for r in rows]

    for r in rows:
        deck_score = (r["decks"] / max_decks * 100) if max_decks else 0
        r["score"] = (
            WEIGHTS["medals"] * norm(medals_l, r["medals"]) +
            WEIGHTS["tenure"] * norm(tenures, r["tenure"]) +
            WEIGHTS["donations"] * norm(donos, r["donations"]) +
            WEIGHTS["activity"] * norm(inacts, r["inactivity"], invert=True) +
            WEIGHTS["decks"] * deck_score
        )
        r["eligible"] = r["tenure"] >= MIN_TENURE_DAYS

    return rows, max_decks


VERDICT_ORDER = ["promote", "demote", "kick", "new", "stable"]
VERDICT_TITLE = {"promote": "⭐ Promote", "demote": "⚠️ Demote", "kick": "🔴 Kick candidates",
                 "new": "🆕 Not eligible yet", "stable": "✅ Stable"}


def verdict(r):
    """-> (code, short reason). Same rules for /playerreview and /playerperformance."""
    role = r["role"]
    if role == "leader":
        return "leader", "Leader — not judged"
    if r["inactivity"] >= KICK_INACTIVE_DAYS:
        return "kick", f"not seen for {r['inactivity']}d"
    if not r["eligible"]:
        return "new", f"{r['tenure']}d in clan (needs {MIN_TENURE_DAYS})"
    if role == "member":
        if r["score"] >= ELDER_PROMOTE_SCORE:
            return "promote", "Member → Elder"
        return "stable", "no change"
    if role == "elder":
        if COLEADER_PROMOTE_SCORE is not None and r["score"] >= COLEADER_PROMOTE_SCORE:
            return "promote", "Elder → Co-Leader"
        if r["score"] < ELDER_DEMOTE_SCORE:
            return "demote", "Elder → Member"
        return "stable", "no change"
    if role == "coLeader":
        if COLEADER_DEMOTE_SCORE is not None and r["score"] < COLEADER_DEMOTE_SCORE:
            return "demote", "Co-Leader → Elder"
        return "stable", "no change"
    return "stable", "no change"


# ---------------- DISCORD ROLE SYNC ----------------
def find_role(guild, game_role):
    for r in guild.roles:
        if DISCORD_ROLE_NAMES.get(r.name.strip().lower()) == game_role:
            return r
    return None


def clan_key(roles):
    """Highest in-game role represented by a list of Discord roles (or None)."""
    best = None
    for r in roles:
        k = DISCORD_ROLE_NAMES.get(r.name.strip().lower())
        if k and (best is None or _rank(k) > _rank(best)):
            best = k
    return best


def _is_dangerous(role):
    p = role.permissions
    return (p.administrator or p.manage_guild or p.manage_roles or p.manage_channels
            or p.kick_members or p.ban_members)


async def sync_member_role(guild, discord_id, game_role):
    """Make the member's Discord clan role match their in-game role. Returns a status string."""
    member = guild.get_member(discord_id)
    if member is None:
        return "not in server"
    target = find_role(guild, game_role)
    if target is None:
        return f"no Discord role named '{ROLE_TEXT[game_role]}'"
    if _is_dangerous(target):
        return f"role '{target.name}' has powerful permissions, so I won't assign it"
    clan_roles = [r for r in (find_role(guild, k) for k in ROLE_ORDER) if r]
    desired = [r for r in member.roles if r not in clan_roles and not r.is_default()] + [target]
    if {r.id for r in desired} == {r.id for r in member.roles if not r.is_default()}:
        return "ok"
    if target >= guild.me.top_role:
        return "my role must be above the clan roles in Server Settings → Roles"
    _expected_edits[(guild.id, member.id)] = time.time()
    try:
        await member.edit(roles=desired, reason="ClanOps role sync")
    except (discord.Forbidden, discord.HTTPException):
        _expected_edits.pop((guild.id, member.id), None)
        return "Discord refused the role change (check Manage Roles and the role order)"
    return "updated"


async def sync_nickname(guild, discord_id, game_name):
    """Set the member's server nickname to their in-game name. Returns a status string."""
    member = guild.get_member(discord_id)
    if member is None:
        return "not in server"
    nick = game_name[:32]
    if member.nick == nick:
        return "ok"
    if member.id == guild.owner_id:
        return "Discord doesn't let bots change the server owner's nickname"
    try:
        await member.edit(nick=nick, reason="ClanOps nickname sync")
    except (discord.Forbidden, discord.HTTPException):
        return "Discord refused (check Manage Nicknames and the role order)"
    return "updated"

async def sync_roles(guild, roles_now, names_now):
    with dbc() as c:
        links = c.execute("SELECT discord_id, tag, name FROM links WHERE guild_id = ?", (guild.id,)).fetchall()
        paused = {r[0] for r in c.execute("SELECT discord_id FROM flags WHERE guild_id = ? AND kind = 'role_change'",
                                           (guild.id,))}
    for discord_id, tag, saved_name in links:
        game_role = roles_now.get(tag)
        if game_role is None:
            continue  # not in the clan right now
        new_name = names_now.get(tag)
        if new_name and new_name != saved_name:
            with dbc() as c:
                c.execute("UPDATE links SET name = ? WHERE guild_id = ? AND discord_id = ?",
                          (new_name, guild.id, discord_id))
        statuses = []
        if discord_id not in paused:
            statuses.append(await sync_member_role(guild, discord_id, game_role))
        if new_name and discord_id != guild.owner_id:
            statuses.append(await sync_nickname(guild, discord_id, new_name))
        for status in statuses:
            if status not in ("ok", "updated", "not in server"):
                key = (guild.id, discord_id, status)
                if key not in _sync_warned:
                    _sync_warned.add(key)
                    log.warning("Sync for %s in guild %s: %s", discord_id, guild.id, status)


async def process_flags(guild, roles_now):
    """Close flags that were handled and repeat the ones still open once a day."""
    now = datetime.now(timezone.utc)
    for f in load_flags(guild.id):
        kind, did, tag = f["kind"], f["discord_id"], f["tag"]
        resolved = False
        drop_link = False
        if kind == "role_change":
            resolved = tag not in roles_now or roles_now.get(tag) == f["wanted_role"]
        elif kind == "left_server":
            resolved = tag not in roles_now
            drop_link = resolved
        elif kind == "left_clan":
            gone = guild.get_member(did) is None
            resolved = tag in roles_now or gone
            drop_link = gone
        if resolved:
            delete_flag(guild.id, kind, did)
            if drop_link:
                delete_link(guild.id, did)
            await post_alert(guild.id, base_embed("✅ Resolved", f"{f['name']}: {FLAG_TITLE.get(kind, kind)}", COLOR_JOIN))
            continue
        try:
            last = datetime.fromisoformat(f["last_reminded"])
        except (TypeError, ValueError):
            last = now
        if now - last >= timedelta(hours=FLAG_REMINDER_HOURS):
            await post_alert(guild.id, flag_embed(f, reminder=True))
            touch_flag_reminder(guild.id, kind, did)


# ---------------- BACKGROUND JOB 1: CLAN WATCHER (every POLL_SECONDS) ----------------
async def process_guild_log(guild_id, clan_tag, log_channel_id):
    # one call gives the clan settings AND the member list; fall back to /members if the list is missing
    info = await api(clan_tag, "")
    items = info.get("memberList")
    if not items:
        items = (await api(clan_tag, "/members"))["items"]
    if not items:
        return  # an empty list is an API hiccup, not "everyone left"
    today = datetime.now(IST).strftime("%Y-%m-%d")
    alerts = []
    left_confirmed = []   # (tag, name) members whose leave was confirmed on two checks in a row

    with dbc() as c:
        # --- what we saw last time ---
        old_settings = c.execute("SELECT description, type, required_trophies, war_frequency "
                                 "FROM clan_settings_snapshot WHERE guild_id = ?", (guild_id,)).fetchone()
        new_settings = (info.get("description"), info.get("type"),
                        info.get("requiredTrophies"), info.get("warFrequency"))
        old_rows = {r[0]: (r[1], r[2], r[3], r[4]) for r in c.execute(
            "SELECT tag, name, role, donations, last_seen FROM members_snapshot WHERE guild_id = ?", (guild_id,))}
        new_members = {m["tag"]: (m["name"], m["role"]) for m in items}
        first_run = not old_rows

        # --- candidate events; one only counts after it shows up on two checks in a row ---
        candidates = set()
        if old_settings and tuple(old_settings) != new_settings:
            candidates.add(("settings", new_settings))
        for tag in set(old_rows) - set(new_members):
            candidates.add(("left", tag))
        for tag, (name, role) in new_members.items():
            if tag in old_rows and old_rows[tag][1] != role:
                candidates.add(("role", tag, role))
        confirmed = candidates & _prev_candidates.get(guild_id, set())
        _prev_candidates[guild_id] = candidates

        # --- clan settings ---
        settings_to_store = new_settings
        if old_settings and tuple(old_settings) != new_settings:
            if ("settings", new_settings) in confirmed:
                labels = ["description", "type", "required trophies", "war frequency"]
                changes = [f"**{label}**: `{o}` → `{n}`" for label, o, n in zip(labels, old_settings, new_settings) if o != n]
                if changes:
                    alerts.append(base_embed("⚙️ Clan settings updated", clip("\n".join(changes)), COLOR_SETTINGS))
            else:
                settings_to_store = tuple(old_settings)
        c.execute("INSERT OR REPLACE INTO clan_settings_snapshot VALUES (?, ?, ?, ?, ?)", (guild_id, *settings_to_store))

        # --- members ---
        left = {t for t in old_rows if t not in new_members and ("left", t) in confirmed}
        if old_rows and len(left) >= MASS_KICK_THRESHOLD:
            names = ", ".join(old_rows[t][0] for t in left)
            alerts.append(base_embed(
                "🚨 Mass kick detected",
                clip(f"**{len(left)} members** left/were removed since the last check:\n{names}\n\n"
                     f"This needs a human decision — the bot can't demote or restore anyone, only alert you."),
                COLOR_ALERT))

        final_roles = {}
        for tag, (name, role) in new_members.items():
            if tag not in old_rows:
                open_stay(c, guild_id, tag, name, today, baseline=1 if first_run else 0)
                final_roles[tag] = role
                if first_run:
                    continue
                alerts.append(base_embed("➕ New member",
                                         f"**{name}** joined as {ROLE_ICON.get(role, '')} {role}.", COLOR_JOIN))
                c.execute("INSERT INTO role_history (guild_id, tag, name, event, old_role, new_role, changed_at) "
                          "VALUES (?, ?, ?, 'joined', NULL, ?, ?)", (guild_id, tag, name, role, today))
            elif old_rows[tag][1] != role:
                if ("role", tag, role) in confirmed:
                    old_role = old_rows[tag][1]
                    if _rank(role) > _rank(old_role):
                        alerts.append(base_embed("⬆️ Promotion",
                                                 f"**{name}**: {old_role} → {ROLE_ICON.get(role, '')} {role}", COLOR_PROMO))
                        event = "promoted"
                    else:
                        alerts.append(base_embed("⬇️ Demotion",
                                                 f"**{name}**: {old_role} → {ROLE_ICON.get(role, '')} {role}", COLOR_DEMO))
                        event = "demoted"
                    c.execute("INSERT INTO role_history (guild_id, tag, name, event, old_role, new_role, changed_at) "
                              "VALUES (?, ?, ?, ?, ?, ?, ?)", (guild_id, tag, name, event, old_role, role, today))
                    final_roles[tag] = role
                else:
                    final_roles[tag] = old_rows[tag][1]  # wait for the second check
            else:
                final_roles[tag] = role

        for tag in left:
            name = old_rows[tag][0]
            alerts.append(base_embed("➖ Member left", f"**{name}** left the clan.", COLOR_LEAVE))
            # the stay is closed (not deleted), so a rejoin keeps the old time and the gap
            c.execute("UPDATE stays SET left_at = ? WHERE guild_id = ? AND tag = ? AND left_at IS NULL",
                      (today, guild_id, tag))
            left_confirmed.append((tag, name))

        # donation counters reset weekly: log it when the clan total suddenly drops (to confirm the reset time)
        old_total = sum(old_rows[t][2] for t in new_members if t in old_rows)
        new_total = sum(m["donations"] for m in items if m["tag"] in old_rows)
        if old_total >= 100 and new_total < old_total * 0.5:
            log.warning("Donation counters look reset (guild %s): clan total %s -> %s at %s IST",
                        guild_id, old_total, new_total, datetime.now(IST).strftime("%a %d %b %H:%M:%S"))

        # new snapshot (members with an unconfirmed leave keep their old row for one more check)
        rows = [(guild_id, m["tag"], m["name"], final_roles[m["tag"]], m["donations"], m["lastSeen"]) for m in items]
        for tag, (name, role, dons, seen) in old_rows.items():
            if tag not in new_members and tag not in left:
                rows.append((guild_id, tag, name, role, dons, seen))
        c.execute("DELETE FROM members_snapshot WHERE guild_id = ?", (guild_id,))
        c.executemany("INSERT INTO members_snapshot VALUES (?, ?, ?, ?, ?, ?)", rows)

    roles_now = {r[1]: r[3] for r in rows}

    # database is saved first; only then post the alerts
    channel = bot.get_channel(log_channel_id) if log_channel_id else None
    if channel is not None:
        for e in alerts:
            try:
                await channel.send(embed=e)
            except discord.HTTPException:
                log.warning("Could not post clan-log alert in guild %s (missing permissions?)", guild_id)
                break

    guild = bot.get_guild(guild_id)
    if guild is None:
        return
    # someone left the clan but is still in the Discord server -> flag it
    for tag, name in left_confirmed:
        discord_id = get_link_by_tag(guild_id, tag)
        if discord_id and guild.get_member(discord_id) is not None:
            text = f"**{name}** left the clan but is still in this Discord server. Remove them from the server."
            upsert_flag(guild_id, "left_clan", discord_id, tag, name, text)
            await post_alert(guild_id, flag_embed({"kind": "left_clan", "text": text}))
    await process_flags(guild, roles_now)
    names_now = {m["tag"]: m["name"] for m in items}
    await sync_roles(guild, roles_now, names_now)


def touch_heartbeat():
    with dbc() as c:
        c.execute("INSERT OR REPLACE INTO meta VALUES ('last_alive', ?)", (datetime.now(timezone.utc).isoformat(),))


@tasks.loop(seconds=POLL_SECONDS)
async def watch_clan_log():
    global _slow_mode, _clean_cycles
    rate_limited = False
    try:
        touch_heartbeat()
    except Exception:
        log.exception("heartbeat failed")
    for guild_id, clan_tag, log_channel_id, _alert in get_all_configs():
        try:
            await process_guild_log(guild_id, clan_tag, log_channel_id)
        except aiohttp.ClientResponseError as ex:
            if ex.status == 429:
                rate_limited = True
            log.warning("watch_clan_log: API error %s for guild %s", ex.status, guild_id)
        except Exception:
            log.exception("watch_clan_log failed for guild %s", guild_id)

    if rate_limited:
        _clean_cycles = 0
        if not _slow_mode:
            _slow_mode = True
            watch_clan_log.change_interval(seconds=SLOW_POLL_SECONDS)
            log.warning("Clash Royale API says 429: checking every %ss for now", SLOW_POLL_SECONDS)
    elif _slow_mode:
        _clean_cycles += 1
        if _clean_cycles >= CLEAN_CYCLES_TO_SPEED_UP:
            _slow_mode = False
            _clean_cycles = 0
            watch_clan_log.change_interval(seconds=POLL_SECONDS)
            log.info("API is fine again: back to checking every %ss", POLL_SECONDS)


async def announce_downtime():
    """On start: if the bot was down for a while, say so (changes in that window may be late)."""
    with dbc() as c:
        row = c.execute("SELECT value FROM meta WHERE key = 'last_alive'").fetchone()
    if not row:
        return
    try:
        last = datetime.fromisoformat(row[0])
    except ValueError:
        return
    now = datetime.now(timezone.utc)
    gap = now - last
    if gap < timedelta(seconds=OFFLINE_NOTICE_SECONDS):
        return
    text = (f"Offline from **{last.astimezone(IST).strftime('%d %b %H:%M')}** to "
            f"**{now.astimezone(IST).strftime('%d %b %H:%M')} IST** ({str(gap).split('.')[0]}). "
            f"Changes in that window may be late.")
    for guild_id, _tag, _log, _alert in get_all_configs():
        await post_alert(guild_id, base_embed("🔌 ClanOps was offline", text, COLOR_WARN))


# ---------------- BACKGROUND JOB 2: DAILY SNAPSHOT (1 minute before the 3:30 PM IST war-day reset) ----------------
@tasks.loop(time=dtime(hour=15, minute=29, tzinfo=IST))
async def daily_snapshot():
    today = datetime.now(IST).strftime("%Y-%m-%d")
    cutoff = (datetime.now(IST) - timedelta(days=HISTORY_DAYS)).strftime("%Y-%m-%d")
    for guild_id, clan_tag, _log, _alert in get_all_configs():
        try:
            members = await api(clan_tag, "/members")
            race = await api(clan_tag, "/currentriverrace")
            deck_map = {p["tag"]: p["decksUsedToday"] for p in race["clan"]["participants"]}
            medal_map = {p["tag"]: p["fame"] for p in race["clan"]["participants"]}
            with dbc() as c:
                for m in members["items"]:
                    c.execute("INSERT OR REPLACE INTO daily_history "
                              "(date, guild_id, tag, name, decks_used, medals, donations, donations_received, trophies) "
                              "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                              (today, guild_id, m["tag"], m["name"], deck_map.get(m["tag"], 0),
                               medal_map.get(m["tag"], 0), m["donations"], m.get("donationsReceived", 0),
                               m["trophies"]))
                c.execute("DELETE FROM daily_history WHERE guild_id = ? AND date < ?", (guild_id, cutoff))
        except Exception:
            log.exception("daily_snapshot failed for guild %s", guild_id)


# ---------------- BACKGROUND JOB 3: WEEKLY DONATION SNAPSHOT (Sunday, 1 minute before the weekly reset) ----------------
@tasks.loop(time=dtime(hour=5, minute=29, tzinfo=IST))
async def weekly_donation_snapshot():
    now = datetime.now(IST)
    if now.weekday() != 6:  # Sunday only
        return
    week_end = now.strftime("%Y-%m-%d")
    cutoff = (now - timedelta(days=HISTORY_DAYS)).strftime("%Y-%m-%d")
    for guild_id, clan_tag, _log, _alert in get_all_configs():
        try:
            members = await api(clan_tag, "/members")
            with dbc() as c:
                for m in members["items"]:
                    c.execute("INSERT OR REPLACE INTO weekly_donations VALUES (?, ?, ?, ?, ?, ?)",
                              (week_end, guild_id, m["tag"], m["name"], m["donations"], m.get("donationsReceived", 0)))
                c.execute("DELETE FROM weekly_donations WHERE guild_id = ? AND week_end < ?", (guild_id, cutoff))
        except Exception:
            log.exception("weekly_donation_snapshot failed for guild %s", guild_id)


# ---------------- DISCORD EVENTS (instant) ----------------
@bot.event
async def on_ready():
    global _started
    log.info("Logged in as %s", bot.user)
    if _started:
        return
    _started = True
    try:
        await announce_downtime()
    except Exception:
        log.exception("announce_downtime failed")
    watch_clan_log.start()
    daily_snapshot.start()
    weekly_donation_snapshot.start()


@bot.event
async def on_member_update(before: discord.Member, after: discord.Member):
    """Nickname edits are reverted; a hand-made clan role change is flagged so it is changed in-game too."""
    if before.nick != after.nick and after.id != after.guild.owner_id:
        link = get_link(after.guild.id, after.id)
        if link:
            wanted = snapshot_name(after.guild.id, link[0])
            if wanted and after.nick != wanted[:32]:
                await sync_nickname(after.guild, after.id, wanted)
    if before.roles == after.roles:
        return
    key = (after.guild.id, after.id)
    made_at = _expected_edits.pop(key, None)
    if made_at and time.time() - made_at < 15:
        return  # this was the bot's own role sync
    link = get_link(after.guild.id, after.id)
    if not link:
        return
    tag, name = link
    new_key, old_key = clan_key(after.roles), clan_key(before.roles)
    if new_key is None or new_key == old_key:
        return
    game_role = snapshot_role(after.guild.id, tag)
    if game_role is None:
        return
    if game_role == new_key:
        delete_flag(after.guild.id, "role_change", after.id)
        return
    action = "Demote" if _rank(new_key) < _rank(game_role) else "Promote"
    text = (f"**{name}** is now **{ROLE_TEXT[new_key]}** in Discord but **{ROLE_TEXT[game_role]}** in Clash Royale.\n"
            f"{action} them in-game to **{ROLE_TEXT[new_key]}**. Role syncing for them is paused until the game matches.")
    upsert_flag(after.guild.id, "role_change", after.id, tag, name, text, wanted_role=new_key)
    await post_alert(after.guild.id, flag_embed({"kind": "role_change", "text": text}))


@bot.event
async def on_member_remove(member: discord.Member):
    """A linked person left (or was removed from) the Discord server."""
    link = get_link(member.guild.id, member.id)
    if not link:
        return
    tag, name = link
    delete_flag(member.guild.id, "left_clan", member.id)
    if snapshot_role(member.guild.id, tag) is None:
        delete_link(member.guild.id, member.id)  # gone from both places, nothing left to do
        return
    text = f"**{name}** left the Discord server but is still in the clan. Remove them in Clash Royale too."
    upsert_flag(member.guild.id, "left_server", member.id, tag, name, text)
    await post_alert(member.guild.id, flag_embed({"kind": "left_server", "text": text}))


@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    original = getattr(error, "original", error)
    name = getattr(interaction.command, "name", "?")
    log.error("Error in /%s: %r", name, original, exc_info=original)

    if isinstance(original, aiohttp.ClientResponseError):
        if original.status == 404:
            msg = "Clash Royale couldn't find that clan. If you changed clans, run `/setup` again."
        elif original.status == 403:
            msg = "The Clash Royale API rejected the request. Check that `CR_API_KEY` in your .env is valid."
        elif original.status == 429:
            msg = "The Clash Royale API is rate-limiting right now. Try again in a minute."
        else:
            msg = "The Clash Royale API is having trouble. Try again shortly."
    elif isinstance(original, (aiohttp.ClientError, asyncio.TimeoutError)):
        msg = "Couldn't reach the Clash Royale API. Try again shortly."
    else:
        msg = "Something went wrong. Please try again."

    embed = base_embed("⚠️ Something went wrong", msg, COLOR_WARN)
    try:
        if interaction.response.is_done():
            await interaction.followup.send(embed=embed, ephemeral=True)
        else:
            await interaction.response.send_message(embed=embed, ephemeral=True)
    except discord.HTTPException:
        pass


# ================= COMMANDS =================

@bot.tree.command(name="setup", description="Link this server to a Clash Royale clan (server owner only).")
@app_commands.guild_only()
@app_commands.describe(clan_tag="Your clan tag, must start with # (e.g. #LP9YPU2G)",
                       log_channel="Channel for auto join/leave/promotion alerts",
                       alert_channel="PRIVATE channel for flags (role changes, leaves). Optional.")
async def setup_cmd(interaction: discord.Interaction, clan_tag: str, log_channel: discord.TextChannel,
                    alert_channel: Optional[discord.TextChannel] = None):
    if not is_owner(interaction):
        return await deny(interaction)
    await interaction.response.defer()

    raw = clan_tag.strip()
    if not raw.startswith("#"):
        return await interaction.followup.send(embed=base_embed(
            "❌ Missing #",
            "Your clan tag needs to start with `#`. For example: `#LP9YPU2G`.\n\nPlease run the command again with the `#` included.",
            COLOR_WARN))

    tag = raw[1:].replace(" ", "").upper()
    if not tag or not tag.isalnum():
        return await interaction.followup.send(embed=base_embed(
            "❌ Invalid tag format",
            "That doesn't look like a valid clan tag. It should look like `#LP9YPU2G` — letters and numbers only after the `#`.",
            COLOR_WARN))

    for ch in [log_channel] + ([alert_channel] if alert_channel else []):
        perms = ch.permissions_for(interaction.guild.me)
        if not (perms.view_channel and perms.send_messages and perms.embed_links):
            return await interaction.followup.send(embed=base_embed(
                "❌ Can't post in that channel",
                f"I need **View Channel**, **Send Messages** and **Embed Links** in {ch.mention}. "
                f"Fix the channel permissions and run `/setup` again.", COLOR_WARN))

    try:
        info = await api(tag, "")
        members = await api(tag, "/members")
    except aiohttp.ClientResponseError as ex:
        if ex.status == 404:
            return await interaction.followup.send(embed=base_embed(
                "❌ Wrong clan tag",
                f"`#{tag}` doesn't exist or is wrong. Double-check it in-game under your clan's info page, right below the clan name, and try again.",
                COLOR_WARN))
        raise  # 403 / 429 / 5xx: the global handler explains it instead of blaming the tag

    gid = interaction.guild.id
    today = datetime.now(IST).strftime("%Y-%m-%d")
    old_cfg = get_config(gid)
    same_clan = bool(old_cfg and old_cfg[0] == tag)

    with dbc() as c:
        if old_cfg and not same_clan:
            # switching clans: forget the old clan's data so history doesn't get mixed up
            for table in ("members_snapshot", "clan_settings_snapshot", "daily_history", "weekly_donations",
                          "stays", "role_history", "links", "flags"):
                c.execute(f"DELETE FROM {table} WHERE guild_id = ?", (gid,))
            _prev_candidates.pop(gid, None)
        alert_id = alert_channel.id if alert_channel else (old_cfg[2] if same_clan else None)
        c.execute("INSERT OR REPLACE INTO guild_config VALUES (?, ?, ?, ?)", (gid, tag, log_channel.id, alert_id))
        if not same_clan:
            # baseline, so the first clan check doesn't announce every member as "new"
            c.executemany("INSERT INTO members_snapshot VALUES (?, ?, ?, ?, ?, ?)",
                          [(gid, m["tag"], m["name"], m["role"], m["donations"], m["lastSeen"])
                           for m in members["items"]])
            c.execute("INSERT OR REPLACE INTO clan_settings_snapshot VALUES (?, ?, ?, ?, ?)",
                      (gid, info.get("description"), info.get("type"),
                       info.get("requiredTrophies"), info.get("warFrequency")))
            for m in members["items"]:
                open_stay(c, gid, m["tag"], m["name"], today, baseline=1)
                c.execute("""INSERT INTO role_history (guild_id, tag, name, event, old_role, new_role, changed_at)
                             SELECT ?, ?, ?, 'joined', NULL, ?, ?
                             WHERE NOT EXISTS (SELECT 1 FROM role_history WHERE guild_id = ? AND tag = ?)""",
                          (gid, m["tag"], m["name"], m["role"], today, gid, m["tag"]))

    title = "✅ ClanOps settings updated" if same_clan else "✅ ClanOps is set up"
    e = base_embed(title, color=COLOR_MAIN)
    e.add_field(name="Clan", value=f"{info['name']} (#{tag})", inline=True)
    e.add_field(name="Members", value=f"{info['members']}/50", inline=True)
    e.add_field(name="Clan-log channel", value=log_channel.mention, inline=False)
    alert_ch = interaction.guild.get_channel(alert_id) if alert_id else None
    e.add_field(name="Alert channel (flags)",
                value=alert_ch.mention if alert_ch else "Not set — flags go to the clan-log channel. Run `/setup` again with `alert_channel` to keep them private.",
                inline=False)
    if same_clan:
        e.add_field(name="Note", value="Same clan — all your data was kept.", inline=False)
    else:
        e.add_field(name="Note", value=f"Tracking starts today ({today}). History before this date isn't available from the game's API.", inline=False)
    badge_url = info.get("badgeUrls", {}).get("large")
    if badge_url:
        e.set_thumbnail(url=badge_url)
    await interaction.followup.send(embed=e)


@bot.tree.command(name="help", description="Show all ClanOps commands.")
@app_commands.guild_only()
async def help_cmd(interaction: discord.Interaction):
    lines = [
        "`/setup` — link this server to your clan (server owner only)",
        "`/link` · `/unlink` — tie a Discord user to their player tag (owner / clan Leader)",
        "`/grant` — let a user or role use specific commands (owner / clan Leader)",
        "`/help` — this list",
        "`/currentriverrace` — live war standings, grouped by role",
        "`/riverhistory` — decks & medals over past wars, with performance category",
        "`/inactive` — members inactive for X+ days",
        "`/donations` — donation leaderboard (this week, or up to 4 weeks)",
        "`/member` — one player's role history and daily stats",
        "`/seniority` — clan tenure ranking, including past stays",
        "`/playerreview` — who to promote, demote, kick or keep",
        "`/playerperformance` — one player's full data and verdict",
        "Automatic: clan-log alerts, role sync with Discord, and flags for things to change in-game",
    ]
    e = base_embed("📖 ClanOps Commands", "\n".join(lines))
    e.add_field(name="Note", value="All commands are free. The server owner and the linked clan Leader can use everything; they can share commands with `/grant`.", inline=False)
    await interaction.response.send_message(embed=e)


@bot.tree.command(name="link", description="Link a player, or list who is linked / not linked (owner / clan Leader).")
@app_commands.guild_only()
@app_commands.describe(action="Link (default), List linked players, or show Unlinked clan members",
                       user="The Discord member (for Link)", player_tag="Their player tag, e.g. #ABC123 (for Link)")
@app_commands.choices(action=[app_commands.Choice(name="Link", value="link"),
                              app_commands.Choice(name="List", value="list"),
                              app_commands.Choice(name="Unlinked", value="unlinked")])
async def link_cmd(interaction: discord.Interaction, action: Optional[app_commands.Choice[str]] = None,
                   user: Optional[discord.Member] = None, player_tag: Optional[str] = None):
    if not is_admin(interaction):
        return await deny(interaction)
    await interaction.response.defer(ephemeral=True)
    gid = interaction.guild.id
    clan = get_clan_tag(gid)
    if not clan:
        return await not_set_up(interaction)
    mode = action.value if action else "link"

    members = await api(clan, "/members")
    by_tag = {m["tag"]: m for m in members["items"]}

    if mode == "list":
        with dbc() as c:
            rows = c.execute("SELECT discord_id, tag, name FROM links WHERE guild_id = ?", (gid,)).fetchall()
        if not rows:
            return await interaction.followup.send(embed=base_embed(
                "🔗 Linked players", "Nobody is linked yet. Use `/link user:@someone player_tag:#TAG`.", COLOR_WARN), ephemeral=True)
        rows.sort(key=lambda r: _rank(by_tag[r[1]]["role"]) if r[1] in by_tag else -1, reverse=True)
        lines = []
        for did, ptag, pname in rows:
            cur = by_tag.get(ptag)
            if cur:
                lines.append(f"<@{did}> ↔ **{cur['name']}** ({ptag}) — {ROLE_TEXT[cur['role']]}")
            else:
                lines.append(f"<@{did}> ↔ **{pname}** ({ptag}) — ⚠️ no longer in the clan")
        return await interaction.followup.send(embed=base_embed(
            f"🔗 Linked players ({len(rows)})", clip("\n".join(lines))), ephemeral=True)

    if mode == "unlinked":
        with dbc() as c:
            linked = {r[0] for r in c.execute("SELECT tag FROM links WHERE guild_id = ?", (gid,))}
        missing = [{"tag": m["tag"], "name": m["name"], "role": m["role"]}
                   for m in members["items"] if m["tag"] not in linked]
        if not missing:
            return await interaction.followup.send(embed=base_embed(
                "✅ Everyone is linked", "Every clan member has a Discord link.", COLOR_JOIN), ephemeral=True)
        body = render_grouped(group_by_role(missing), lambda p: f"{p['name']} ({p['tag']})")
        return await interaction.followup.send(embed=base_embed(
            f"🔓 Not linked ({len(missing)})", clip(body), COLOR_WARN), ephemeral=True)

    if user is None or not player_tag:
        return await interaction.followup.send(embed=base_embed(
            "⚠️ Missing options", "To link, fill in both `user` and `player_tag`.", COLOR_WARN), ephemeral=True)

    ptag = norm_tag(player_tag)
    match = by_tag.get(ptag)
    if not match:
        return await interaction.followup.send(embed=base_embed(
            "❌ Not in your clan", f"`{ptag}` isn't a current member of your clan. Check the tag and try again.", COLOR_WARN), ephemeral=True)

    with dbc() as c:
        by_user = c.execute("SELECT tag, name FROM links WHERE guild_id = ? AND discord_id = ?", (gid, user.id)).fetchone()
        by_tag_row = c.execute("SELECT discord_id FROM links WHERE guild_id = ? AND tag = ?", (gid, ptag)).fetchone()
        if by_user and by_user[0] != ptag:
            return await interaction.followup.send(embed=base_embed(
                "⚠️ Already linked", f"{user.mention} is already linked to **{by_user[1]}** ({by_user[0]}). Use `/unlink` first.", COLOR_WARN), ephemeral=True)
        if by_tag_row and by_tag_row[0] != user.id:
            return await interaction.followup.send(embed=base_embed(
                "⚠️ Already linked", f"**{match['name']}** is already linked to <@{by_tag_row[0]}>. Use `/unlink` for that user first.", COLOR_WARN), ephemeral=True)
        c.execute("INSERT OR REPLACE INTO links VALUES (?, ?, ?, ?, ?)",
                  (gid, user.id, ptag, match["name"], datetime.now(IST).strftime("%Y-%m-%d")))

    role_status = await sync_member_role(interaction.guild, user.id, match["role"])
    nick_status = await sync_nickname(interaction.guild, user.id, match["name"])
    e = base_embed("🔗 Linked", f"{user.mention} ↔ **{match['name']}** ({ptag}) — {ROLE_TEXT[match['role']]} in-game.")
    e.add_field(name="Discord role",
                value="Matched to their in-game role." if role_status in ("ok", "updated") else f"Not changed: {role_status}.", inline=False)
    e.add_field(name="Nickname",
                value=f"Set to **{match['name'][:32]}**." if nick_status in ("ok", "updated") else f"Not changed: {nick_status}.", inline=False)
    await interaction.followup.send(embed=e, ephemeral=True)


@bot.tree.command(name="unlink", description="Remove a Discord user's player link (owner / clan Leader).")
@app_commands.guild_only()
@app_commands.describe(user="The Discord member")
async def unlink_cmd(interaction: discord.Interaction, user: discord.Member):
    if not is_admin(interaction):
        return await deny(interaction)
    await interaction.response.defer(ephemeral=True)
    gid = interaction.guild.id
    if not get_link(gid, user.id):
        return await interaction.followup.send(embed=base_embed("Not linked", f"{user.mention} has no link.", COLOR_WARN), ephemeral=True)
    delete_link(gid, user.id)
    with dbc() as c:
        c.execute("DELETE FROM flags WHERE guild_id = ? AND discord_id = ?", (gid, user.id))
    await interaction.followup.send(embed=base_embed("🔓 Unlinked", f"{user.mention} is no longer linked. Their Discord roles were left as they are."), ephemeral=True)


@bot.tree.command(name="grant", description="Let a user or role use specific commands (owner / clan Leader).")
@app_commands.guild_only()
@app_commands.describe(action="Add, remove or list grants", command="Which command", user="A Discord user", role="A Discord role")
@app_commands.choices(
    action=[app_commands.Choice(name="Add", value="add"), app_commands.Choice(name="Remove", value="remove"),
            app_commands.Choice(name="List", value="list")],
    command=[app_commands.Choice(name=c, value=c) for c in GRANTABLE])
async def grant_cmd(interaction: discord.Interaction, action: app_commands.Choice[str],
                    command: Optional[app_commands.Choice[str]] = None,
                    user: Optional[discord.Member] = None, role: Optional[discord.Role] = None):
    if not is_admin(interaction):
        return await deny(interaction)
    await interaction.response.defer(ephemeral=True)
    gid = interaction.guild.id

    if action.value == "list":
        with dbc() as c:
            rows = c.execute("SELECT command, kind, target_id FROM grants WHERE guild_id = ? ORDER BY command", (gid,)).fetchall()
        if not rows:
            return await interaction.followup.send(embed=base_embed("🔑 Grants", "Nothing granted yet. Only the owner and the clan Leader can use the commands."), ephemeral=True)
        lines = [f"`/{cmd}` → {'<@' + str(tid) + '>' if kind == 'user' else '<@&' + str(tid) + '>'}" for cmd, kind, tid in rows]
        return await interaction.followup.send(embed=base_embed("🔑 Grants", clip("\n".join(lines))), ephemeral=True)

    if command is None or (user is None and role is None):
        return await interaction.followup.send(embed=base_embed(
            "⚠️ Missing options", "Pick a `command` and a `user` or a `role`.", COLOR_WARN), ephemeral=True)
    kind, target = ("user", user) if user is not None else ("role", role)
    with dbc() as c:
        if action.value == "add":
            c.execute("INSERT OR IGNORE INTO grants VALUES (?, ?, ?, ?)", (gid, kind, target.id, command.value))
        else:
            c.execute("DELETE FROM grants WHERE guild_id = ? AND kind = ? AND target_id = ? AND command = ?",
                      (gid, kind, target.id, command.value))
    verb = "can now use" if action.value == "add" else "can no longer use"
    await interaction.followup.send(embed=base_embed("🔑 Updated", f"{target.mention} {verb} `/{command.value}`."), ephemeral=True)


@bot.tree.command(name="currentriverrace", description="Show live war standings.")
@app_commands.guild_only()
@app_commands.describe(role="Filter to one role", player="Filter to one player")
@app_commands.choices(role=[app_commands.Choice(name=k, value=k) for k in ROLE_MAP])
@app_commands.autocomplete(player=player_autocomplete)
async def currentriverrace(interaction: discord.Interaction, role: Optional[app_commands.Choice[str]] = None,
                           player: Optional[str] = None):
    if not can_use(interaction, "currentriverrace"):
        return await deny(interaction)
    await interaction.response.defer()
    tag = get_clan_tag(interaction.guild.id)
    if not tag:
        return await not_set_up(interaction)

    race = await api(tag, "/currentriverrace")
    period = str(race.get("periodType", "")).lower()
    log.info("currentriverrace periodType=%r periodIndex=%r", race.get("periodType"), race.get("periodIndex"))
    if period == "training":
        return await interaction.followup.send(embed=base_embed(
            "🏋️ Training days",
            "It's a training day, so there are no war decks to track right now. Live standings return when war days start.",
            COLOR_WARN))

    members = await api(tag, "/members")
    role_map = {m["tag"]: (m["name"], m["role"]) for m in members["items"]}

    people = []
    decks_today = {}
    for p in race["clan"]["participants"]:
        if p["tag"] not in role_map:
            continue  # contributed earlier this war but has since left the clan
        name, prole = role_map[p["tag"]]
        decks_today[p["tag"]] = p["decksUsedToday"]
        if p["decksUsed"] == 0 and p["fame"] == 0:
            continue
        people.append({"tag": p["tag"], "name": name, "role": prole, "medals": p["fame"],
                       "decks_today": p["decksUsedToday"]})

    if player:
        people = [p for p in people if is_player(p, player)]
        if not people:
            return await interaction.followup.send(embed=base_embed("Not found", f"No war data for '{player}'.", COLOR_WARN))
        p = people[0]
        mark = "✅" if p["decks_today"] >= 4 else f"{p['decks_today']}/4"
        return await interaction.followup.send(embed=base_embed(
            f"⚔️ {p['name']} ({p['role']})", f"Medals: {p['medals']} · Decks today: {mark}"))

    if role:
        people = [p for p in people if p["role"] == ROLE_MAP[role.value]]

    grouped = group_by_role(people)

    def line(p):
        mark = "✅" if p["decks_today"] >= 4 else f"{p['decks_today']}/4"
        return f"{p['name']} — {p['medals']} medals — {mark}"

    # everyone currently in the clan who still has decks to play today
    lazy = [name for tg, (name, prole) in role_map.items()
            if decks_today.get(tg, 0) < 4 and (not role or prole == ROLE_MAP[role.value])]
    lazy_value = ", ".join(lazy) if lazy else "Nobody — all done! 🎉"
    await send_grouped_embed(
        interaction, f"⚔️ Current River Race — {race['clan']['fame']} medals",
        render_grouped(grouped, line), extra_field=("Decks left today", lazy_value))


@bot.tree.command(name="riverhistory", description="Show decks/medals over the last n wars (1-4).")
@app_commands.guild_only()
@app_commands.describe(n="Number of past wars, 1-4", role="Filter to one role",
                       rivercategory="Filter by performance category", player="Filter to one player")
@app_commands.choices(
    role=[app_commands.Choice(name=k, value=k) for k in ROLE_MAP],
    rivercategory=[app_commands.Choice(name=x, value=x) for x in ["Excellent", "Okay", "Bad"]]
)
@app_commands.autocomplete(player=player_autocomplete)
async def riverhistory(interaction: discord.Interaction, n: app_commands.Range[int, 1, 4] = 4,
                       role: Optional[app_commands.Choice[str]] = None,
                       rivercategory: Optional[app_commands.Choice[str]] = None,
                       player: Optional[str] = None):
    if not can_use(interaction, "riverhistory"):
        return await deny(interaction)
    await interaction.response.defer()
    gid = interaction.guild.id
    tag = get_clan_tag(gid)
    if not tag:
        return await not_set_up(interaction)

    race_log = await api(tag, "/riverracelog")
    members = await api(tag, "/members")
    role_map = {m["tag"]: m["role"] for m in members["items"]}
    stays = load_stays(gid)
    today = datetime.now(IST).date()

    names, medals, decks = {}, defaultdict(int), defaultdict(int)
    for race in race_log["items"][:n]:
        for st in race["standings"]:
            if st["clan"]["tag"].replace("#", "") == tag:
                for p in st["clan"]["participants"]:
                    names[p["tag"]] = p["name"]
                    medals[p["tag"]] += p["fame"]
                    decks[p["tag"]] += p["decksUsed"]
    wars_counted = max(1, min(n, len(race_log["items"])))
    max_decks = 16 * wars_counted

    def category(pct):
        if pct >= 70:
            return "Excellent", "🟢"
        if pct >= 40:
            return "Okay", "🟡"
        return "Bad", "🔴"

    people = []
    for ptag in decks:
        if ptag not in role_map:
            continue  # left the clan
        summ = stay_summary(stays.get(ptag, []), today)
        # joined after the bot was set up, and recently enough to have missed part of these wars
        is_new = summ["has"] and not summ["baseline"] and summ["current"] < 7 * wars_counted
        pct = (decks[ptag] / max_decks * 100) if max_decks else 0
        if is_new:
            cat, icon = "New", "🆕"
        else:
            cat, icon = category(pct)
        people.append({"tag": ptag, "name": names[ptag], "role": role_map[ptag],
                       "decks": decks[ptag], "pct": pct, "medals": medals[ptag],
                       "cat": cat, "icon": icon, "new": is_new, "days": summ["current"]})

    def describe(p):
        if p["new"]:
            return f"🆕 new member ({p['days']}d in clan) — {p['decks']} decks played — {p['medals']} medals"
        return f"{p['decks']}/{max_decks} decks ({p['pct']:.0f}%) {p['icon']} {p['cat']} — {p['medals']} medals"

    if player:
        people = [p for p in people if is_player(p, player)]
        if not people:
            return await interaction.followup.send(embed=base_embed("Not found", f"No history for '{player}'.", COLOR_WARN))
        p = people[0]
        return await interaction.followup.send(embed=base_embed(f"📜 {p['name']} — last {wars_counted} wars", describe(p)))

    if role:
        people = [p for p in people if p["role"] == ROLE_MAP[role.value]]
    if rivercategory:
        people = [p for p in people if p["cat"] == rivercategory.value]

    grouped = group_by_role(people)
    line = lambda p: f"{p['name']} — {describe(p)}"
    title = f"📜 River History — last {wars_counted} wars (max {max_decks} decks)"
    if rivercategory:
        title += f" — {rivercategory.value} players"
    await send_grouped_embed(interaction, title, render_grouped(grouped, line))


@bot.tree.command(name="inactive", description="Show members inactive for d+ days.")
@app_commands.guild_only()
@app_commands.describe(days="Inactivity threshold in days", role="Filter to one role", player="Filter to one player")
@app_commands.choices(role=[app_commands.Choice(name=k, value=k) for k in ROLE_MAP])
@app_commands.autocomplete(player=player_autocomplete)
async def inactive(interaction: discord.Interaction, days: app_commands.Range[int, 1, 365] = 7,
                   role: Optional[app_commands.Choice[str]] = None, player: Optional[str] = None):
    if not can_use(interaction, "inactive"):
        return await deny(interaction)
    await interaction.response.defer()
    tag = get_clan_tag(interaction.guild.id)
    if not tag:
        return await not_set_up(interaction)

    data = await api(tag, "/members")
    now = datetime.now(timezone.utc)
    people = []
    for m in data["items"]:
        gap = (now - parse_seen(m["lastSeen"])).days
        if gap >= days:
            people.append({"tag": m["tag"], "name": m["name"], "role": m["role"], "gap": gap})

    if player:
        people = [p for p in people if is_player(p, player)]
        if not people:
            return await interaction.followup.send(embed=base_embed("Not flagged", f"'{player}' hasn't been inactive {days}+ days."))
        p = people[0]
        return await interaction.followup.send(embed=base_embed(f"😴 {p['name']} ({p['role']})", f"Last seen {p['gap']}d ago"))

    if role:
        people = [p for p in people if p["role"] == ROLE_MAP[role.value]]

    if not people:
        return await interaction.followup.send(embed=base_embed("😴 Inactive check", f"Everyone was seen in the last {days} days."))

    grouped = group_by_role(people)
    line = lambda p: f"{p['name']} — last seen {p['gap']}d ago"
    await send_grouped_embed(interaction, f"😴 Inactive {days}+ days", render_grouped(grouped, line), COLOR_WARN)


@bot.tree.command(name="donations", description="Donation leaderboard: this week, or up to the last 4 weeks.")
@app_commands.guild_only()
@app_commands.describe(weeks="How many weeks to combine, 1-4 (default 1 = this week)",
                       role="Filter to one role", donationcategory="Filter by give/take category",
                       player="Filter to one player")
@app_commands.choices(
    role=[app_commands.Choice(name=k, value=k) for k in ROLE_MAP],
    donationcategory=[app_commands.Choice(name=x, value=x) for x in ["Generous", "Balanced", "Taker", "NaN"]]
)
@app_commands.autocomplete(player=player_autocomplete)
async def donations(interaction: discord.Interaction, weeks: app_commands.Range[int, 1, 4] = 1,
                    role: Optional[app_commands.Choice[str]] = None,
                    donationcategory: Optional[app_commands.Choice[str]] = None, player: Optional[str] = None):
    if not can_use(interaction, "donations"):
        return await deny(interaction)
    await interaction.response.defer()
    gid = interaction.guild.id
    tag = get_clan_tag(gid)
    if not tag:
        return await not_set_up(interaction)

    data = await api(tag, "/members")

    # the live counters are the current week; earlier weeks come from the Sunday snapshots the bot saved
    past, recorded = {}, 0
    if weeks > 1:
        with dbc() as c:
            week_ends = [r[0] for r in c.execute(
                "SELECT DISTINCT week_end FROM weekly_donations WHERE guild_id = ? ORDER BY week_end DESC LIMIT ?",
                (gid, weeks - 1))]
            recorded = len(week_ends)
            if week_ends:
                marks = ",".join("?" * len(week_ends))
                for ptag, gave, got in c.execute(
                        f"SELECT tag, SUM(donated), SUM(received) FROM weekly_donations "
                        f"WHERE guild_id = ? AND week_end IN ({marks}) GROUP BY tag", (gid, *week_ends)):
                    past[ptag] = (gave or 0, got or 0)

    def categorize(gave, received):
        if gave == 0 and received == 0:
            return "NaN", "⚪"
        if received == 0 and gave > 0:
            return "Generous", "🟢"
        ratio = gave / received
        if ratio >= 1.5:
            return "Generous", "🟢"
        if ratio >= 0.5:
            return "Balanced", "🟡"
        return "Taker", "🔴"

    people = []
    for m in data["items"]:
        extra_gave, extra_got = past.get(m["tag"], (0, 0))
        gave, got = m["donations"] + extra_gave, m["donationsReceived"] + extra_got
        cat, icon = categorize(gave, got)
        people.append({"tag": m["tag"], "name": m["name"], "role": m["role"], "gave": gave,
                       "got": got, "cat": cat, "icon": icon})

    if player:
        people = [p for p in people if is_player(p, player)]
        if not people:
            return await interaction.followup.send(embed=base_embed("Not found", f"No data for '{player}'.", COLOR_WARN))
        p = people[0]
        return await interaction.followup.send(embed=base_embed(
            f"🎁 {p['name']} ({p['role']})", f"Gave {p['gave']} / got {p['got']} — {p['icon']} {p['cat']}"))

    if role:
        people = [p for p in people if p["role"] == ROLE_MAP[role.value]]
    if donationcategory:
        people = [p for p in people if p["cat"] == donationcategory.value]

    grouped = group_by_role(people)
    line = lambda p: f"{p['name']} — gave {p['gave']} / got {p['got']} {p['icon']} {p['cat']}"
    title = "🎁 Donations — this week" if weeks == 1 else f"🎁 Donations — this week + {recorded} earlier week(s)"
    if donationcategory:
        title += f" — {donationcategory.value}"
    body = render_grouped(grouped, line)
    if weeks > 1 and recorded < weeks - 1:
        body += f"\n\n_Only {recorded} of {weeks - 1} earlier weeks are recorded so far (the bot saves one every Sunday)._"
    await send_grouped_embed(interaction, title, body)


@bot.tree.command(name="member", description="Show one player's role history and daily stats.")
@app_commands.guild_only()
@app_commands.describe(name="Player name or tag")
@app_commands.autocomplete(name=player_autocomplete)
async def member_cmd(interaction: discord.Interaction, name: str):
    if not can_use(interaction, "member"):
        return await deny(interaction)
    await interaction.response.defer()
    clan = get_clan_tag(interaction.guild.id)
    if not clan:
        return await not_set_up(interaction)

    members = await api(clan, "/members")
    ptag, pname = resolve_player(interaction.guild.id, members["items"], name)
    if not ptag:
        return await interaction.followup.send(embed=base_embed("Not found", f"No player '{name}' found.", COLOR_WARN))
    match = next((m for m in members["items"] if m["tag"] == ptag), None)
    role = match["role"] if match else "no longer in clan"

    cutoff = (datetime.now(IST) - timedelta(days=MEMBER_DISPLAY_DAYS)).strftime("%Y-%m-%d")
    with dbc() as c:
        role_events = c.execute("""SELECT event, old_role, new_role, changed_at FROM role_history
                                   WHERE guild_id = ? AND tag = ? ORDER BY changed_at ASC, id ASC""",
                                (interaction.guild.id, ptag)).fetchall()
        daily_rows = c.execute("""SELECT date, decks_used, medals, donations, donations_received, trophies
                                  FROM daily_history WHERE guild_id = ? AND tag = ? AND date >= ?
                                  ORDER BY date DESC""",
                               (interaction.guild.id, ptag, cutoff)).fetchall()

    role_lines = []
    for event, old_role, new_role, changed_at in role_events:
        if event == "joined":
            role_lines.append(f"{changed_at} — Joined as {new_role}")
        elif event == "promoted":
            role_lines.append(f"{changed_at} — ⬆️ {old_role} → {new_role}")
        else:
            role_lines.append(f"{changed_at} — ⬇️ {old_role} → {new_role}")

    e = base_embed(f"📅 History — {pname} ({role})",
                   clip("**Role History**\n" + ("\n".join(role_lines) if role_lines else "No recorded changes yet.")))
    await interaction.followup.send(embed=e)

    if not daily_rows:
        return await interaction.followup.send(
            f"No daily stats recorded yet for {pname} — the daily snapshot needs at least one day to run first.")

    lines = [f"Daily Stats (last {MEMBER_DISPLAY_DAYS} days)", ""]
    for day, decks, medals, don, got, troph in daily_rows:
        lines.append(f"{day} — {decks} decks, {medals} medals, {don} given / {got} got, {troph}🏆")
    await send_long(lambda t: interaction.followup.send(t), "\n".join(lines))


@bot.tree.command(name="seniority", description="Show clan seniority order (including past stays).")
@app_commands.guild_only()
@app_commands.describe(role="Filter to one role", player="Filter to one player")
@app_commands.choices(role=[app_commands.Choice(name=k, value=k) for k in ROLE_MAP])
@app_commands.autocomplete(player=player_autocomplete)
async def seniority(interaction: discord.Interaction, role: Optional[app_commands.Choice[str]] = None,
                    player: Optional[str] = None):
    if not can_use(interaction, "seniority"):
        return await deny(interaction)
    await interaction.response.defer()
    gid = interaction.guild.id
    tag = get_clan_tag(gid)
    if not tag:
        return await not_set_up(interaction)

    members = await api(tag, "/members")
    stays = load_stays(gid)
    today = datetime.now(IST).date()

    people = []
    for m in members["items"]:
        s = stay_summary(stays.get(m["tag"], []), today)
        people.append({"tag": m["tag"], "name": m["name"], "role": m["role"], "since": s["since"] or "unknown",
                       "current": s["current"], "before": s["before"], "gap": s["gap"],
                       "total": s["current"] + s["before"]})

    def describe(p):
        text = f"since {p['since']} ({fmt_days(p['current'])})"
        if p["before"] > 0 or p["gap"] is not None:
            text += f" · before: {fmt_days(p['before'])}"
            if p["gap"] is not None:
                text += f" · away {fmt_days(p['gap'])}"
        return text

    if player:
        people = [p for p in people if is_player(p, player)]
        if not people:
            return await interaction.followup.send(embed=base_embed("Not found", f"No data for '{player}'.", COLOR_WARN))
        p = people[0]
        return await interaction.followup.send(embed=base_embed(
            f"👑 {p['name']} ({p['role']})", f"{describe(p)}\nTotal time in clan: {fmt_days(p['total'])}"))

    if role:
        people = [p for p in people if p["role"] == ROLE_MAP[role.value]]

    grouped = group_by_role(people)
    for r in grouped:
        grouped[r].sort(key=lambda p: p["total"], reverse=True)
    line = lambda p: f"{p['name']} — {describe(p)}"
    await send_grouped_embed(interaction, "👑 Seniority Order (by total time in clan)", render_grouped(grouped, line))


@bot.tree.command(name="playerreview", description="Who to promote, demote, kick or keep.")
@app_commands.guild_only()
async def playerreview(interaction: discord.Interaction):
    if not can_use(interaction, "playerreview"):
        return await deny(interaction)
    await interaction.response.defer()
    tag = get_clan_tag(interaction.guild.id)
    if not tag:
        return await not_set_up(interaction)

    rows, _ = await compute_scores(interaction.guild.id, tag)
    groups = {k: [] for k in VERDICT_ORDER}
    for r in rows:
        code, why = verdict(r)
        if code == "leader":
            continue
        groups[code].append((r, why))

    parts = []
    for code in VERDICT_ORDER:
        entries = sorted(groups[code], key=lambda x: x[0]["score"], reverse=True)
        if not entries:
            continue
        lines = [f"{i + 1}. {r['name']} ({ROLE_TEXT[r['role']]}) — {r['score']:.1f} — {why}"
                 for i, (r, why) in enumerate(entries)]
        parts.append(f"**{VERDICT_TITLE[code]} ({len(entries)})**\n" + "\n".join(lines))

    notes = [f"Kick candidate = not seen for {KICK_INACTIVE_DAYS}+ days. Suggestions only: the bot can't change anyone's role."]
    if COLEADER_PROMOTE_SCORE is None or COLEADER_DEMOTE_SCORE is None:
        notes.append("Co-Leader promotion/demotion rules are not set yet, so none are suggested.")
    await send_grouped_embed(interaction, "📋 Player Review", "\n\n".join(parts) or "No members found.",
                             extra_field=("Notes", "\n".join(notes)))


@bot.tree.command(name="playerperformance", description="One player's full data and verdict.")
@app_commands.guild_only()
@app_commands.describe(player="The player to look up")
@app_commands.autocomplete(player=player_autocomplete)
async def playerperformance(interaction: discord.Interaction, player: str):
    if not can_use(interaction, "playerperformance"):
        return await deny(interaction)
    await interaction.response.defer()
    gid = interaction.guild.id
    clan = get_clan_tag(gid)
    if not clan:
        return await not_set_up(interaction)

    rows, max_decks = await compute_scores(gid, clan)
    match = next((r for r in rows if is_player(r, player)), None)
    if not match:
        return await interaction.followup.send(embed=base_embed("Not found", f"No current member '{player}'.", COLOR_WARN))

    code, why = verdict(match)
    verdict_text = {
        "leader": "👑 Leader — not judged",
        "promote": f"⭐ Promote — {why}",
        "demote": f"⚠️ Demote — {why}",
        "kick": f"🔴 Kick candidate — {why}",
        "new": f"🆕 Not eligible yet — {why}",
        "stable": "✅ Stable — no change suggested",
    }[code]

    pct = (match["decks"] / max_decks * 100) if max_decks else 0
    s = match["stay"]
    tenure_line = f"{fmt_days(match['tenure'])} in current stay"
    if s["before"] > 0 or s["gap"] is not None:
        tenure_line += f" · before: {fmt_days(s['before'])}"
        if s["gap"] is not None:
            tenure_line += f" · away {fmt_days(s['gap'])}"

    with dbc() as c:
        events = c.execute("""SELECT event, old_role, new_role, changed_at FROM role_history
                              WHERE guild_id = ? AND tag = ? ORDER BY changed_at DESC, id DESC LIMIT 5""",
                           (gid, match["tag"])).fetchall()
    hist = []
    for event, old_role, new_role, changed_at in events:
        hist.append(f"{changed_at} — Joined as {new_role}" if event == "joined"
                    else f"{changed_at} — {'⬆️' if event == 'promoted' else '⬇️'} {old_role} → {new_role}")

    desc = (f"**Verdict:** {verdict_text}\n\n"
            f"Score: {match['score']:.1f}\n"
            f"Medals (last 4 wars): {match['medals']} — {pct:.0f}% decks used\n"
            f"Donations given: {match['donations']}\n"
            f"Tenure: {tenure_line}\n"
            f"Last seen: {match['inactivity']}d ago\n\n"
            f"**Recent role history**\n" + ("\n".join(hist) if hist else "No recorded changes yet."))
    await interaction.followup.send(embed=base_embed(
        f"📋 {match['name']} ({ROLE_TEXT[match['role']]}) — {match['tag']}", clip(desc)))


if __name__ == "__main__":
    bot.run(DISCORD_TOKEN)