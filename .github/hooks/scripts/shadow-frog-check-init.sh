#!/usr/bin/env bash
# Hook: sessionStart — check if .shadow/ exists, report status
# Outputs JSON with additionalContext for injection into agent conversation.

# sessionStart is fail-open by contract, but we still run defensively so an
# internal hiccup never produces noisy stderr or a non-zero exit. See
# shadow-frog-pre-tool.sh for the full defense-in-depth rationale. Same trap
# pyramid: EXIT handles clean non-zero exits; TERM/HUP/INT handles runner-
# initiated signal kills (EXIT alone returns 143/-15 under SIGTERM).
trap 'exit 0' EXIT
trap 'exit 0' TERM HUP INT PIPE

# Defensive PATH — some runners launch hooks with a stripped PATH (observed
# under sandboxed containers). Append the standard binary dirs so cat,
# python3, and git remain findable. We APPEND (not prepend) to honor any
# custom paths the runner exported intentionally.
PATH="${PATH:+$PATH:}/usr/local/bin:/usr/bin:/bin"
export PATH

# Consume stdin (the JSON payload) to keep the runner's pipe drained, even
# though check-init doesn't need its content. shellcheck flags INPUT as unused;
# that's intentional. Brace group silences bash's own "ignored null byte"
# warning (bash 5+) if stdin ever contains NULs.
# shellcheck disable=SC2034
{ INPUT=$(cat 2>/dev/null || echo ""); } 2>/dev/null

if [ ! -d ".shadow" ]; then
    python3 -c "import json; ctx='[ShadowFrog] No .shadow/ directory found. Run /shadow-frog-init to create one.'; print(json.dumps({'additionalContext': ctx, 'hookSpecificOutput': {'hookEventName': 'SessionStart', 'additionalContext': ctx}}))" 2>/dev/null
    exit 0
fi

# Read state.json in ONE python3 invocation (instead of three separate calls).
# Single startup cost; smaller blast radius if python3 is slow or state.json
# is unusual. Output is three pipe-separated values on stdout:
#   <total_files>|<total_discoveries>|<last_update_at>
STATE_INFO=$(python3 -c "
import json
try:
    s = json.load(open('.shadow/_meta/state.json'))
    if not isinstance(s, dict):
        s = {}
except Exception:
    s = {}
print(str(s.get('total_files', 0)) + '|' + str(s.get('total_discoveries', 0)) + '|' + str(s.get('last_update_at', 'unknown')))
" 2>/dev/null || echo "0|0|unknown")
TOTAL_FILES="${STATE_INFO%%|*}"
REST="${STATE_INFO#*|}"
TOTAL_DISCOVERIES="${REST%%|*}"
LAST_UPDATE="${REST#*|}"
[ -z "$TOTAL_FILES" ] && TOTAL_FILES=0
[ -z "$TOTAL_DISCOVERIES" ] && TOTAL_DISCOVERIES=0
[ -z "$LAST_UPDATE" ] && LAST_UPDATE="unknown"

# Garbage-collect old dedup directories from past sessions. Without this,
# /tmp/shadowfrog-hook-* accumulates over months and can hit inode caps on
# long-lived workstations. SessionStart fires once per Copilot session, so
# it's the natural GC trigger (vs pre-tool which fires many times per
# session). Bounded inside Python with top-level try/except so any
# filesystem hiccup is silently absorbed.
python3 - <<'PYEOF' 2>/dev/null || true
import os, time, shutil
tmp_root = os.environ.get('SHADOWFROG_TMP_DIR') or os.environ.get('TMPDIR') or '/tmp'
TTL_SEC = 24 * 60 * 60
now = time.time()
try:
    entries = os.listdir(tmp_root)
except Exception:
    entries = []
for entry in entries:
    if not entry.startswith('shadowfrog-hook-'):
        continue
    p = os.path.join(tmp_root, entry)
    try:
        if (now - os.path.getmtime(p)) > TTL_SEC:
            shutil.rmtree(p, ignore_errors=True)
    except Exception:
        pass
PYEOF

# Check staleness. Git work is bounded with per-call subprocess timeouts so a
# large/locked repo can't exceed the hook budget. Timeouts sum to 2.0s,
# leaving >=3s headroom under timeoutSec=5. Any failure -> no warning.
STALE_MSG=""
CHANGED=$(python3 - <<'PYEOF' 2>/dev/null || echo ""
import json, subprocess

def git(args, timeout):
    return subprocess.run(["git"] + args, capture_output=True, text=True, timeout=timeout)

try:
    last = json.load(open(".shadow/_meta/state.json")).get("last_commit", "none")
    head = git(["rev-parse", "HEAD"], 0.5).stdout.strip()
    if last and last != "none" and last != head \
            and git(["rev-parse", "--verify", last], 0.5).returncode == 0:
        r = git(["diff", "--name-only", last, "HEAD", "--", ":!.shadow"], 1.0)
        n = len([ln for ln in r.stdout.splitlines() if ln.strip()])
        if n > 0:
            print(n)
except Exception:
    pass
PYEOF
)
if [ -n "$CHANGED" ]; then
    STALE_MSG=" WARNING: ${CHANGED} file(s) changed since last update — consider running /shadow-frog-update."
fi

# Read top preferences
PREFS=""
if [ -f ".shadow/_prefs.md" ]; then
    PREFS=$(grep '^\- ' .shadow/_prefs.md 2>/dev/null | head -3 | sed 's/"/\\"/g' | tr '\n' ' ' || echo "")
fi

# Output JSON — additionalContext gets injected into the conversation
export SF_FILES="$TOTAL_FILES"
export SF_DISC="$TOTAL_DISCOVERIES"
export SF_UPDATED="$LAST_UPDATE"
export SF_STALE="$STALE_MSG"
export SF_PREFS="$PREFS"
python3 << 'PYEOF' 2>/dev/null
import json, os

files = os.environ.get("SF_FILES", "0")
disc = os.environ.get("SF_DISC", "0")
updated = os.environ.get("SF_UPDATED", "unknown")
stale = os.environ.get("SF_STALE", "")
prefs = os.environ.get("SF_PREFS", "")

parts = [
    f"[ShadowFrog] Shadow loaded — {files} files, {disc} discoveries, last updated {updated}.",
    stale,
    "Before editing any file, check .shadow/<filepath>.md for known bugs, edge cases, and implicit contracts.",
    "Read .shadow/_prefs.md for project conventions the user wants followed.",
]
if prefs:
    parts.append(f"Top preferences: {prefs}")

ctx = " ".join(p for p in parts if p)
# Emit both shapes: top-level `additionalContext` (Copilot CLI) and the
# nested `hookSpecificOutput` form (Claude Code). Each agent reads its own
# key and ignores the other, so one payload drives both platforms.
print(json.dumps({
    "additionalContext": ctx,
    "hookSpecificOutput": {"hookEventName": "SessionStart", "additionalContext": ctx},
}))
PYEOF
