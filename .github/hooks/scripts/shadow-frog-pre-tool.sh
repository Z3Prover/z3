#!/usr/bin/env bash
# Hook: preToolUse — always remind agent to consult the shadow knowledge base
# Outputs JSON with additionalContext before every tool execution.
# Includes file-specific hints for edit/create and staleness warnings when behind.
#
# When a mutation tool (edit/create/str_replace/write) targets a file with
# a shadow that has actionable discoveries (bug/security labels), the
# top entries are inlined into additionalContext via
# shadow-viewer.py --top. Per-session dedup ensures the same file's
# content is injected at most once per Copilot CLI process.

# This hook is ADVISORY — it only injects shadow context, it is NOT a security
# gate. Copilot CLI >= 1.0.57 treats a non-zero preToolUse exit as a DENY of the
# user's tool call, so this script MUST run fail-open under every condition.
#
# Defense in depth:
#   1. No `set -e`/`-u`/`pipefail` — a failing sub-step doesn't abort the script.
#   2. trap on EXIT — converts clean non-zero exits to 0.
#   3. trap on TERM/HUP/INT — converts runner-initiated signal kills to 0.
#      (bash 3.2+ on macOS and bash 5+ on Linux verified: EXIT alone is NOT
#      enough — SIGTERM still produces exit 143/-15 without a TERM trap.)
#   4. Every external call (git, python3, shadow-viewer.py) MUST be wrapped in
#      a bounded subprocess timeout. If the foreground child hangs, bash will
#      queue the signal until the child returns, so the trap can't save us
#      unless boundedness holds. CI enforces this via .github/workflows/shellcheck.yml.
#   5. Total bounded work budget is ~3.5s, leaving >=1.5s headroom under the
#      hook's 5s timeoutSec configured in shadow-frog-hooks.json.
trap 'exit 0' EXIT
trap 'exit 0' TERM HUP INT PIPE

# Defensive PATH — some runners launch hooks with a stripped PATH (observed
# under sandboxed containers). Append the standard binary dirs so cat,
# python3, and git remain findable. We APPEND (not prepend) to honor any
# custom paths the runner exported intentionally. Without this, bash itself
# emits `cat: No such file or directory` to stderr.
PATH="${PATH:+$PATH:}/usr/local/bin:/usr/bin:/bin"
export PATH

# Wrap in a brace group so bash's own "ignored null byte in input" warning
# (emitted by bash 5+ when command substitution captures NULs) is silenced
# alongside cat's stderr.
{ INPUT=$(cat 2>/dev/null || echo ""); } 2>/dev/null

[ ! -d ".shadow" ] && exit 0

# Base reminder (always injected — agent decides whether to act on it).
# Kept terse: this fires on every tool call, so every char counts against
# the per-call prompt budget. Details live in /shadow-frog.
MSG="[ShadowFrog] .shadow/ mirrors the repo (src/x.py -> .shadow/src/x.py.md). Check before edits; capture user-shared knowledge as source: user; preferences -> .shadow/_prefs.md. /shadow-frog"

# Extract tool name + target file in ONE python3 invocation (instead of two
# separate `python3 -c` calls). Single startup cost; smaller blast radius if
# python3 is slow/broken. Output is two pipe-separated values on stdout:
#   <lowercase_tool_name>|<target_file_path>
# Support both Copilot CLI (camelCase fields, lowercase tool names like
# `edit`/`create`/`str_replace`/`write`) and Claude Code (snake_case fields,
# PascalCase tool names like `Edit`/`Write`/`MultiEdit`/`NotebookEdit`).
# Normalize tool name to lowercase so one case statement handles both.
# Prefer `file_path` over `path` — both Copilot CLI and Claude Code use
# `file_path` as the canonical key; `path` is a less-common alias. When both
# are present, `file_path` wins.
TOOL_INFO=$(echo "$INPUT" | python3 -c "
import json, sys
try:
    d = json.load(sys.stdin)
except Exception:
    d = {}
if not isinstance(d, dict):
    d = {}
name = (d.get('toolName') or d.get('tool_name') or '')
if not isinstance(name, str):
    name = ''
args = d.get('toolInput') or d.get('tool_input') or d.get('toolArgs') or d.get('tool_args') or {}
target = ''
if isinstance(args, dict):
    target = args.get('file_path') or args.get('path') or ''
    if not isinstance(target, str):
        target = ''
# Strip NUL and newline bytes — bash 5+ warns when command substitution
# captures NULs, and a newline in target would break the pipe-delimited
# output format on parse. These bytes never appear in legitimate tool
# names or file paths; an adversarial JSON \u0000 escape is the only way
# they reach this point.
def _scrub(s):
    return s.replace('\x00', '').replace('\n', '').replace('\r', '')
print(_scrub(name).lower() + '|' + _scrub(target))
" 2>/dev/null || echo "|")
TOOL_NAME="${TOOL_INFO%%|*}"
TARGET_FILE="${TOOL_INFO#*|}"
case "$TOOL_NAME" in
    edit|create|str_replace|write|multiedit|notebookedit)
        IS_MUTATION=1
        ;;
    *)
        IS_MUTATION=0
        ;;
esac

if [ "$IS_MUTATION" = "1" ]; then
    # Oversized path → fall back to base reminder. A 200KB path took
    # ~5.3s in benchmarks, exceeding the production deny threshold. Real
    # file paths are well under 1KB; anything larger is malformed or
    # adversarial. The base reminder still fires.
    if [ -n "$TARGET_FILE" ] && [ "${#TARGET_FILE}" -le 1024 ]; then
        # CWD is where .shadow/ lives (verified above). Compute the
        # file's path relative to CWD. This works for both
        # at-repo-root and subdirectory shadow setups (e.g.,
        # examples/coupon-demo within a parent monorepo).
        CWD=$(pwd)
        REL_PATH="${TARGET_FILE#"$CWD"/}"
        SHADOW_FILE=".shadow/${REL_PATH}.md"
        if [ -f "$SHADOW_FILE" ]; then
                # Default pointer message if --top is unavailable or empty
                MSG="[ShadowFrog] .shadow/${REL_PATH}.md has discoveries — check before changes. Capture user-shared knowledge as source: user. /shadow-frog"

                # Per-session dedup — keyed on PPID + parent process start time so the
                # bucket doesn't collide across (a) PID-wrap on long-running systems,
                # (b) Claude Code sessions sharing PPID=1 under a process manager, or
                # (c) different shells of the same user transiently sharing PPID. Falls
                # back to PPID alone if `ps` is unavailable (some sandboxed containers).
                # Hooks must remain pure-read w.r.t. .shadow/, so the
                # dedup marker stays outside the shadow tree.
                TMP_ROOT="${SHADOWFROG_TMP_DIR:-/tmp}"
                PARENT_START=$(ps -p "$PPID" -o lstart= 2>/dev/null | tr -d ' :' || echo "")
                SESSION_KEY="${PPID}${PARENT_START:+-${PARENT_START}}"
                DEDUP_DIR="${TMP_ROOT}/shadowfrog-hook-${SESSION_KEY}"
                mkdir -p "$DEDUP_DIR" 2>/dev/null || true
                SAFE_PATH=$(echo "$REL_PATH" | tr '/' '_' | tr -cd '[:alnum:]_.-')
                DEDUP_FILE="${DEDUP_DIR}/${SAFE_PATH}.injected"

                if [ ! -f "$DEDUP_FILE" ]; then
                    SCRIPT_DIR=""
                    if [ -n "$0" ]; then
                        SCRIPT_DIR="$(cd "$(dirname "$0")" 2>/dev/null && pwd -P)" || SCRIPT_DIR=""
                    fi
                    # Resolve viewer + run it inside ONE Python block. Every
                    # external call (git rev-parse, viewer subprocess) is
                    # bounded with subprocess.run(timeout=...) so a hung git
                    # or hung viewer can't blow the hook's 5s budget — even
                    # the trap pyramid can't help if bash is blocked waiting
                    # on an unbounded foreground child (signals are queued).
                    # Total bounded work here is ~1.5s (rev-parse 0.5s + viewer 1.0s).
                    TOP_OUTPUT=$(SF_SCRIPT_DIR="$SCRIPT_DIR" SF_REL_PATH="$REL_PATH" python3 - <<'PYEOF' 2>/dev/null || true
import os, subprocess, sys

script_dir = os.environ.get('SF_SCRIPT_DIR', '')
rel_path = os.environ.get('SF_REL_PATH', '')

def _git(args, timeout):
    try:
        r = subprocess.run(['git'] + args, capture_output=True, text=True, timeout=timeout)
        if r.returncode == 0:
            return r.stdout.strip()
    except Exception:
        pass
    return ''

# Locate shadow-viewer.py. Order:
#   1. Script-relative — works for source repo dev AND project installs
#      (hooks at .github/hooks/scripts/ co-located with .github/skills/).
#   2-3. Parent repo's .github/ or .claude/ skills — useful when the hook
#      is run from a subdir of a monorepo with an installed parent.
repo_root = _git(['rev-parse', '--show-toplevel'], 0.5)

candidates = []
if script_dir:
    candidates.append(os.path.join(script_dir, '..', '..', 'skills', 'shadow-frog-viewer', 'shadow-viewer.py'))
if repo_root:
    candidates.append(os.path.join(repo_root, '.github', 'skills', 'shadow-frog-viewer', 'shadow-viewer.py'))
    candidates.append(os.path.join(repo_root, '.claude', 'skills', 'shadow-frog-viewer', 'shadow-viewer.py'))

viewer = ''
for candidate in candidates:
    if os.path.isfile(candidate):
        viewer = candidate
        break

if viewer:
    try:
        r = subprocess.run(
            ['python3', viewer,
             '--shadow-dir', '.shadow',
             '--top', rel_path,
             '--top-labels', 'bug,security',
             '--top-limit', '3',
             '--top-max-chars', '600'],
            capture_output=True, text=True, timeout=1.0,
        )
        if r.returncode == 0:
            sys.stdout.write(r.stdout.strip())
    except Exception:
        pass
PYEOF
)
                    # Only inline when the viewer produced an actionable
                    # response (non-empty and not the "no discoveries" sentinel).
                    if [ -n "$TOP_OUTPUT" ] && [[ "$TOP_OUTPUT" != "No actionable"* ]]; then
                        MSG="[ShadowFrog] Actionable discoveries for ${REL_PATH} (verify against source before acting):
${TOP_OUTPUT}
Capture user-shared knowledge as source: user. /shadow-frog"
                        touch "$DEDUP_FILE" 2>/dev/null || true
                    fi
                fi
        fi
    fi
fi

# Staleness warning (appended when shadow is behind HEAD).
# All git work is bounded with per-call subprocess timeouts so a huge/locked
# repo can't blow past the hook's 5s budget. Timeouts sum to 2.0s here,
# matched with the viewer's ~1.5s above + bash overhead = ~4s worst case,
# leaving 1s headroom under timeoutSec=5. Any failure/timeout -> no warning.
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
    MSG="${MSG} Shadow is behind HEAD — ${CHANGED} file(s) changed since last update. Run /shadow-frog-update when ready."
fi

export SF_MSG="$MSG"
# Emit both shapes: top-level `additionalContext` (Copilot CLI) and the
# nested `hookSpecificOutput` form (Claude Code). Each agent reads its own
# key and ignores the other.
python3 -c "import json,os; ctx=os.environ['SF_MSG']; print(json.dumps({'additionalContext': ctx, 'hookSpecificOutput': {'hookEventName': 'PreToolUse', 'additionalContext': ctx}}))" 2>/dev/null || true

exit 0
