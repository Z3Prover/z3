#!/usr/bin/env bash
# Dream worktree cleanup — safe removal of ONE dream worktree.
#
# Usage:
#   dream-cleanup.sh <worktree-dir> [--repo-root DIR] [--quiet]
#
# Replaces the previous inline shell snippet:
#   git worktree remove "$WORKTREE_DIR" --force 2>/dev/null
#   git worktree prune
# which silently leaked the worktree directory whenever `git worktree remove`
# failed (the `2>/dev/null` swallowed the error AND the next prune only
# cleared git's bookkeeping — not the directory on disk).
#
# This script first tries the polite path (`git worktree remove --force`),
# and ONLY if git fails AND the path passes a strict safety gate, falls back
# to `rm -rf`. The safety gate is enforced by `_worktree_safety.py` (see
# that module for the full rule set).
#
# This script is INTERACTIVE (run by the dream agent) so it FAILS FAST on
# bad input — unlike the always-exit-0 hook scripts. Exit codes:
#   0 → worktree removed (or never existed)
#   1 → safety gate refused the path (no removal attempted)
#   2 → usage error
#   3 → fallback rm -rf itself failed
#   4 → safety module (_worktree_safety.py) is missing
#
# Flags:
#   --repo-root DIR   Where to invoke `git worktree remove` from.
#                     If omitted, falls back to $REPO_ROOT env var, then
#                     derives from the worktree's `.git` pointer
#                     (rev-parse --git-common-dir).
#   --quiet           Suppress progress output (errors still print).
#   --help, -h        Show this help message.
#
# Environment:
#   DREAM_WORKTREE_BASE  Override the base path the safety gate checks
#                        against (default: /tmp/shadowfrog-dreams).

set -euo pipefail

show_help() {
    sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
}

WORKTREE_DIR=""
REPO_ROOT_OVERRIDE=""
QUIET=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --repo-root) REPO_ROOT_OVERRIDE="$2"; shift 2 ;;
        --quiet|-q) QUIET=true; shift ;;
        --help|-h) show_help ;;
        --*) echo "ERROR: unknown flag: $1" >&2; exit 2 ;;
        *)
            if [[ -z "$WORKTREE_DIR" ]]; then
                WORKTREE_DIR="$1"; shift
            else
                echo "ERROR: unexpected positional arg: $1" >&2; exit 2
            fi
            ;;
    esac
done

if [[ -z "$WORKTREE_DIR" ]]; then
    echo "ERROR: <worktree-dir> is required" >&2
    echo "Usage: dream-cleanup.sh <worktree-dir> [--repo-root DIR] [--quiet]" >&2
    exit 2
fi

say() { [[ "$QUIET" == true ]] || echo "$@"; }

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SAFETY="$SCRIPT_DIR/_worktree_safety.py"
BASE="${DREAM_WORKTREE_BASE:-/tmp/shadowfrog-dreams}"

# --- Pre-flight: safety module must exist ---
# If `_worktree_safety.py` is missing, `python3` itself exits 2 — the same
# code the gate uses for "safe but path missing". Detect this BEFORE
# invoking python so a missing module fails loudly instead of silently
# pretending nothing needs cleanup (which would re-introduce the leak
# this script exists to fix).
if [[ ! -f "$SAFETY" ]]; then
    echo "ERROR: safety module not found: $SAFETY" >&2
    echo "       refusing to operate without a safety gate." >&2
    exit 4
fi

# --- SAFETY GATE — enforced BEFORE any destructive action ---
# Exit codes from _worktree_safety.py:
#   0 = safe AND path exists (we proceed)
#   2 = safe AND path missing (idempotent no-op — exit 0)
#   1 = refused (we abort)
guard_rc=0
python3 "$SAFETY" "$WORKTREE_DIR" "$BASE" || guard_rc=$?
case "$guard_rc" in
    0) ;;
    2) say "Nothing to clean (path doesn't exist): $WORKTREE_DIR"; exit 0 ;;
    1)
        echo "ERROR: dream-cleanup.sh refuses to operate on '$WORKTREE_DIR'" >&2
        echo "       (base=$BASE — see _worktree_safety.py for rules)" >&2
        exit 1
        ;;
    *)
        echo "ERROR: safety gate returned unexpected code $guard_rc for '$WORKTREE_DIR'" >&2
        exit 1
        ;;
esac

# --- Resolve repo root (where the bare repo lives) for `git worktree …` ---
# Precedence: --repo-root flag > $REPO_ROOT env var > worktree's gitdir.
# Parameter expansion preserves env-inherited REPO_ROOT instead of
# clobbering it (the previous unconditional assignment lost env values).
REPO_ROOT="${REPO_ROOT_OVERRIDE:-${REPO_ROOT:-}}"
# Fall back to the dream worktree's recorded gitdir when --repo-root and
# $REPO_ROOT are both absent. A dead worktree (broken .git pointer) will
# fail this — that's fine, we'll just skip the git step and rm -rf below.
if [[ -z "$REPO_ROOT" ]] && [[ -e "$WORKTREE_DIR/.git" ]]; then
    REPO_ROOT="$(git -C "$WORKTREE_DIR" rev-parse --show-superproject-working-tree 2>/dev/null || true)"
    if [[ -z "$REPO_ROOT" ]]; then
        # Single-repo case: superproject is empty; derive from common-dir.
        COMMON_DIR="$(git -C "$WORKTREE_DIR" rev-parse --git-common-dir 2>/dev/null || true)"
        if [[ -n "$COMMON_DIR" ]]; then
            REPO_ROOT="$(cd "$COMMON_DIR/.." 2>/dev/null && pwd || true)"
        fi
    fi
fi

# Helper: is $1 a usable git repo root (regular OR worktree OR bare)?
# `-d .git` was too strict — when REPO_ROOT is itself a worktree, `.git`
# is a file, not a directory, and we'd silently skip the polite git path.
_is_git_root() {
    [[ -n "${1:-}" ]] && git -C "$1" rev-parse --git-dir >/dev/null 2>&1
}

# --- Step 1: try `git worktree remove --force` (lets git clean its bookkeeping) ---
git_cleaned=false
if _is_git_root "$REPO_ROOT"; then
    if git -C "$REPO_ROOT" worktree remove "$WORKTREE_DIR" --force 2>/dev/null; then
        git_cleaned=true
        say "Removed via git worktree: $WORKTREE_DIR"
    fi
fi

# --- Step 2: fallback rm -rf (only because safety gate passed) ---
# The gate enforces: absolute path, strictly under $DREAM_WORKTREE_BASE,
# exact `<base>/<ns>/dream-<slug>` shape, every component matches SAFE_RE.
# We re-check existence in case `git worktree remove` actually succeeded
# (some failure-modes of git's exit code don't reflect rm success).
if [[ "$git_cleaned" != true ]] && [[ -d "$WORKTREE_DIR" || -L "$WORKTREE_DIR" ]]; then
    say "git worktree remove failed (or no repo-root) — rm -rf fallback: $WORKTREE_DIR"
    if rm -rf -- "$WORKTREE_DIR"; then
        say "Removed: $WORKTREE_DIR"
    else
        echo "ERROR: rm -rf '$WORKTREE_DIR' failed" >&2
        exit 3
    fi
fi

# --- Step 3: prune stale worktree refs (cheap, safe, no-op if nothing stale) ---
if _is_git_root "$REPO_ROOT"; then
    git -C "$REPO_ROOT" worktree prune 2>/dev/null || true
fi

exit 0
