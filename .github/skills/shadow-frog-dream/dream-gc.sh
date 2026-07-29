#!/usr/bin/env bash
# Dream worktree garbage collector — sweep ORPHAN worktrees from the base.
#
# Usage:
#   dream-gc.sh [--repo-root DIR] [--min-age-min N] [--dry-run] [--quiet]
#   dream-gc.sh --task-complete --namespace NS [--repo-root DIR] [--min-age-min N]
#
# Defense-in-depth complement to dream-cleanup.sh: even when individual
# `dream-cleanup.sh` calls fail (e.g. machine crash, OOM-killed agent),
# this sweeper finds and removes orphan dream worktrees that have outlived
# their git registration. Safe to cron / run manually.
#
# IMPORTANT: `--task-complete` is always namespace-scoped (refuses without
# `--namespace`). Default orphan-only mode walks the whole base, which is
# safe because it only sweeps dirs whose `.git` pointer is already broken.
#
# A directory under $DREAM_WORKTREE_BASE/<ns>/dream-<slug>/ is an "orphan"
# when BOTH of these hold:
#   (a) It is older than --min-age-min minutes (default: 10) by mtime.
#       Avoids racing with a worktree being created RIGHT NOW.
#   (b) Its git registration is broken: either `.git` is missing, OR the
#       `.git` file points at a `gitdir:` path that no longer exists.
#
# Every candidate is then re-validated through `_worktree_safety.py` before
# removal. This script can NEVER rm a path that doesn't match the
# `<base>/<ns>/dream-<slug>` shape, even if the base is misconfigured.
#
# Flags:
#   --repo-root DIR     Where the bare repo lives (for `git worktree prune`
#                       at the end). Default: $REPO_ROOT, then $PWD.
#   --min-age-min N     Only consider dirs whose MTIME is older than N
#                       minutes (default: 10). NOT a liveness check — an
#                       active dream that hasn't written to disk in N
#                       minutes is still eligible.
#   --dry-run           Print what would be removed; remove nothing.
#   --quiet, -q         Suppress progress output (errors still print).
#   --task-complete     Sweep registered-but-stale dream-* dirs too (not
#                       just orphans), in the named namespace ONLY.
#                       REQUIRES --namespace. For each candidate,
#                       `git worktree remove --force` runs first; if git
#                       refuses (e.g. the worktree is `git worktree
#                       lock`'d), we WARN and skip — we do NOT fall back
#                       to `rm -rf` for registered candidates, since git's
#                       refusal is a liveness signal we must respect.
#   --namespace NS, -n NS
#                       Required for `--task-complete`. Restricts the
#                       sweep to `<base>/<ns>/`. Default source:
#                       $DREAM_NAMESPACE env. No auto-derivation from
#                       REPO_ROOT — that could silently sweep the wrong
#                       namespace if REPO_ROOT came from cwd inference.
#   --help, -h          Show this help message.
#
# Environment:
#   DREAM_WORKTREE_BASE  Base path to sweep (default: /tmp/shadowfrog-dreams).
#                        Refuses sensitive bases (/, /tmp, /home, $HOME, …).
#
# Exit codes:
#   0 → sweep completed (anything from 0..N worktrees removed)
#   1 → base path is unsafe to sweep (no removal attempted)
#   2 → usage error
#   4 → safety module (_worktree_safety.py) is missing

set -euo pipefail

show_help() {
    sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
}

MIN_AGE_MIN=10
DRY_RUN=false
QUIET=false
TASK_COMPLETE=false
REPO_ROOT_OVERRIDE=""
NAMESPACE_OVERRIDE=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --repo-root) REPO_ROOT_OVERRIDE="$2"; shift 2 ;;
        --min-age-min) MIN_AGE_MIN="$2"; shift 2 ;;
        --dry-run) DRY_RUN=true; shift ;;
        --quiet|-q) QUIET=true; shift ;;
        --task-complete) TASK_COMPLETE=true; shift ;;
        --namespace|-n) NAMESPACE_OVERRIDE="$2"; shift 2 ;;
        --help|-h) show_help ;;
        *) echo "ERROR: unknown flag: $1" >&2; exit 2 ;;
    esac
done

# Validate --min-age-min is a non-negative integer (prevents shell injection
# via the `find -mmin +N` arg).
if ! [[ "$MIN_AGE_MIN" =~ ^[0-9]+$ ]]; then
    echo "ERROR: --min-age-min must be a non-negative integer (got: $MIN_AGE_MIN)" >&2
    exit 2
fi

# --- Resolve namespace (REQUIRED when --task-complete is set) ---
# No auto-derivation from `basename "$REPO_ROOT"` — REPO_ROOT can come
# from cwd inference, so that fallback could silently sweep the wrong ns.
NAMESPACE="${NAMESPACE_OVERRIDE:-${DREAM_NAMESPACE:-}}"
if [[ "$TASK_COMPLETE" == true ]]; then
    if [[ -z "$NAMESPACE" ]]; then
        echo "ERROR: --task-complete requires --namespace NS (or DREAM_NAMESPACE env)" >&2
        echo "       Refusing to sweep registered worktrees across all namespaces." >&2
        exit 2
    fi
    # First char non-`.` to reject bare `.`/`..` (depth-1 + dream-* basename +
    # _worktree_safety.py already defend in depth; this just makes intent clear).
    if ! [[ "$NAMESPACE" =~ ^[A-Za-z0-9_-][A-Za-z0-9._-]*$ ]]; then
        echo "ERROR: --namespace must match [A-Za-z0-9_-][A-Za-z0-9._-]* (got: $NAMESPACE)" >&2
        exit 2
    fi
fi

# Validate --min-age-min as a non-negative integer. We need this before the
# find branching below: `0` means "no age gate" (omit -mmin entirely) while
# any positive N maps to `-mmin +N`. Without this check, a non-integer would
# silently flow to find and bypass age gating.
if ! [[ "$MIN_AGE_MIN" =~ ^[0-9]+$ ]]; then
    echo "ERROR: --min-age-min must be a non-negative integer (got: $MIN_AGE_MIN)" >&2
    exit 2
fi

say() { [[ "$QUIET" == true ]] || echo "$@"; }

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SAFETY="$SCRIPT_DIR/_worktree_safety.py"
BASE="${DREAM_WORKTREE_BASE:-/tmp/shadowfrog-dreams}"

# --- Pre-flight: safety module must exist ---
# A missing `_worktree_safety.py` makes `python3` exit 2 (same code as
# "missing path"); without this guard the probe + per-candidate gate would
# both fail in non-distinguishable ways. Refuse loudly.
if [[ ! -f "$SAFETY" ]]; then
    echo "ERROR: safety module not found: $SAFETY" >&2
    echo "       refusing to sweep without a safety gate." >&2
    exit 4
fi

# --- Refuse upfront if the base itself is unsafe ---
# Use a sentinel path to probe the base: `<base>/__probe__/dream-_probe`
# violates the shape only if BASE itself is sensitive (rule 4 fires first).
# A successful gate on a real path implies BASE is non-sensitive.
PROBE="$BASE/__probe__/dream-_probe_"
probe_rc=0
python3 "$SAFETY" "$PROBE" "$BASE" >/dev/null 2>&1 || probe_rc=$?
case "$probe_rc" in
    0|2) ;;   # gate passed (path-exists or path-missing both fine for probe)
    1)
        echo "ERROR: dream-gc.sh refuses to sweep base '$BASE'" >&2
        echo "       (sensitive root, or fails safety check — set DREAM_WORKTREE_BASE)" >&2
        exit 1
        ;;
    *)
        echo "ERROR: safety gate returned unexpected code $probe_rc for base '$BASE'" >&2
        exit 1
        ;;
esac

# Nothing to sweep if base doesn't exist (idempotent no-op).
if [[ ! -d "$BASE" ]]; then
    say "Base does not exist (nothing to sweep): $BASE"
    exit 0
fi

# --- Resolve repo root for the final `git worktree prune` ---
REPO_ROOT="${REPO_ROOT_OVERRIDE:-${REPO_ROOT:-}}"
if [[ -z "$REPO_ROOT" ]]; then
    REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
fi

# Helper: is $1 a usable git repo root (regular OR worktree OR bare)?
_is_git_root() {
    [[ -n "${1:-}" ]] && git -C "$1" rev-parse --git-dir >/dev/null 2>&1
}

say "Sweeping dream worktree base: $BASE"
say "  min age: ${MIN_AGE_MIN} minutes"
if [[ "$TASK_COMPLETE" == true ]]; then
    say "  TASK-COMPLETE MODE — sweeping registered worktrees in namespace '$NAMESPACE' only"
fi
[[ "$DRY_RUN" == true ]] && say "  DRY RUN — no removal"

# --- Enumerate candidates ---
# Shape: $BASE/<ns>/dream-<slug>. We use `find` to keep this fast on large
# bases. `-mindepth 2 -maxdepth 2` matches exactly that level.
# `-mmin +N` requires modification time older than N minutes (avoids racing
# with a fresh `dream-setup.sh` mid-creation).
removed=0
kept=0
refused=0

# NUL-delimited to handle exotic chars even though SAFE_RE forbids them.
while IFS= read -r -d '' candidate; do
    # Only consider dirs whose leaf starts with "dream-".
    [[ "$(basename "$candidate")" == dream-* ]] || continue

    # Re-validate via the safety gate. This guarantees the candidate matches
    # `<base>/<ns>/dream-<slug>` exactly.
    gate_rc=0
    python3 "$SAFETY" "$candidate" "$BASE" >/dev/null 2>&1 || gate_rc=$?
    if [[ "$gate_rc" -ne 0 ]]; then
        say "  refused (gate): $candidate"
        refused=$((refused + 1))
        continue
    fi

    # Orphan check: missing .git OR broken gitdir pointer.
    # In --task-complete mode we ALSO sweep registered (non-orphan) dirs,
    # so the orphan check becomes informational rather than a gate.
    git_path="$candidate/.git"
    is_orphan=false
    if [[ ! -e "$git_path" ]]; then
        is_orphan=true
    elif [[ -f "$git_path" ]]; then
        # `.git` is a file (the standard worktree layout). Parse the
        # `gitdir:` line robustly:
        #   - sed strips ONLY the `gitdir:` prefix + leading whitespace,
        #     preserving any `:` chars in the rest of the path.
        #   - `tr -d '\r'` tolerates CRLF line endings.
        #   - `head -1` defends against multi-line files (only first matters).
        # Earlier `awk -F': *'` truncated on every `:`, so a path like
        # `/repo:with-colon/.git/...` was misclassified as orphan and the
        # live worktree would be deleted.
        gitdir_target="$(sed -n 's|^gitdir:[[:space:]]*||p' "$git_path" 2>/dev/null | head -1 | tr -d '\r' || true)"
        if [[ -z "$gitdir_target" ]]; then
            is_orphan=true
        else
            # Relative gitdir paths (rare but legal) resolve relative to the
            # .git file's directory — NOT the cwd.
            if [[ "$gitdir_target" != /* ]]; then
                gitdir_target="$candidate/$gitdir_target"
            fi
            if [[ ! -e "$gitdir_target" ]]; then
                is_orphan=true
            fi
        fi
    fi

    # Decide whether to sweep this candidate.
    if [[ "$is_orphan" != true ]] && [[ "$TASK_COMPLETE" != true ]]; then
        kept=$((kept + 1))
        continue
    fi

    label="orphan"
    [[ "$is_orphan" != true ]] && label="stale-registered"

    # Action: dry-run logs, real run removes.
    if [[ "$DRY_RUN" == true ]]; then
        say "  WOULD REMOVE ($label): $candidate"
        removed=$((removed + 1))
        continue
    fi

    say "  removing $label: $candidate"

    # For registered worktrees, try git's polite path first so its
    # bookkeeping is cleaned up too. Capture stderr to distinguish
    # success from refusal — locked worktrees MUST NOT be force-deleted
    # via the rm fallback.
    cleaned=false
    git_stderr=""
    if [[ "$is_orphan" != true ]] && _is_git_root "$REPO_ROOT"; then
        git_stderr="$(git -C "$REPO_ROOT" worktree remove "$candidate" --force 2>&1 >/dev/null || true)"
        if [[ -z "$git_stderr" ]]; then
            cleaned=true
        fi
    fi

    if [[ "$cleaned" != true ]] && [[ -d "$candidate" || -L "$candidate" ]]; then
        if [[ "$is_orphan" == true ]]; then
            # Orphan: `.git` already broken, no ownership concern.
            if rm -rf -- "$candidate"; then
                cleaned=true
            fi
        else
            # Registered worktree git refused to remove (locked, wrong
            # repo, REPO_ROOT unset). DO NOT fall back to rm -rf — git's
            # refusal is a liveness signal.
            if [[ -n "$git_stderr" ]]; then
                echo "  WARN: git refused to remove registered worktree: $candidate" >&2
                echo "        ($git_stderr)" >&2
            else
                echo "  WARN: no usable REPO_ROOT — skipping registered worktree: $candidate" >&2
            fi
            refused=$((refused + 1))
            continue
        fi
    fi

    if [[ "$cleaned" == true ]]; then
        removed=$((removed + 1))
    else
        echo "  ERROR: failed to remove '$candidate'" >&2
        refused=$((refused + 1))
    fi
done < <(
    if [[ "$TASK_COMPLETE" == true ]]; then
        # Namespace-scoped: silently no-op if the ns subtree is missing.
        # mindepth/maxdepth 1 matches dream-* one level below the ns dir
        # (the walk root is the ns dir itself).
        # MIN_AGE_MIN=0 omits -mmin entirely: -mmin +0 means older-than-0
        # minutes, which still EXCLUDES files modified in the last ~1
        # minute. Without this special case the end-of-session sweep would
        # silently miss the freshly-pushed final batch it must catch.
        if [[ -d "$BASE/$NAMESPACE" ]]; then
            if [[ "$MIN_AGE_MIN" -gt 0 ]]; then
                find "$BASE/$NAMESPACE" -mindepth 1 -maxdepth 1 -type d -mmin "+$MIN_AGE_MIN" -print0
            else
                find "$BASE/$NAMESPACE" -mindepth 1 -maxdepth 1 -type d -print0
            fi
        fi
    else
        # Default orphan-only mode walks the whole base. Safe because the
        # orphan gate (.git missing or pointer broken) cannot fire on live
        # sibling-repo worktrees. Same MIN_AGE_MIN=0 special case.
        if [[ "$MIN_AGE_MIN" -gt 0 ]]; then
            find "$BASE" -mindepth 2 -maxdepth 2 -type d -mmin "+$MIN_AGE_MIN" -print0
        else
            find "$BASE" -mindepth 2 -maxdepth 2 -type d -print0
        fi
    fi
)

say "Summary: removed=$removed kept=$kept refused=$refused"

# --- Prune stale worktree refs (in case our rm beat git's bookkeeping) ---
if [[ "$DRY_RUN" != true ]] && _is_git_root "$REPO_ROOT"; then
    git -C "$REPO_ROOT" worktree prune 2>/dev/null || true
fi

exit 0
