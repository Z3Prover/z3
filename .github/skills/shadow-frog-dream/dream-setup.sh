#!/usr/bin/env bash
# Dream experiment setup — creates worktree and exports environment.
#
# Usage:
#   eval "$(dream-setup.sh --slug t01-csv-fuzzer)" || { echo "setup failed" >&2; exit 1; }
#   eval "$(dream-setup.sh --slug t03-extend --base-branch dream/ns/20250612-143012Z-csv-fuzzer)" || exit 1
#
# IMPORTANT: ALWAYS check the exit status of `eval` — on failure this script
# prints to stderr and exits non-zero, which `eval "$(...)"` cannot detect on
# its own. Without `|| exit 1` the agent silently proceeds with empty env vars.
#
# Why `eval` is safe HERE (do not cargo-cult it elsewhere): this script never
# echoes untrusted input back. All inputs (slug/namespace) are validated
# against [A-Za-z0-9_-][A-Za-z0-9._-]* before use, and every exported value is
# shell-escaped with `printf %q`, so the emitted text is a fixed set of safe
# `export` lines. Only `eval` output you produced under these guarantees.
#
# This script:
#   1. Validates inputs (slug/namespace) against [A-Za-z0-9_-][A-Za-z0-9._-]*
#      (non-`.` first char rejects bare `.`/`..`) to prevent shell-metachar
#      injection through the eval contract
#   2. Computes DREAM_ID, BRANCH_NAME, WORKTREE_DIR, BASE_COMMIT
#   3. Creates the worktree (idempotent — cleans existing if found)
#   4. Prints export statements (values shell-escaped via printf %q)
#
# Flags:
#   --slug NAME        Task slug (required, e.g., "t01-csv-fuzzer")
#   --base-branch REF  Branch to base from (default: default branch = fresh)
#   --namespace NS     Override DREAM_NAMESPACE (default: env or repo basename)
#   --repo-root DIR    Override repo root (default: git rev-parse)
#   --print-env        Print export statements (default behavior)
#   --print-json       Print JSON instead of shell exports
#   --dry-run          Compute values without creating worktree
#   --help, -h         Show this help message
#
# Design decisions:
#   - Idempotent: re-running with same slug cleans and recreates
#   - External path: worktrees always in /tmp/shadowfrog-dreams/<NS>/
#   - Validates worktree is NOT inside project directory
#   - Detects default branch (main/master) automatically
#   - Resolves DREAM_NAMESPACE from env > TASK_INFO.json > .env > repo name

set -euo pipefail

# --- Argument parsing ---
SLUG=""
BASE_BRANCH=""
NAMESPACE_OVERRIDE=""
REPO_ROOT_OVERRIDE=""
OUTPUT_MODE="env"
DRY_RUN=false

show_help() {
    sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --slug) SLUG="$2"; shift 2 ;;
        --base-branch) BASE_BRANCH="$2"; shift 2 ;;
        --namespace) NAMESPACE_OVERRIDE="$2"; shift 2 ;;
        --repo-root) REPO_ROOT_OVERRIDE="$2"; shift 2 ;;
        --print-json) OUTPUT_MODE="json"; shift ;;
        --print-env) OUTPUT_MODE="env"; shift ;;
        --dry-run) DRY_RUN=true; shift ;;
        --help|-h) show_help ;;
        *) echo "ERROR: Unknown argument: $1" >&2; exit 1 ;;
    esac
done

if [[ -z "$SLUG" ]]; then
    echo "ERROR: --slug is required" >&2
    echo "Usage: dream-setup.sh --slug t01-name [--base-branch BRANCH]" >&2
    exit 1
fi

# --- Input validation: prevent shell injection via the `eval` contract ---
# The script's output is fed to `eval`, so any unescaped shell metachars in
# slug/namespace would execute as code. Restrict to filesystem-safe chars,
# AND require a non-`.` first char to reject bare `.`/`..` as a slug or ns.
SAFE_RE='^[A-Za-z0-9_-][A-Za-z0-9._-]*$'
if ! [[ "$SLUG" =~ $SAFE_RE ]]; then
    echo "ERROR: --slug must match $SAFE_RE (got: $SLUG)" >&2
    echo "  Use kebab-case alphanumerics like 't01-csv-fuzzer'." >&2
    exit 1
fi
if [[ -n "$NAMESPACE_OVERRIDE" ]] && ! [[ "$NAMESPACE_OVERRIDE" =~ $SAFE_RE ]]; then
    echo "ERROR: --namespace must match $SAFE_RE (got: $NAMESPACE_OVERRIDE)" >&2
    exit 1
fi

# --- Resolve repo root ---
if [[ -n "$REPO_ROOT_OVERRIDE" ]]; then
    REPO_ROOT="$REPO_ROOT_OVERRIDE"
else
    REPO_ROOT=$(git rev-parse --show-toplevel 2>/dev/null) || {
        echo "ERROR: Not in a git repository" >&2; exit 1
    }
fi
cd "$REPO_ROOT"

# --- Guard: .shadow/ must be tracked by git (not gitignored) ---
# The dream workflow moves .shadow/ content through git: artifacts are
# committed onto the dream branch, pushed, then read back by the reconciler
# via `git show origin/<branch> .shadow/...`. If .shadow/ is gitignored,
# `git add -A` silently skips those files, nothing is pushed, and the
# reconciler finds no manifest — every discovery is lost without warning.
# Fail fast with a clear message instead. (shadow-frog-init asks the user
# whether to commit or gitignore .shadow/; the dream skill requires committed.)
# Probe a NEW child path rather than `.shadow` itself: when `.shadow/` is
# gitignored but already tracked, `git check-ignore .shadow` reports "not
# ignored" (tracked content wins), yet `git add -A` still silently drops any
# NEW files created under it (e.g. _dreams/<id>/manifest.json) — the exact
# data-loss case this guard exists to prevent. A child path under .shadow/
# reflects the gitignore rule regardless of tracking state.
if git check-ignore -q .shadow/_dreams/__shadowfrog_probe__/manifest.json 2>/dev/null; then
    echo "ERROR: .shadow/ is gitignored — shadow-frog-dream requires it to be tracked by git." >&2
    echo "  Dream experiments commit .shadow/ artifacts onto a branch, push them, and" >&2
    echo "  reconcile reads them back from the remote. A gitignored .shadow/ would be" >&2
    echo "  silently dropped at commit time, losing every discovery." >&2
    echo "  Fix: remove the '.shadow/' entry from .gitignore and commit .shadow/," >&2
    echo "  or run shadow-frog-update (which works in local-only mode) instead of dream." >&2
    exit 1
fi

# --- Detect default branch ---
DEFAULT_BRANCH=$(git symbolic-ref refs/remotes/origin/HEAD 2>/dev/null \
    | sed 's|refs/remotes/origin/||')
if [[ -z "$DEFAULT_BRANCH" ]]; then
    if git show-ref --verify refs/remotes/origin/main >/dev/null 2>&1; then
        DEFAULT_BRANCH="main"
    elif git show-ref --verify refs/remotes/origin/master >/dev/null 2>&1; then
        DEFAULT_BRANCH="master"
    else
        echo "ERROR: Cannot detect default branch. Fix: git remote set-head origin <branch>" >&2
        exit 1
    fi
fi

# --- Resolve namespace ---
if [[ -n "$NAMESPACE_OVERRIDE" ]]; then
    DREAM_NS="$NAMESPACE_OVERRIDE"
elif [[ -n "${DREAM_NAMESPACE:-}" ]]; then
    DREAM_NS="$DREAM_NAMESPACE"
elif [[ -f TASK_INFO.json ]]; then
    DREAM_NS=$(python3 -c "import json; print(json.load(open('TASK_INFO.json')).get('dream_namespace',''))" 2>/dev/null || echo "")
elif [[ -f .env ]]; then
    DREAM_NS=$(grep '^DREAM_NAMESPACE=' .env 2>/dev/null | head -1 | cut -d'=' -f2- | sed -E 's/^[[:space:]]*["'\'']?//; s/["'\'']?[[:space:]]*$//' || echo "")
fi
DREAM_NS="${DREAM_NS:-$(basename "$REPO_ROOT")}"

# Validate resolved namespace too (could come from TASK_INFO/.env/basename)
if ! [[ "$DREAM_NS" =~ $SAFE_RE ]]; then
    echo "ERROR: Resolved DREAM_NS contains unsafe characters: $DREAM_NS" >&2
    echo "  Allowed: $SAFE_RE" >&2
    echo "  Override with --namespace or set DREAM_NAMESPACE." >&2
    exit 1
fi

# --- Compute identifiers ---
DREAM_ID="$(date -u +%Y%m%d-%H%M%SZ)-${SLUG}"
BRANCH_NAME="dream/${DREAM_NS}/${DREAM_ID}"

# --- Compute worktree path (ALWAYS in /tmp, NEVER in project) ---
WORKTREE_BASE="${DREAM_WORKTREE_BASE:-/tmp/shadowfrog-dreams}/${DREAM_NS}"
WORKTREE_DIR="${WORKTREE_BASE}/dream-${SLUG}"

# Validate worktree is external to project
case "$WORKTREE_DIR" in
    "$REPO_ROOT"|"$REPO_ROOT"/*)
        echo "ERROR: Worktree would be inside project: $WORKTREE_DIR" >&2
        echo "MUST use external path (default: /tmp/shadowfrog-dreams/)" >&2
        exit 1
        ;;
esac

# --- Resolve base reference ---
if [[ -z "$BASE_BRANCH" ]]; then
    BASE_REF="origin/$DEFAULT_BRANCH"
    PARENT_BRANCH="$DEFAULT_BRANCH"
else
    BASE_REF="origin/$BASE_BRANCH"
    PARENT_BRANCH="$BASE_BRANCH"
    # Verify the base branch exists on remote
    if ! git show-ref --verify "refs/remotes/$BASE_REF" >/dev/null 2>&1; then
        echo "ERROR: Base branch not found: $BASE_REF" >&2
        exit 1
    fi
fi

# --- Create worktree (unless dry-run) ---
BASE_COMMIT=""
if [[ "$DRY_RUN" == "false" ]]; then
    mkdir -p "$WORKTREE_BASE"

    # --- Periodic auto-GC (Bug A fix from bug-cleanup-gaps.md) ---
    # `dream-gc.sh` is documented as "run periodically" but had no caller in
    # the skill flow, so long-running fleets accumulated orphans forever
    # (machine reboots, OOM-killed agents, `$REPO_ROOT` unset, races, …).
    # Trigger it from here, throttled by a per-namespace tombstone file so
    # the cost amortizes across many dreams. ALL output is redirected to
    # stderr or /dev/null to preserve the `eval "$(...)"` contract.
    if [[ "${DREAM_GC_AUTO:-1}" != "0" ]]; then
        SCRIPT_DIR_SH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
        GC_SCRIPT="$SCRIPT_DIR_SH/dream-gc.sh"
        TOMBSTONE="$WORKTREE_BASE/.last-gc"
        GC_INTERVAL_MIN="${DREAM_GC_INTERVAL_MIN:-60}"
        GC_AGE_MIN="${DREAM_GC_AGE_MIN:-60}"

        # Validate the env-supplied integers so a hostile value can't reach
        # `find -mmin` or `dream-gc.sh --min-age-min` as injected args.
        # (dream-gc.sh itself also re-validates, but defense in depth.)
        SAFE_INT='^[0-9]+$'
        if ! [[ "$GC_INTERVAL_MIN" =~ $SAFE_INT ]] || ! [[ "$GC_AGE_MIN" =~ $SAFE_INT ]]; then
            echo "WARN: DREAM_GC_INTERVAL_MIN / DREAM_GC_AGE_MIN must be non-negative integers — skipping auto-GC" >&2
        elif [[ -x "$GC_SCRIPT" ]] || [[ -f "$GC_SCRIPT" ]]; then
            should_run=false
            if [[ ! -f "$TOMBSTONE" ]]; then
                should_run=true
            elif [[ "$GC_INTERVAL_MIN" -eq 0 ]]; then
                # Interval 0 ⇒ "always run". `-mmin +0` would NOT match a
                # tombstone touched in the last ~1 min, so we'd silently
                # skip-throttle the very first invocation after touch. Bypass
                # the find entirely.
                should_run=true
            elif [[ -n "$(find "$TOMBSTONE" -mmin "+$GC_INTERVAL_MIN" 2>/dev/null)" ]]; then
                should_run=true
            fi
            if [[ "$should_run" == true ]]; then
                # Touch BEFORE running, so a parallel `dream-setup.sh` for
                # the same ns sees a fresh tombstone and skips. Worst case
                # of a tombstone-vs-gc race is one extra GC pass; never a
                # missed cleanup.
                touch "$TOMBSTONE" 2>/dev/null || true
                bash "$GC_SCRIPT" \
                    --repo-root "$REPO_ROOT" \
                    --quiet \
                    --min-age-min "$GC_AGE_MIN" \
                    >&2 || true
            fi
        fi
    fi

    # Clean existing worktree (idempotent). Try git first, then fall back
    # to a safety-gated rm -rf for stale worktrees git can't see. Matches
    # the dream-cleanup.sh path so a leak healed during a retry instead of
    # cascading into "branch already exists" errors at git worktree add.
    if [[ -d "$WORKTREE_DIR" ]]; then
        SAFETY_SH="$(dirname "${BASH_SOURCE[0]}")/_worktree_safety.py"
        if ! git worktree remove "$WORKTREE_DIR" --force 2>/dev/null; then
            # Safety gate: only rm if path matches `<base>/<ns>/dream-<slug>`.
            # If the safety module is missing, REFUSE — never fall through
            # to an un-gated rm just because the gate is unloadable.
            if [[ ! -f "$SAFETY_SH" ]]; then
                echo "ERROR: safety module not found, refusing pre-clean rm: $SAFETY_SH" >&2
                exit 1
            fi
            if python3 "$SAFETY_SH" "$WORKTREE_DIR" "${DREAM_WORKTREE_BASE:-/tmp/shadowfrog-dreams}" >/dev/null 2>&1; then
                rm -rf -- "$WORKTREE_DIR"
            fi
        fi
        git worktree prune
    fi

    # Create worktree with new branch.
    # IMPORTANT: redirect BOTH stdout and stderr — modern git prints
    # "branch '...' set up to track..." and "HEAD is now at..." to stdout,
    # which would corrupt the `eval "$(...)"` contract used by callers.
    git worktree add "$WORKTREE_DIR" -b "$BRANCH_NAME" "$BASE_REF" >/dev/null 2>&1 || {
        git branch -D "$BRANCH_NAME" >/dev/null 2>&1 || true
        git worktree prune >/dev/null 2>&1
        git worktree add "$WORKTREE_DIR" -b "$BRANCH_NAME" "$BASE_REF" >/dev/null 2>&1 || {
            echo "ERROR: git worktree add failed for $WORKTREE_DIR (branch $BRANCH_NAME, base $BASE_REF)" >&2
            exit 1
        }
    }

    BASE_COMMIT=$(git -C "$WORKTREE_DIR" rev-parse HEAD)
else
    BASE_COMMIT=$(git rev-parse "$BASE_REF" 2>/dev/null || echo "DRY_RUN")
fi

# --- Detect RUN_PREFIX ---
RUN_PREFIX=""
if [[ -f uv.lock ]]; then
    RUN_PREFIX="uv run"
elif [[ -f package-lock.json ]]; then
    RUN_PREFIX="npx"
elif [[ -f yarn.lock ]]; then
    RUN_PREFIX="npx"
fi

# --- Output (values shell-escaped via printf %q for safe `eval`) ---
emit_export() {
    # printf %q produces a string that bash/zsh/sh can parse back losslessly.
    printf 'export %s=%q\n' "$1" "$2"
}

if [[ "$OUTPUT_MODE" == "json" ]]; then
    # JSON output — use python for safe escaping (handles quotes, backslashes,
    # control chars). Values are passed via the environment (NOT interpolated
    # into the Python source) so a repo path containing ", \, or $ can't break
    # the script. Falls back with a clear error if python is missing.
    SF_REPO_ROOT="$REPO_ROOT" \
    SF_DEFAULT_BRANCH="$DEFAULT_BRANCH" \
    SF_DREAM_NS="$DREAM_NS" \
    SF_DREAM_ID="$DREAM_ID" \
    SF_BRANCH_NAME="$BRANCH_NAME" \
    SF_PARENT_BRANCH="$PARENT_BRANCH" \
    SF_WORKTREE_DIR="$WORKTREE_DIR" \
    SF_WORKTREE_BASE="$WORKTREE_BASE" \
    SF_BASE_COMMIT="$BASE_COMMIT" \
    SF_RUN_PREFIX="$RUN_PREFIX" \
    SF_SLUG="$SLUG" \
    python3 - <<'PYEOF' || {
import json, os
print(json.dumps({
    "repo_root": os.environ["SF_REPO_ROOT"],
    "default_branch": os.environ["SF_DEFAULT_BRANCH"],
    "dream_ns": os.environ["SF_DREAM_NS"],
    "dream_id": os.environ["SF_DREAM_ID"],
    "branch_name": os.environ["SF_BRANCH_NAME"],
    "parent_branch": os.environ["SF_PARENT_BRANCH"],
    "worktree_dir": os.environ["SF_WORKTREE_DIR"],
    "worktree_base": os.environ["SF_WORKTREE_BASE"],
    "base_commit": os.environ["SF_BASE_COMMIT"],
    "run_prefix": os.environ["SF_RUN_PREFIX"],
    "slug": os.environ["SF_SLUG"],
}, indent=2))
PYEOF
        echo "ERROR: python3 required for --print-json" >&2
        exit 1
    }
else
    emit_export REPO_ROOT       "$REPO_ROOT"
    emit_export DEFAULT_BRANCH  "$DEFAULT_BRANCH"
    emit_export DREAM_NS        "$DREAM_NS"
    emit_export DREAM_ID        "$DREAM_ID"
    emit_export BRANCH_NAME     "$BRANCH_NAME"
    emit_export PARENT_BRANCH   "$PARENT_BRANCH"
    emit_export WORKTREE_DIR    "$WORKTREE_DIR"
    emit_export WORKTREE_BASE   "$WORKTREE_BASE"
    emit_export BASE_COMMIT     "$BASE_COMMIT"
    emit_export RUN_PREFIX      "$RUN_PREFIX"
    emit_export SLUG            "$SLUG"
fi
