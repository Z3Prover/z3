---
name: shadow-frog-dream
description: >-
  Run autonomous experimentation while the user is AFK. Uses 6 investigation
  categories (investigation, bug hunting, feature design, refactoring,
  optimization, security audit) to systematically discover non-obvious
  behaviors. Every task is an experiment — implement in worktrees, commit
  to persistent dream branches, and push to the fork. Dreams compound
  across sessions: future experiments branch from prior dream branches,
  building a tree of progressively deeper work. Invoke when the user is
  AFK or asks for a dream run.
scripts:
  - dream-coverage.py
  - dream-validate.py
  - dream-reconcile.py
  - dream-setup.sh
  - dream-cleanup.sh
  - dream-gc.sh
---

# ShadowFrog Dream

Autonomous experimentation while the user is away. Every task is an
**experiment** — implement real code in a worktree, run it, persist as a
**named git branch** pushed to the fork. Dream's unique value is
implementation experience that **compounds across sessions**.

## Critical Invariants

These rules are stated ONCE here and enforced by helper scripts. Violating
any of them is a completion criteria failure.

### Prerequisite: `.shadow/` must be git-tracked

Dream moves `.shadow/` content **through git** — artifacts are committed onto
the dream branch, pushed to the remote, then read back by the reconciler via
`git show origin/<branch> .shadow/...`. If `.shadow/` is gitignored (the
"local only" option in `shadow-frog-init`), `git add -A` silently skips those
files, nothing reaches the remote, and the reconciler finds no manifest —
**every discovery is lost without warning**. `dream-setup.sh` runs
`git check-ignore .shadow` up front and refuses to start if it's ignored.
Use `shadow-frog-update` instead for local-only shadows.

### Path Isolation

```
WORKTREE_BASE = /tmp/shadowfrog-dreams/<DREAM_NS>/
WORKTREE_DIR  = $WORKTREE_BASE/dream-<SLUG>
```

- Worktrees are ALWAYS in `/tmp/shadowfrog-dreams/<DREAM_NS>/`, NEVER in
  the project directory. This prevents conflicts between parallel agents
  and keeps the main repo clean.
- `DREAM_NS` (namespace) isolates branches per task/instance. Resolved
  from: `DREAM_NAMESPACE` env → `TASK_INFO.json` → `.env` → repo basename.
- Override only with `DREAM_WORKTREE_BASE` env var if `/tmp` is too small.
- `dream-setup.sh` computes and enforces all paths. Use it.

### Branch Naming

```
BRANCH_NAME = dream/<DREAM_NS>/<DREAM_ID>
DREAM_ID    = YYYYMMDD-HHMMSSZ-<SLUG>
```

### Artifact Format

```
.shadow/_dreams/<DREAM_ID>/report.md
.shadow/_dreams/<DREAM_ID>/manifest.json
.shadow/_dreams/<DREAM_ID>/patch.diff
```

NEVER flat files (`_dreams/<DREAM_ID>.md`). Flat files break the pipeline.

### RUN_PREFIX

All python/pytest commands MUST use the `RUN_PREFIX` resolved during
preflight. When `RUN_PREFIX="uv run"`, use `$RUN_PREFIX python3 ...`.
Bare `python3` or `pytest` without prefix is a violation when non-empty.

### Reconciliation is Mandatory

Every dream branch must reconcile to main before the session ends. The
most common failure mode is agents pushing dream branches but never
reconciling — losing all discoveries.

**Two modes:**
- **Parallel mode (default):** Launch a batch of 3-4 sub-agents → wait
  for all to push → run `dream-reconcile.py "$REPO_ROOT"` ONCE at the end
  of the batch. The reconciler auto-discovers every un-reconciled dream
  branch in the namespace — you do NOT pass branch names. One call merges
  every pushed branch.
- **Sequential mode (fallback when sub-agents unavailable):**
  Complete dream → push → reconcile → verify → next dream. Adds ~30s
  per dream but guarantees zero data loss if the session crashes
  mid-batch.

Never queue multiple un-reconciled batches; reconcile at the end of
each batch or each individual dream.

### Script Failure Recovery

All helper scripts (`dream-setup.sh`, `dream-reconcile.py`,
`dream-validate.py`) are **self-documenting**. If a script fails or is
unavailable: **read the script source**, understand what it does, and adapt
its logic manually for your situation. Never skip steps just because a
script errored — the steps still need to happen.

```
Fork repo (user/target-repo)
  main --- .shadow/ (accumulated ALL discoveries)
  |
  +-- dream/<ns>/<id-1>  (cycle 1, agent A, from main)
  +-- dream/<ns>/<id-2>  (cycle 1, agent B, from main)
  +-- dream/<ns>/<id-3>  (cycle 2, from dream/<ns>/<id-1>, compounding)
```

- Branches are live — `git checkout dream/<id>` runs the code
- Shadow follows lineage — ancestor chain, not sibling branches
- Main is the accumulator — reconciliation merges ALL discoveries

### Prerequisites

1. Forked repo cloned locally with pushable remote
2. ShadowFrog skills installed (`install.sh --project /path/to/fork`)
3. `.shadow/` initialized (`/shadow-frog-init`)

## Helper Scripts

This skill bundles 6 helper scripts. Find them in the skill directory:

```bash
SKILL_DIR=""
for DIR in .github/skills/shadow-frog-dream .claude/skills/shadow-frog-dream; do
    [ -d "$DIR" ] && SKILL_DIR="$DIR" && break
done
```

| Script | Purpose | When to use |
|--------|---------|-------------|
| `dream-setup.sh` | Creates worktree + branch with namespace isolation | **Phase 3** — start of every experiment |
| `dream-validate.py` | Validates artifacts before push (hard gate) | **Phase 5** — before `git push` |
| `dream-reconcile.py` | Merges dream branches into main's `.shadow/` | **Phase 6** — after all experiments done |
| `dream-coverage.py` | Computes exploration coverage map | **Phase 2** — task planning for diversity |
| `dream-cleanup.sh` | Safely removes ONE dream worktree (with safety gate) | **After push** — replaces the old inline cleanup snippet |
| `dream-gc.sh` | Sweeps orphan dream worktrees from `$DREAM_WORKTREE_BASE` | **Auto** — triggered by `dream-setup.sh` (per-namespace throttle, default 1× / hour) in orphan-only mode; also `--task-complete --namespace "$DREAM_NS" --min-age-min 0` for end-of-session sweep of registered-but-stale dirs |

**Usage patterns:**

```bash
# Setup: creates worktree, prints export vars.
# IMPORTANT: capture the output FIRST, then eval it. Writing
# `eval "$(dream-setup.sh ...)" || exit 1` does NOT catch failures: if the
# command substitution exits non-zero and prints nothing, `eval ""` still
# succeeds (exit 0) and the agent silently proceeds with empty env vars.
# Assigning to a variable makes `|| exit 1` fire on the script's real exit code.
SETUP_OUT="$("$SKILL_DIR/dream-setup.sh" --slug t01-my-experiment)" || exit 1
eval "$SETUP_OUT"
# → exports (keep in sync with dream-setup.sh emit_export block):
#   REPO_ROOT, DEFAULT_BRANCH, DREAM_NS, DREAM_ID, BRANCH_NAME, PARENT_BRANCH,
#   WORKTREE_DIR, WORKTREE_BASE, BASE_COMMIT, RUN_PREFIX, SLUG

# Validate: hard gate before push
python3 "$SKILL_DIR/dream-validate.py" "$DREAM_ID" "$WORKTREE_DIR"

# Reconcile: merge all dream branches into main
python3 "$SKILL_DIR/dream-reconcile.py" "$REPO_ROOT"
# After `git push` succeeds, optionally clean up reconciled branches.
# Cleanup REFUSES to run if `.shadow/` has uncommitted changes, or unless
# HEAD is already on origin/<default-branch> — so the canonical flow is:
#   reconcile → git add .shadow/ && git commit && git push → re-run --cleanup-branches
python3 "$SKILL_DIR/dream-reconcile.py" "$REPO_ROOT" --cleanup-branches

# Coverage: show which files still need exploration
python3 "$SKILL_DIR/dream-coverage.py" "$REPO_ROOT"

# All scripts support --help.
```

If a script is not found or fails, read its source — they are
self-documenting. Adapt the steps manually if needed (see each phase for
inline fallback instructions).

## Phase 1: Preflight and Assess

### Preflight Validation

```bash
REPO_ROOT=$(git rev-parse --show-toplevel)
cd "$REPO_ROOT"

# 0. Auto-detect DREAM_NAMESPACE
if [ -z "${DREAM_NAMESPACE:-}" ]; then
    if [ -f TASK_INFO.json ]; then
        DREAM_NAMESPACE=$(python3 -c "import json; print(json.load(open('TASK_INFO.json')).get('dream_namespace',''))" 2>/dev/null)
        export DREAM_NAMESPACE
    elif [ -f .env ]; then
        DREAM_NAMESPACE=$(grep '^DREAM_NAMESPACE=' .env | head -1 | cut -d'=' -f2-)
        export DREAM_NAMESPACE
    fi
fi
[ -n "${DREAM_NAMESPACE:-}" ] && echo "Dream namespace: $DREAM_NAMESPACE"

# 1. Detect default branch
DEFAULT_BRANCH=$(git symbolic-ref refs/remotes/origin/HEAD 2>/dev/null | sed 's|refs/remotes/origin/||')
if [ -z "$DEFAULT_BRANCH" ]; then
    if git show-ref --verify refs/remotes/origin/main >/dev/null 2>&1; then
        DEFAULT_BRANCH="main"
    elif git show-ref --verify refs/remotes/origin/master >/dev/null 2>&1; then
        DEFAULT_BRANCH="master"
    else
        echo "ERROR: Cannot detect default branch. Fix: git remote set-head origin <branch>"
    fi
fi
echo "Default branch: $DEFAULT_BRANCH"

# 2-5. Validate environment
echo "Current branch: $(git branch --show-current)"
echo "Remote: $(git remote get-url origin)"
git ls-remote origin HEAD >/dev/null 2>&1 || echo "ERROR: Cannot reach remote."
[ -d .shadow ] || echo "ERROR: .shadow/ not found. Run /shadow-frog-init first."
mkdir -p .shadow/_dreams
git diff --quiet && git diff --cached --quiet || echo "ERROR: Uncommitted changes."

# 6. Fetch all remote branches (ONE fetch for all agents)
git fetch origin --prune

# 7. List dream branches (namespace-filtered)
DREAM_NS="${DREAM_NAMESPACE:-}"
BRANCH_PATTERN="${DREAM_NS:+origin/dream/${DREAM_NS}/}"
BRANCH_PATTERN="${BRANCH_PATTERN:-origin/dream/}"
echo "Available dream branches:"
git branch -r | grep "$BRANCH_PATTERN" | sed 's|origin/||' || echo "  (none)"

# 8. Detect RUN_PREFIX from lockfiles
if [ -f uv.lock ]; then
    uv sync --all-groups 2>&1 | tail -3
    RUN_PREFIX="uv run"
elif [ -f package-lock.json ]; then
    npm install --quiet 2>&1 | tail -3
    RUN_PREFIX="npx"
elif [ -f yarn.lock ]; then
    yarn install --silent 2>&1 | tail -3
    RUN_PREFIX="npx"
else
    RUN_PREFIX=""
fi
echo "RUN_PREFIX='$RUN_PREFIX'"

# 9. List compoundable experiments
echo ""
echo "=== COMPOUNDABLE EXPERIMENTS ==="
if [ -f .shadow/_dreams/_index.md ]; then
    awk -F'|' 'NR>2 && /useful/ {
        gsub(/ /,"",$2); gsub(/ /,"",$4); gsub(/ /,"",$6);
        gsub(/^ +| +$/,"",$5);
        if ($2 != "" && $6 != "") print $6 " | " $3 " | " $5
    }' .shadow/_dreams/_index.md
    COMPOUNDABLE=$(awk -F'|' 'NR>2 && /useful/ {gsub(/ /,"",$2); if ($2 != "") c++} END {print c+0}' .shadow/_dreams/_index.md)
    echo "Total compoundable: $COMPOUNDABLE"
else
    echo "(none — first dream session)"
fi
```

**If any check prints ERROR, STOP.** Do not use `exit 1` — check output
and stop at the agent level.

(`RUN_PREFIX` MUST be threaded into every subagent prompt — see Critical
Invariants above. Bare `python3`/`pytest` without prefix = completion
criteria violation.)

### Snapshot Branch State

After the single `git fetch`, capture dream branches and pass to all
sub-agents — they do NOT fetch independently.

```bash
DREAM_NS="${DREAM_NAMESPACE:-}"
BRANCH_FILTER="${DREAM_NS:+origin/dream/${DREAM_NS}/}"
BRANCH_FILTER="${BRANCH_FILTER:-origin/dream/}"
git branch -r --format='%(refname:short) %(objectname:short)' \
  | grep -F "$BRANCH_FILTER" \
  | sed 's|origin/||' > .shadow/_dreams/.branch-map.txt
cat .shadow/_dreams/.branch-map.txt

# Initialize session tracking (orchestrator-only; agents do NOT write here)
: > .shadow/_dreams/.session-branches.txt
```

### Assess Codebase

Read `_meta/state.json`, `_index.md`, existing discoveries, and **past
dream reports** in `_dreams/`.

### Build Exploration Coverage Map

File-level coverage breadth is the strongest predictor of dream success
(r²=0.63 vs bugs found), NOT dream count (r²=0.04).

```bash
# Find and run the coverage script
COVERAGE_SCRIPT=""
for DIR in .github/skills/shadow-frog-dream .claude/skills/shadow-frog-dream; do
    [ -f "$DIR/dream-coverage.py" ] && COVERAGE_SCRIPT="$DIR/dream-coverage.py" && break
done
[ -n "$COVERAGE_SCRIPT" ] && python3 "$COVERAGE_SCRIPT" "$REPO_ROOT" || echo "WARNING: dream-coverage.py not found"
```

**Coverage definition:** A file is "covered" only when its shadow has
≥1 behavioral discovery (line starting with `- `). Placeholder-only = NOT covered.

**Scoped exploration (`--scope`)** — pass `--scope <path-prefix>` (repeatable)
to restrict the coverage map to a specific subtree. Use this when the
broader repo is well-explored but a particular area (e.g., a known
frontier of bugs, a newly-added module, a subsystem the user just
flagged) deserves a focused dream session. All counts (totals, %,
saturated, fan-in, per-dir) are computed over the scoped subset only.

```bash
# Scope to one subtree
python3 "$COVERAGE_SCRIPT" "$REPO_ROOT" --scope src/auth/

# Scope to multiple subtrees in one pass
python3 "$COVERAGE_SCRIPT" "$REPO_ROOT" --scope src/auth/ --scope src/db/
```

When using `--scope`, the per-category task quotas (Phase 2) still apply
but are interpreted against the scoped subset. Don't use scoped
exploration as the default — pick it only when there's a concrete reason
to concentrate effort. Unscoped diversity remains the strongest
predictor of useful discoveries.

### Review Past Dreams (Required)

When compoundable experiments exist (preflight step 9):
- Read each report: `cat .shadow/_dreams/<dream_id>/report.md`
- Choose which to continue (extending, fixing, integrating)
- Note `dead_end` experiments to avoid repeating
- Trace lineage via the `parent` column in `_dreams/_index.md`

**Compounding quality gate** — before choosing to compound from a parent:

1. Read the parent's `report.md` AND `manifest.json`
2. Verify the parent has a non-empty `patch.diff` (prose-only parents
   are low-value — prefer parents with working code)
3. Identify at least one specific file or function you plan to modify/extend
4. Check the parent's area isn't saturated (8+ discoveries) — if it is,
   start fresh from main unless you have a concrete new angle
5. Log your compounding intent: "I will extend parent's retry logic in
   `src/http.py` to handle connection timeouts" — vague "continue
   exploring" is NOT compounding

**First dream session:** if preflight step 9 shows `(none)`, all tasks
branch from main.

## Phase 2: Plan

Generate a concrete plan. **Target 12 tasks (2 per category).** On small
codebases (<30 source files), minimum 6 tasks across 4+ categories.

### The 6 Investigation Categories

| Category | What to look for | Priority signals |
|----------|-----------------|-----------------|
| **Investigation** | Under-explored files, shallow coverage, uncertain discoveries | Files with 0-2 discoveries, import chains not traced, `uncertain` entries |
| **Bug hunting** | Defects, edge cases, race conditions | Error-handling code, concurrency, unvalidated inputs |
| **Feature design** | New capabilities, missing functionality | TODOs, FIXMEs, user-facing gaps, integration opportunities |
| **Refactoring** | Structural improvements, duplication | God classes, copy-paste patterns, high-coupling files |
| **Optimization** | Algorithmic efficiency, performance | Hot paths, nested loops, repeated I/O, missing caches |
| **Security audit** | Vulnerabilities, unsafe patterns | Auth code, data handling, deserialization, user inputs |

| Category | What to experiment |
|----------|-------------------|
| **Investigation** | Write assertion-based tests proving/disproving behavior hypotheses |
| **Bug hunting** | Fuzz inputs, trigger error paths, reproduce race conditions |
| **Feature design** | Implement the feature, run it, evaluate integration |
| **Refactoring** | Do the refactor, run existing tests, measure complexity |
| **Optimization** | Benchmark, profile, implement optimization, measure before/after |
| **Security audit** | Craft adversarial inputs, test injection vectors (local only) |

**Exception — user-directed focus**: If the user specifies a focus area
(e.g., "dream focus on security"), allocate ALL tasks to that category.

### Task Plan Format

Each task specifies **base branch**, **primary target file(s)**, and **why**:

```
Tasks (by category):
  Investigation:
    1. [title] — write tracing tests for [target]
       Base: main
       Target: src/auth/validator.py (UNCOVERED, 12 refs)
       Why: High fan-in utility with no shadow coverage
  Bug hunting:
    1. [title] — fuzz [target]
       Base: dream/<ns>/<prior-id> (compounds prior)
       Target: src/parsers/csv.py (extending parent's failing tests)
       Why: Parent found 2 crashes, need to verify fixes
  ...
```

### Diversity Rules

Prevent fixation (exploring the same files while leaving most untouched):

1. **Max 2 tasks per source file** (unless prior dream left concrete follow-up)
2. **≥30% of tasks on uncovered files** (from coverage map)
3. **≥2 tasks on "deep" files** (utilities, internals, converters)
4. **Vary directories** — no 3+ consecutive tasks in same dir

**Self-check before finalizing:** unique target files ≥ 60% of task count,
uncovered file tasks ≥ 30%, no file in > 2 tasks. Swap if failing.

**Escape hatches** (document justification): prior dream's failing test,
concrete untested hypothesis, file is 500+ lines with unexplored sections,
codebase has <20 source files.

### Task Design

Each task needs: **category**, **hypothesis**, **what to implement**,
**base branch**, **primary target** (with coverage status), **why this
target**, **scope** (hours, not days), and **success criteria**.

Good examples (one per category):
- **Investigation**: "Write assertion harness for request lifecycle —
  instrument each layer to log entry/exit and reveal implicit contracts"
- **Bug hunting**: "Fuzz the CSV parser with malformed inputs — what
  crashes or silently corrupts?"
- **Feature design**: "Implement retry logic with exponential backoff —
  does it handle transient failures without masking permanent ones?"
- **Refactoring**: "Extract 5 duplicate auth checks into middleware —
  run tests, measure if it simplifies without breaking special cases"
- **Optimization**: "Benchmark the hot path, implement LRU cache for
  repeated lookups — measure before/after wall time"
- **Security audit**: "Craft SQL injection payloads for user-facing
  endpoints — does parameterized query hold under nested quotes?"

Bad examples: "Look at the code", "Trace the flow", "Review error
handling", "Improve code quality"

### Feature Design: Motivation Required

Feature experiments must address a real gap identified in existing code.
Answer: "Why would maintainers want this?" with a specific code reference.
The feature must connect to the existing codebase (imports, modifies,
replaces duplication). Standalone modules with only stdlib don't qualify.

### Vary Your Approach

Each experiment should have unique structure driven by its hypothesis. If
you find yourself copying the same module layout (one source file + one
test file, identical importlib hack) across experiments, you're optimizing
for throughput over insight. Vary your approach: some experiments modify
existing files, some add tests for existing code, some create minimal
scripts, some refactor existing modules.

### File Selection Guidance

Agents gravitate toward entry points. Evaluation shows this causes missed bugs.

**High-value targets typically missed:**
- High fan-in files (imported by many, rarely explored directly)
- Internal/private modules (`_internal/`, `_utils/`, `_compat/`)
- Conversion/serialization code (parse, encode, format, marshal)
- Error handling paths (exception hierarchies, fallback logic)

**Avoid:** Starting from `__init__.py`, skipping "boring" files, same
directory 3+ times, ignoring files with few public symbols.

## Phase 3: Execute Tasks

Work through the plan. **Launch 3-4 experiments in parallel** via
sub-agents. Each handles the full lifecycle: create worktree → implement
→ test → write shadow + manifest + report → commit → push → clean up.
If sub-agents are unavailable, fall back to sequential execution.

**Each experiment runs in a separate git worktree.** The worktree IS the
dream branch (created with `-b`). After pushing, the worktree is removed
but the branch persists on the remote.

### Reading Before Implementing

You must understand the code before changing it. For each task:

1. Read the source file(s) and their shadows (existing discoveries)
2. Read shadows of referenced/referencing files
3. Understand the current behavior, edge cases, and implicit contracts

Reading is *preparation*, not the deliverable. The deliverable is code
written, code run, results recorded.

### Experiment Setup

Use `dream-setup.sh` to create worktrees (handles all path computation,
namespace resolution, worktree creation, and validation):

```bash
# Find the setup script
SETUP_SCRIPT=""
for DIR in .github/skills/shadow-frog-dream .claude/skills/shadow-frog-dream; do
    [ -f "$DIR/dream-setup.sh" ] && SETUP_SCRIPT="$DIR/dream-setup.sh" && break
done

# Fresh experiment from main:
SETUP_OUT="$("$SETUP_SCRIPT" --slug t01-csv-fuzzer)" || exit 1
eval "$SETUP_OUT"

# Compounding from prior dream:
SETUP_OUT="$("$SETUP_SCRIPT" --slug t03-extend --base-branch dream/<ns>/<prior-id>)" || exit 1
eval "$SETUP_OUT"
```

Capture into `SETUP_OUT` first, then `eval` it — see Helper Scripts §
usage patterns (above) for why bare `eval "$(…)" || exit 1` silently
swallows the script's exit code.

This exports (keep in sync with `dream-setup.sh`): `REPO_ROOT`,
`DEFAULT_BRANCH`, `DREAM_NS`, `DREAM_ID`, `BRANCH_NAME`, `PARENT_BRANCH`,
`WORKTREE_DIR`, `WORKTREE_BASE`, `BASE_COMMIT`, `RUN_PREFIX`, `SLUG`.

**If `dream-setup.sh` fails or is not found:** Apply the Script Failure
Recovery rule (read the script source, adapt its logic). Common causes:
missing git remote, branch already exists, `/tmp` permissions.

**Note:** Shell variables don't persist across tool calls. Either run
multi-step setup in a single shell, or re-derive values. From inside a
worktree, get main repo with:
`git -C "$(git rev-parse --git-common-dir)/.." rev-parse --show-toplevel`

**If worktree creation fails:** mark task `blocked`, replace with another.

### What Meaningful Compounding Looks Like

Compounding means **actively engaging with the parent's code**, not just
sitting on its branch. Valid compounding approaches:
- **Extend**: import or call the parent's modules and build on them
- **Modify**: edit the parent's code to fix limitations noted in its report
- **Refactor**: restructure the parent's implementation for better design
- **Integrate**: wire the parent's standalone module into the real codebase
- **Test deeper**: add edge-case tests for the parent's implementation

Don't assume the parent dream's code is complete or frozen — iterative
improvement is the whole point. If you can't find anything meaningful to
build on, start fresh from main instead.

Compounding that only adds a new standalone module beside the parent's
code (with no imports, edits, or integration) is NOT compounding — it's
a fresh experiment on the wrong branch.

### Run

1. Implement the experiment — write real code, run tests/builds
2. Note what worked, broke, surprised
3. Debug if needed — the struggle produces the best discoveries
4. Record results as you go

### Write Shadow Discoveries

**On the dream branch** (in the worktree), NOT on main.

**Every experiment MUST write ≥1 discovery to a per-file `.shadow/*.md`.**
Authoring order: write the human-readable shadow first, then mirror every
discovery into `manifest.json`. For reconciliation the **manifest is the
source of truth** — the reconciler merges manifest entries into main, so a
discovery that is missing from the manifest never reaches main. The per-file
shadow is the human-readable copy (and a required validate gate), not the
propagation path.

Follow the dedup and writing rules in `/shadow-frog`. Dream discoveries
are typically `source: exploration`. Mark `verified` when confirmed by
running code; `uncertain` if not fully testable.

#### How to Append

Find the `##`/`###` heading for the symbol, then:
- Placeholder `_No discoveries yet._` → replace with discovery
- Existing discoveries → append after last bullet
- No heading → create before `## Cross-References`

#### Label Triage (REQUIRED)

After writing each discovery, evaluate whether it deserves any of the
five actionable labels from `/shadow-frog` (`bug`, `security`,
`performance`, `feature-gap`, `tech-debt`). Apply labels when:

| Label | Apply when the discovery describes... |
|-------|---------------------------------------|
| `bug` | A defect, silent failure, off-by-one, race, incorrect result, edge case that misbehaves, validate-then-use ordering hazard |
| `security` | Injection vector, unsafe default, missing auth/authz check, sensitive value logged, untrusted input reaching unsafe sink |
| `performance` | Measured bottleneck, O(N²) where N is large, repeated I/O that could batch, missing cache, blocking call on hot path |
| `feature-gap` | Missing capability the codebase clearly needs, asymmetric API (e.g., reads but no writes) |
| `tech-debt` | Duplication, dead code, leaky abstraction, vestigial parameter, inconsistent naming |

Rules:
- Apply labels to BOTH the in-file discovery markdown AND the
  `manifest.json` discovery entry (`"labels": ["bug"]`). The reconciler
  uses the manifest as source of truth; the in-file copy is for humans
  reading the shadow directly.
- Multiple labels are fine when accurate: `labels: [bug, security]`.
- Omit labels for pure behavioral observations ("retries N times before
  giving up", "default timeout is 30s") — these are knowledge, not
  action items.
- Do not apply labels speculatively. The label says "an engineer should
  act on this." If you wouldn't act on it, don't label it.

Examples:

```
- /api/upload accepts paths from request body without normalization,
  allowing `../` traversal into /etc/.
  _(verified, source: exploration, labels: [bug, security])_
  Dream report: `_dreams/20260518-161200Z-upload-traversal/`
```

```
- HttpClient.send retries 3x on transient failures.
  _(verified, source: exploration)_
  Dream report: `_dreams/20260518-163000Z-retry-audit/`
```
(No label — pure behavioral knowledge, no action implied.)

`dream-validate.py` emits non-blocking warnings when discovery text
contains label-signal keywords but no label is set. Treat those
warnings as a prompt to re-check the triage, not as a directive.

#### Anchor Rules

- About existing code → anchor to that symbol
- Spans 3+ files → `_cross/<slug>.md`
- Project-wide convention → `_prefs.md`
- **Only create shadows for base-codebase files** — experiment-only files
  don't get shadows (the branch IS the artifact). Anchor findings to the
  existing code they relate to.

#### Cross-Cutting Discoveries

When you see the same behavior in 3+ files, create a `_cross/<slug>.md`
rather than repeating the discovery in each per-file shadow. Add
back-pointers in each file's `## Cross-References` section.

#### Discovery Quality

Discoveries must be **self-contained process knowledge** — understandable
with just the base codebase. Someone reading main's shadow should understand
the insight without checking out the dream branch. Capture **how to do it**,
**what you learned**, and **what to avoid** — not what was built. The branch
preserves the artifact; the shadow preserves the wisdom.

Good (behavioral insights about existing code):
- "functools.lru_cache is not thread-safe for initialization — two
  threads can trigger duplicate expensive computations on first call."
- "agent.py's retry loop catches all exceptions including OOM, masking
  fatal errors that should crash immediately."
- "To add a new eval metric, register in METRIC_MAP at metrics.py:25
  and implement the Metric interface — missing either causes a silent
  no-op in the pipeline."

Bad (descriptions of new code):
- "The implemented PluginFramework has PluginRegistry, PluginManager,
  and 7 lifecycle hooks." — describes branch-only artifact.
- "Provides RewardShaper with 4 methods, Welford normalizer, and
  GAE-lambda estimation." — feature spec, not behavioral insight.
- "Complete tested module with 58 passing tests." — verdict, not discovery.

Per-file discoveries should reference the dream report:

```
- Retrying with exponential backoff recovers from 99% of transient errors,
  but must exclude 4xx or it retries bad requests for 30s.
  _(verified, source: exploration)_
  Dream report: `_dreams/20250612-143012Z-retry-logic/`
```

### Write Discovery Manifest

After shadow writes, create `.shadow/_dreams/$DREAM_ID/manifest.json`:

```json
{
  "dream_id": "<DREAM_ID>",
  "branch": "<BRANCH_NAME>",
  "parent_branch": "main",
  "category": "bug hunting",
  "verdict": "useful",
  "title": "CSV Parser Edge Cases",
  "discoveries": [
    {
      "op": "add",
      "anchor": "src/parsers/csv.py::parse_row",
      "text": "Unescaped quotes in fields cause silent truncation.",
      "status": "verified",
      "source": "exploration",
      "labels": ["bug"],
      "also_involves": ["src/parsers/utils.py::unescape"],
      "dream_report": "_dreams/<DREAM_ID>/"
    }
  ],
  "cross_cutting": []
}
```

**Anchor format:** `file::symbol` with bare names (no backticks). The
reconciler handles normalization.

Manifest `op` values: only `add` is supported by the reconciler today.
`update` and `refute` are reserved keywords — `dream-validate.py` will
reject any discovery whose `op` is not `add`. To revise or contradict an
existing discovery, run a meditate session against main's `.shadow/`
instead of trying to do it from a dream branch.

**Hard gate — discoveries must be mirrored into per-file shadows.** The
reconciler merges `manifest.json` entries into main directly (so discoveries
are not lost at merge time), but the branch's per-file shadows must ALSO be
updated so human PR reviewers can read the discoveries in context. If
`manifest.json` declares discoveries but no `.shadow/*.md` files outside
`_dreams/` are modified in the branch diff vs `base_commit`,
`dream-validate.py` rejects the dream. Always write each discovery into BOTH
the corresponding per-file shadow (or `.shadow/_cross/`) AND the manifest
before staging.

### Save Dream Report

Save as `.shadow/_dreams/$DREAM_ID/report.md`:

```markdown
---
dream_id: "<DREAM_ID>"
category: bug hunting
verdict: useful
base_commit: "<BASE_COMMIT>"
branch: "<BRANCH_NAME>"
parent_branch: "main"
remote: "origin"
related_symbols:
  - "src/parsers/csv.py::parse_row"
builds_on: []
---

# CSV Parser Edge Cases

## Motivation
<cite specific existing files/symbols where gap was identified>

## Compounding Delta
<ONLY if parent_branch != main — what parent code was modified/extended>

## Hypothesis
<what we expected to learn>

## Implementation
<key decisions, approach>

## Commands Run
<exact commands with exit codes>

## Evaluation
<results, what worked/didn't>

## Takeaways
<lessons, gotchas>

## Verdict Details
<why useful/dead_end>
```

| Field | Required | Values |
|-------|----------|--------|
| `dream_id` | yes | `YYYYMMDD-HHMMSSZ-slug` |
| `category` | yes | one of the 6 categories |
| `verdict` | yes | `useful` or `dead_end` |
| `base_commit` | yes | SHA branched from |
| `branch` | yes | full branch name |
| `parent_branch` | yes | `main` or prior branch path |
| `related_symbols` | yes | `file::symbol` refs |

**`tip_commit` is NOT in the report.** Including the final commit SHA
creates a chicken-and-egg problem (SHA changes when report is committed).
The reconciler derives it via `git rev-parse origin/$BRANCH` and records
it in `_dreams/_index.md`.

**Verdict** is the agent's assessment (set once, immutable):
- `useful` — produced actionable findings, working code, or valuable lessons
- `dead_end` — approach doesn't work; documented why so future dreams skip

### Validate, Commit, Push

```bash
cd "$WORKTREE_DIR"

# 1. Generate diff (exclude .shadow/ and common build artifacts)
git add -A -- ':!.dream_parent' ':!__pycache__/' ':!.pytest_cache/'
git commit -m "dream: $SLUG"
mkdir -p .shadow/_dreams/"$DREAM_ID"
git diff "$BASE_COMMIT" HEAD -- \
    ':!.shadow/' ':!__pycache__/' ':!*.pyc' ':!.pytest_cache/' \
    ':!node_modules/' ':!*.lock' ':!dist/' ':!build/' \
    > .shadow/_dreams/"$DREAM_ID"/patch.diff
[ ! -s .shadow/_dreams/"$DREAM_ID"/patch.diff ] && echo "WARNING: Empty diff"

# 2. Validate (hard gate — must pass before push)
VALIDATE_SCRIPT=""
for DIR in .github/skills/shadow-frog-dream .claude/skills/shadow-frog-dream; do
    [ -f "$DIR/dream-validate.py" ] && VALIDATE_SCRIPT="$DIR/dream-validate.py" && break
done
if [ -n "$VALIDATE_SCRIPT" ]; then
    python3 "$VALIDATE_SCRIPT" "$DREAM_ID" "$WORKTREE_DIR" || {
        # If validate fails: read the script to understand what checks failed,
        # fix the issues it reports, then re-run. The script checks artifact
        # structure, manifest schema, and report frontmatter.
        echo "FIX ERRORS"; exit 1
    }
else
    # Script not found — inline fallback (minimal checks)
    [ ! -d ".shadow/_dreams/$DREAM_ID" ] && echo "ERROR: Missing dir" && exit 1
    for F in report.md manifest.json patch.diff; do
        [ ! -f ".shadow/_dreams/$DREAM_ID/$F" ] && echo "ERROR: Missing $F" && exit 1
    done
fi

# 3. Final commit and push
git add -A -- ':!.dream_parent'
git commit -m "dream: $SLUG — final with report and manifest"
if git push origin "$BRANCH_NAME"; then
    echo "Pushed: $BRANCH_NAME"
else
    echo "ERROR: Push failed. Keep worktree for recovery."
    exit 1
fi
```

**Do NOT write to `.session-branches.txt`** — that is managed by the
orchestrator after all agents complete. Agents only push their branch;
the orchestrator discovers pushed branches from the remote.

### Worktree Cleanup

```bash
bash "$SKILL_DIR/dream-cleanup.sh" "$WORKTREE_DIR" --repo-root "$REPO_ROOT"
```

`dream-cleanup.sh` does the equivalent of `git worktree remove --force`
followed by `git worktree prune`, but ALSO falls back to a safety-gated
`rm -rf` if `git worktree remove` silently fails — the failure mode that
leaked tens of dream worktrees per AFK session under the previous inline
snippet (see bug-worktree-leak.md). The rm fallback ONLY fires for paths
that match `${DREAM_WORKTREE_BASE:-/tmp/shadowfrog-dreams}/<ns>/dream-<slug>`
exactly; any other path is refused.

Remove as you go. If push failed, keep the worktree.

### Mid-Session Diversity Check

After completing roughly half of your planned tasks, pause and review:

1. **Count unique primary target files** explored so far. If fewer than
   50% of completed tasks targeted distinct files, remaining tasks MUST
   target new files.
2. **Check for re-exploration** — are any completed tasks exploring files
   already well-covered before this session? Swap remaining tasks for
   uncovered ones.
3. **Review coverage map delta** — if fewer than 2 previously uncovered
   files explored, prioritize uncovered files for remaining tasks.
4. **Adjust the plan** — swap, add, or reorder remaining tasks. The plan
   is a starting point, not a contract.

This prevents the fixation failure mode where the first half discovers a
rich area and the second half keeps digging there instead of spreading.

## Phase 4: AFK-Safe Patterns

1. Worktrees are outside the repo — writes don't trigger approval
2. Temp scripts go in `/tmp/shadow-dream-<slug>.*`
3. Never modify main directly — only during reconciliation
4. Clean up worktrees after push
5. Shadow writes on dream branches are safe

## Phase 5: Parallel Agent Rules

1. Each agent targets different files (orchestrator assigns non-overlapping sets)
2. Each agent gets its own branch (inherently isolated)
3. Each agent writes its own manifest in its `$DREAM_ID/` directory
4. Do NOT write to main or shared files (`_index.md`, `state.json`)
5. Do NOT update metadata — reconciled post-dream by orchestrator
6. Fetch once, branch from Phase 1 snapshot (no independent fetches)
7. Manifest anchors use bare symbol names (reconciler normalizes)
8. Thread `RUN_PREFIX` into every subagent prompt
9. Include `WORKTREE_BASE` and `DREAM_NS` in every subagent prompt
10. Dream artifacts MUST use subdirectory format — flat files are a
    completion criteria violation (see Critical Invariants → Artifact Format)

## Phase 6: Reconcile to Main

**⚠️ CRITICAL: Reconciliation is MANDATORY at the end of every dream batch.**
See Critical Invariants → Reconciliation is Mandatory (above) for the
parallel-vs-sequential mode definitions and the auto-discover rule. Do
NOT defer reconciliation across batches.

The `_index.md` entry is your sequential-mode checkpoint — any dream
listed there is safe if the session crashes.

Use the reconciliation script:

```bash
cd "$REPO_ROOT"
git checkout "$DEFAULT_BRANCH"
git fetch origin --prune

# Find and run the reconciliation script
RECONCILE_SCRIPT=""
for DIR in .github/skills/shadow-frog-dream .claude/skills/shadow-frog-dream; do
    [ -f "$DIR/dream-reconcile.py" ] && RECONCILE_SCRIPT="$DIR/dream-reconcile.py" && break
done

if [ -n "$RECONCILE_SCRIPT" ]; then
    python3 "$RECONCILE_SCRIPT" "$REPO_ROOT"
else
    echo "WARNING: dream-reconcile.py not found. Apply Script Failure Recovery: read dream-reconcile.py source, adapt its 9 steps manually."
fi
```

**If the reconciler script fails or errors:** Read `dream-reconcile.py` source
to understand which step broke and why. The script is structured as 9
sequential, idempotent steps (see below). You can often fix the issue and
re-run the script (it skips dreams already in `_index.md`), or perform the
failing step manually and then re-run the remaining steps. Common failures:
missing manifest, corrupt report frontmatter, merge conflict in shadow file.
Adapt based on the error message.

### What the Reconciler Does

1. **Discovers** new branches (namespace-filtered, not in `_index.md`)
2. **Reads/validates** manifests from remote branches
3. **Merges** discoveries into main's per-file shadows (semantic dedup; on an exact-text duplicate it upgrades the existing entry's metadata — unions labels, raises source trust, promotes `uncertain`→`verified` — but never alters a `refuted` status)
4. **Mirrors** reports, manifests, patches to main's `_dreams/`
5. **Updates** `_dreams/_index.md` with new entries
6. **Updates** `_meta/state.json`
7. **Rebuilds** top-level `.shadow/_index.md` (per-file discovery counts)
8. **Verifies** all artifacts present (hard gate)
9. **(Optional)** Deletes reconciled branches — only with `--cleanup-branches`, and only after the reconciliation has been committed and pushed (refuses on a dirty `.shadow/` or when HEAD is not yet on `origin/<default-branch>`)

### After Reconciliation: Commit, Push, and Cleanup

```bash
cd "$REPO_ROOT"
git add .shadow/
git commit -m "dream: reconcile $(date -u +%Y%m%d-%H%M%SZ) — N experiments"
git pull --rebase origin "$DEFAULT_BRANCH" || {
    echo "ERROR: Rebase failed. Abort and retry manually."
    git rebase --abort 2>/dev/null
    exit 1
}
if git push origin "$DEFAULT_BRANCH"; then
    echo "✓ Pushed reconciliation"
else
    echo "ERROR: Push failed. Retry: git pull --rebase && git push"
    echo "⚠️ Do NOT clean up branches until push succeeds."
    exit 1
fi
```

### Post-Reconciliation Branch Cleanup

After reconciliation is **committed AND pushed**, clean up dream branches
to prevent repo pollution. Only delete branches whose artifacts are safely
on main.

```bash
for BRANCH in $RECONCILED_BRANCHES; do
    DREAM_ID="${BRANCH#dream/${DREAM_NS}/}"
    # Safety check: verify artifacts exist on main BEFORE deleting.
    # Match the _index.md entry by EXACT cell (column 2), not substring —
    # `grep -qF "$DREAM_ID"` would false-match when one dream_id is a prefix
    # of another, deleting an un-reconciled branch.
    if [ -f .shadow/_dreams/"$DREAM_ID"/report.md ] && \
       [ -f .shadow/_dreams/"$DREAM_ID"/manifest.json ] && \
       [ -f .shadow/_dreams/"$DREAM_ID"/patch.diff ] && \
       awk -F'|' -v id="$DREAM_ID" \
         '{gsub(/ /,"",$2); if ($2==id) f=1} END {exit !f}' \
         .shadow/_dreams/_index.md 2>/dev/null; then
        # Safe to delete — all artifacts are on main
        git push origin --delete "$BRANCH" 2>/dev/null && \
            echo "  🗑 Deleted remote: $BRANCH"
        git branch -D "$BRANCH" 2>/dev/null && \
            echo "  🗑 Deleted local: $BRANCH"
    else
        echo "  ⚠️ KEEPING $BRANCH — artifacts not verified on main"
    fi
done
```

**Rules:**
- NEVER delete branches before push to main succeeds
- NEVER delete branches that have un-reconciled descendants
- If `SHADOWFROG_KEEP_BRANCHES=1` is set, skip cleanup (for eval harness)
- `dead_end` branches are cleaned up too — `patch.diff` + `tip_commit` in
  index preserves recoverability
- Branches with compounding descendants: delete ONLY after descendants are
  also reconciled (check `_index.md` for entries listing this branch as parent)

**Worktree cleanup** happens separately (Phase 7 — see "Worktree Pruning"
below). Worktrees can be removed immediately after branch push regardless
of reconciliation status. Reconciled branches also have their worktree
GC'd automatically by `dream-reconcile.py --cleanup-branches`.

### Recovery

If reconciliation is interrupted: branches are already pushed (no data
loss). Re-run reconciliation — it's idempotent. The reconciler uses
`_dreams/_index.md` as its journal: any branch already listed there is
skipped, any branch not listed is reprocessed. The reconciler's own
step 8 verifies all artifacts on main; if verification fails the script
exits non-zero — fix the cause and re-run.

## Phase 7: Summary, Review, and Pruning

### End-of-Session Cleanup

Before the summary, sweep leftover worktrees from the mid-batch leak
(dreams that pushed but weren't `dream-cleanup.sh`'d before the loop
exited). Only run this once the agent has asserted no more dreams are
starting **in this namespace**:

```bash
bash "$SKILL_DIR/dream-gc.sh" \
    --task-complete --namespace "$DREAM_NS" \
    --repo-root "$REPO_ROOT" --min-age-min 0
```

See "Worktree Pruning" below for `--namespace` rationale, `--min-age-min`
semantics, and the other three cleanup paths.

### Summary

```
Dream session complete.
  Results (by category):
    Investigation: N tasks, M discoveries
    Bug hunting: ...
  Branches pushed: K
  Branch tree:
    main
    +-- dream/<id-1> (useful)
    +-- dream/<id-2> (dead_end)
  Top findings:
    - <discovery> -- <category>
```

### Experiment Review

Walk through each experiment with the user. Actions:
- **Keep** (default) — branch and report stay
- **Delete** — remove from `_dreams/`, delete remote branch
- **Checkout** — inspect the code live

Wait for user confirmation before deleting any remote branch.

### Branch Pruning

Reconciled branches are cleaned up automatically after push. For
branches not auto-cleaned (push failed, or `SHADOWFROG_KEEP_BRANCHES=1`
set), apply the rules in Phase 6 → Post-Reconciliation Branch Cleanup
(above).

### Worktree Pruning

Dream worktrees live OUTSIDE the repo at
`${DREAM_WORKTREE_BASE:-/tmp/shadowfrog-dreams}/<ns>/dream-<slug>/`. There
are four places they get cleaned up:

1. **`dream-cleanup.sh`** — called by the agent after each `git push` (see
   "Worktree Cleanup" earlier in this skill). Removes ONE worktree.
2. **`dream-reconcile.py --cleanup-branches`** — after deleting a merged
   branch, also `rm -rf`s its worktree directory. No extra command needed.
3. **`dream-gc.sh` (auto-triggered)** — `dream-setup.sh` invokes this
   sweeper at the start of each new dream, throttled by a per-namespace
   `.last-gc` tombstone to run at most once per `DREAM_GC_INTERVAL_MIN`
   minutes (default 60). Catches orphans from crashed dreams, machine
   reboots, OOM-killed agents — the long tail of cleanup failures that
   accumulated GBs of leaked worktrees on long-running fleets.

   Env knobs (all optional, sensible defaults):
     - `DREAM_GC_AUTO=0` — disable the auto-trigger entirely
     - `DREAM_GC_INTERVAL_MIN` — how often the trigger fires (default 60)
     - `DREAM_GC_AGE_MIN` — min worktree age to sweep (default 60)

4. **`dream-gc.sh --task-complete --namespace "$DREAM_NS"`** —
   end-of-session sweep, run by the agent when it stops dreaming (dream
   count reached, or genuinely blocked). Unlike the auto-trigger, this
   mode ALSO removes `stale-registered` worktrees (valid `.git` pointer
   but no `dream-cleanup.sh` ever ran on them — the mid-batch
   `task_complete` leak). The agent's assertion "I'm done dreaming
   **in this namespace**" is what makes this safe.

   **Required:** `--namespace` (or `DREAM_NAMESPACE` env). The script
   refuses with exit 2 if neither is given — that prevents a multi-repo
   fleet sharing one `$DREAM_WORKTREE_BASE` from one agent's
   `task_complete` destroying another agent's live worktrees.

   `--min-age-min` is an **mtime gate, not a liveness check**. Pass `0`
   at end-of-session to catch the freshly-pushed final batch; pass a
   higher value (e.g. `10`) if you can't fully assert that no other
   dream in the same namespace is in flight. Locked worktrees
   (`git worktree lock`) are always respected — the sweeper WARNs and
   leaves them in place.

   ```bash
   # At the end of the dream loop, before the final summary:
   bash "$SKILL_DIR/dream-gc.sh" \
       --task-complete \
       --namespace "$DREAM_NS" \
       --repo-root "$REPO_ROOT" \
       --min-age-min 0
   ```

All four paths share a single safety gate (`_worktree_safety.py`) that
refuses ANY path which is not strictly under `$DREAM_WORKTREE_BASE` and
doesn't match the exact `<base>/<ns>/dream-<slug>` shape. The gate is
unconditional — even an attacker-controlled `$DREAM_WORKTREE_BASE` cannot
cause `rm -rf /`.

### Applying Dream Code

```bash
# Option 1: Merge the dream branch
git checkout "$DEFAULT_BRANCH"
git merge dream/<id> --no-ff -m "Adopt dream: <title>"

# Option 2: Cherry-pick specific commits
git cherry-pick <tip_commit>

# Option 3: Apply the patch (if branch was pruned but commit exists)
git show <tip_commit> | git apply
```

## Guidance

- **Always experiment.** Implementation reveals what reading cannot.
- **Small tasks, big lessons.** 30-minute experiment > 3 hours reading.
- **Fail forward.** "Tried X, broke because Y" is extremely valuable.
- **Breadth over depth.** More files with 2-3 discoveries > one file with 20.
- **No descriptions.** "Catches all exceptions including OOM" yes.
  "This function authenticates users" no.
- **Compound deliberately.** Read parent's report. Build on findings.
- **Branches are cheap, shadow is expensive.** Push freely, write carefully.

## Experiment Completion Criteria

A task is complete ONLY when ALL of these hold:

1. Code was written or modified (non-empty `patch.diff`)
2. At least one command was executed with exit code recorded in `Commands Run`
3. At least one finding tied to running code (not just reading)
4. At least one per-file `.shadow/*.md` edit made
5. Discoveries are behavioral insights, not feature descriptions
6. `report.md` saved with all required fields
7. Dream branch pushed to remote
8. Reconciliation completed and verified (`report.md`, `manifest.json`,
   `patch.diff` exist on main, `_index.md` has entry)

Additional gates:
- **Feature design:** `## Motivation` cites specific existing code
- **Compounding:** `## Compounding Delta` explains what parent code was modified

A task that fails these criteria is **not completed**. If setup fails or
the experiment produces nothing, mark it `blocked` in the summary and
replace it with another experiment. Blocked tasks do not count toward the
category minimum.

> **After reconciliation:** run `/shadow-frog-meditate` to consolidate
> discoveries and repair the index.

## Curating Dream Experiments for Upstream PRs

Once dream branches accumulate, you (or the user) may want to surface a
few worth submitting to the upstream project. The default AI failure mode
is sycophancy — approving too many experiments because they look like
work. Resist that. Apply these heuristics:

1. **The maintainer test.** For each experiment, ask: *If I submitted this
   as a PR to an open-source repo I don't maintain, would the maintainer
   merge it — or politely close it?* This is the only question that matters.
2. **Devil's advocate framing.** Your job is to find reasons NOT to PR
   each experiment. Recommend only when you cannot find a compelling
   reason to reject.
3. **70% rejection quota.** If you approve more than 30% of experiments
   reviewed, your standards are too low. Re-evaluate.
4. **The "so what?" test.** Would a human engineer read the report and
   say "so what?" If yes, reject.
5. **The 30-minute test.** Could a competent developer have produced
   this in 30 minutes with a linter, TODO grep, or quick docs read? If
   yes, it's maintenance work, not a contribution. Reject.
6. **The novelty test.** Does the experiment reveal a non-obvious
   behavior, hidden assumption, or unexpected interaction? If not, reject.
7. **No credit for effort.** A 10-experiment chain that produces a minor
   tweak is still a minor tweak. Judge the result, not the journey.

When you do submit a PR, write the body for someone who has never seen
the fork. Include: one-paragraph "what it does" derived from the dream
report, the experiment's evidence (test output, before/after metric),
and an honest "what we did not verify" note.
