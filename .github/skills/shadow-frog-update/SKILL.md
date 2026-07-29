---
name: shadow-frog-update
description: >-
  Update the shadow knowledge base after code changes and from conversational
  insights. Detects what changed via git diff, refreshes per-file shadows,
  captures knowledge shared by the user during the session, and updates
  cross-cutting discoveries. Invoke manually with /shadow-frog-update; the
  preToolUse hook will remind the agent when the shadow is behind HEAD.
---

# ShadowFrog Update

Updates `.shadow/` from two sources: code changes (git diff) and conversational
knowledge (what the user said during the session). Prerequisite: `.shadow/` exists.

## Triggers

1. Hook reminder: `preToolUse` injects a staleness warning when
   `.shadow/_meta/state.json#last_commit` differs from HEAD. The hook
   only reminds — it does NOT auto-run update.
2. Manual: user invokes `/shadow-frog-update`

## Phase 1: Detect Changes

```bash
# Read last_commit defensively: it may be missing, or the literal "none"
# when init ran without git (e.g. inside a container). `git diff none HEAD`
# would abort with "fatal: bad revision 'none'", and a missing key would
# make $LAST_COMMIT empty so `git diff HEAD` silently reports the wrong set.
LAST_COMMIT=$(python3 -c "import json,sys; print(json.load(sys.stdin).get('last_commit','none'))" < .shadow/_meta/state.json 2>/dev/null || echo "none")
if git rev-parse --verify "$LAST_COMMIT" >/dev/null 2>&1; then
    git diff --name-only "$LAST_COMMIT" HEAD   # committed changes since last update
else
    echo "WARNING: state.json has no usable last_commit — falling back to a full re-scan."
fi
git diff --name-only HEAD                       # uncommitted changes
git diff --name-only --cached                   # staged changes
```

Categorize: modified, added, deleted, renamed.

## Phase 2: Update Per-File Shadows (Symbol-Level)

For each changed file, update its shadow at the symbol level:

- **Added symbols** → add new `##` section
- **Removed symbols** → mark section as `REMOVED`, keep discoveries for history
- **Renamed symbols** → update heading, preserve discoveries
- **Modified symbols** → check if discoveries still hold

Lightweight update (auto/hook): re-extract symbols, update headings, flag stale.
Deep update (manual/dream): read diffs, generate new discoveries, verify existing ones.

## Phase 3: Capture Conversational Knowledge

When the user shares knowledge during the session, write it immediately.
Do not batch for later.

Signals to capture:

| Signal | Example | Category |
|--------|---------|----------|
| Warning | "Don't change the retry logic, it's subtle" | warning |
| Design intent | "We use this pattern because the API is unreliable" | intent |
| History | "We tried caching here but it caused stale reads" | history |
| Gotcha | "This looks wrong but matches the tax authority spec" | warning |
| Deprecation | "This module is being replaced by v2/" | intent |
| Contract | "The 30s timeout matches our SLA" | contract |
| Convention | "Always use the helper in utils.py, not raw SQL" | convention |

Write as:
```markdown
- <user's words, as close to verbatim as possible>
  _(verified, source: user)_
```

For knowledge emerging from collaborative work (debugging, refactoring, test failures):
```markdown
- <what was discovered and how>
  _(verified, source: interaction)_
```

Anchor to the specific `file::symbol`. `source: user` and `source: interaction`
are always `verified`.

### Auto-Placement

Users will not specify where to store their knowledge. You must find the
correct location. Procedure:

1. Parse the user's statement for code references — file names, function names,
   class names, module names, variable names, error messages, CLI flags.
2. If the knowledge is a **project-wide preference or convention** with no code
   references (e.g., "always use snake_case", "no backward compatibility",
   "prefer small PRs") → write to `_prefs.md`.
3. If explicit references found → look up those `file::symbol` paths in
   `_index.md` and the corresponding shadow files.
4. If no explicit references → use context:
   - What file is the user currently viewing or editing?
   - What files were recently modified in this session?
   - Search shadow files: `grep -rl "<keyword>" .shadow/ --include="*.md"`
5. If multiple candidate locations → pick the most specific symbol that the
   knowledge applies to. Prefer a single `file::symbol` over file-level.
6. If the knowledge spans 3+ files → create a `_cross/<slug>.md`
   entry and add back-pointers to each involved file's `## Cross-References`.
   For 2-file discoveries, use per-file entries with `Also involves:` instead.
7. If no matching location exists (e.g., the user mentions a concept not yet in
   the shadow) → place at the file-level `## File-Level` section of the most
   relevant file, or create a new `_cross/` entry for repo-wide knowledge.

Never ask the user "where should I put this?" — always resolve placement yourself.

## Phase 4: Extract Session Insights

At session end or manual trigger, review the session for:
1. Files modified and why
2. Patterns revealed by the changes
3. Unrecorded conversational knowledge (user statements not yet shadowed)
4. Cross-cutting discoveries (create in `_cross/<slug>.md` if 3+ files involved)

## Phase 5: Handle Structural Changes

Added files:
1. Check `.shadow/.shadowignore` — skip if the file matches an ignore pattern
2. Create `.shadow/<path>/<file>.md` with symbol-organized template
3. Add `## Cross-References` section
4. Add to `_index.md`

Deleted files:
1. Add `ORPHANED` marker to shadow header
2. Keep shadow (discoveries explain history)
3. Mark `[REMOVED]` on any `_cross/` refs pointing to this file
4. Update `_index.md`

Renamed files:
1. Move `.shadow/<old>.md` to `.shadow/<new>.md`
2. Update all `_cross/` `**Refs**:` entries (old path → new path)
3. Update all `Also involves:` in other per-file shadows
4. Update `_index.md`
5. Preserve all discoveries

## Phase 6: Verify and Dedup

Follow the dedup and writing rules in `/shadow-frog` — read before
write, merge or update existing entries, fix bad format in place.

**Verify exploration discoveries** using the observe-based or do-based
methods in `/shadow-frog` § Verification. `source: user` and
`source: interaction` → always `verified`; only re-verify if the
underlying code changes.

## Phase 7: Verify Reference Integrity

Check the five core invariants (full 7-invariant set in `/shadow-frog`):
- Every `_cross/<slug>.md` ref has a back-pointer in per-file `## Cross-References`
- Every `## Cross-References` entry has a corresponding `_cross/<slug>.md`
- No duplicate cross-cutting filenames
- All `Also involves:` use `file::symbol` notation
- No duplicate discoveries (same behavioral claim at same symbol)

Repair any violations before proceeding.

## Phase 8: Update Metadata

Preserve `dream_cycles_completed` from the existing state — only `dream-reconcile.py` increments it.

```json
{
  "version": 1,
  "initialized_at": "<preserved>",
  "last_update_at": "<now ISO>",
  "last_commit": "<full 40-char HEAD SHA>",
  "last_update_type": "init|auto|manual|dream|meditate",
  "total_files": N,
  "total_symbols": N,
  "total_discoveries": N,
  "dream_cycles_completed": <preserved>
}
```

Refresh `_index.md` with current counts.

## Discovery Writing Rules

See `/shadow-frog` § Discovery Format for the verbatim per-file,
cross-cutting, and preference formats. Rules to keep in mind during
update sessions:

- Be behavioral: "silently returns None on expired tokens" not "handles token expiration"
- `source: user` and `source: interaction` → always `verified`, use user's own words
- `source: exploration` → mark `uncertain` unless verified by code reading or tests
- If 3+ files involved → create in `_cross/<slug>.md` instead, add back-pointers
- If project-wide preference with no file reference → write to `_prefs.md`
- Slug naming: kebab-case derived from title (e.g., "Token expiry config split" → `token-expiry-config-split.md`)

## Staleness Rules

- Symbol modified → check if discovery still holds
- Symbol renamed → move discoveries to new heading
- Symbol removed → mark section `REMOVED`, keep discoveries
- `source: user` discoveries → only mark stale if symbol completely removed
