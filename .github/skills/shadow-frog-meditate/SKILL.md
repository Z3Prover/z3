---
name: shadow-frog-meditate
description: >-
  Clean and consolidate the shadow knowledge base. Scans all shadow files
  for duplicate discoveries (same claim, different wording), near-duplicates
  (one extends another), and conflicting entries (contradicting claims).
  Merges duplicates, resolves conflicts by investigating the code, and
  asks the user only when resolution is unclear. Invoke periodically to
  keep the shadow focused and free of noise.
scripts:
  - meditate-repair.py
---

# ShadowFrog Meditate

Shadow hygiene — deduplicate, merge, and resolve conflicts across the
entire `.shadow/` knowledge base. Prerequisite: `.shadow/` exists with
discoveries.

## Why Meditate?

Over time, shadows accumulate noise:
- **Duplicates**: the same insight written differently by different sessions
- **Near-duplicates**: one discovery is a subset of another
- **Conflicts**: two discoveries contradict each other (code may have changed,
  or one was wrong)
- **Cross-scope duplicates**: a per-file discovery and a `_cross/` entry
  saying the same thing

This noise confuses downstream agents and dilutes signal. Meditate cleans
it up.

## Phase 1: Scan

Use parallel subagents to scan the shadow. Each subagent handles a batch
of shadow files.

### Scope Optimization

Not every file needs scanning. To reduce cost:
- **Skip files with 0-1 discoveries** — they can't have internal duplicates
- **Focus on files modified since last meditate** — check `_meta/state.json`
  `last_update_at` against file modification times
- **Always scan files with 5+ discoveries** — highest duplicate risk

For the first meditate after a large dream run, most files will need
scanning. For incremental meditation after small updates, this can
reduce scope by 80%+.

### Per-File Scan

For each per-file shadow (e.g., `src/auth.py.md`):

1. Read all discoveries under each `## symbol` heading
2. For each pair of discoveries under the **same symbol**, classify:
   - **Duplicate**: same behavioral claim, different wording
   - **Near-duplicate**: one discovery is a subset/refinement of the other
   - **Conflict**: the two discoveries make contradicting claims
   - **Distinct**: genuinely different insights — no action needed
3. Record each finding as a structured action (see below)

### Scan Output Format

Subagents must output findings as **one JSON object per line** so the
orchestrator can auto-apply resolutions. This is critical for automation —
prose recommendations require manual interpretation.

```
{"action": "merge", "file": "src/auth.py.md", "symbol": "authenticate_user", "keep": "- silently returns None on expired tokens...", "remove": "- returns None when token expires...", "merged": "- authenticate_user() silently returns None on expired tokens instead of raising. 3 of 7 callers don't check.\n  _(verified, source: exploration)_", "reason": "duplicate: same claim, different wording"}
{"action": "merge", "file": "src/db.py.md", "symbol": "connect", "keep": "- connection pool exhaustion...", "remove": "- pool runs out...", "merged": "...", "reason": "near-duplicate: first extends second"}
{"action": "conflict", "file": "src/auth.py.md", "symbol": "validate_token", "entry_a": "- raises ValueError...", "entry_b": "- returns False...", "resolution": "verified_a", "reason": "code inspection: line 42 raises ValueError"}
{"action": "conflict", "file": "src/cache.py.md", "symbol": "invalidate", "entry_a": "...", "entry_b": "...", "resolution": "escalate", "reason": "both claims have evidence, needs user input"}
{"action": "move_to_cross", "file": "src/auth.py.md", "symbol": "validate_token", "entry": "- all validators share...", "cross_slug": "shared-validation-pattern", "reason": "cross-scope: involves 4 files"}
```

Fields:
- `action`: `merge` | `conflict` | `move_to_cross` | `move_from_cross`
- `file`: shadow file path relative to `.shadow/`
- `symbol`: the `##`/`###` heading the discovery lives under
- `keep`: the discovery text to keep (for merge)
- `remove`: the discovery text to delete (for merge)
- `merged`: the final merged text (for merge)
- `resolution`: `verified_a` | `verified_b` | `escalate` (for conflict)
- `reason`: human-readable explanation

The orchestrator collects all lines, applies `merge` and `conflict`
actions automatically, and presents `escalate` items to the user.

### Cross-Scope Scan

After per-file scanning:

1. Collect all per-file discoveries into a flat list
2. For each `_cross/*.md` discovery, check if any per-file discovery
   makes the same or overlapping claim
3. For each `_prefs.md` preference, check if any per-file discovery
   or `_cross/` entry duplicates it
4. Record cross-scope findings the same way

### Scanning Guidelines

- Compare claims semantically, not just textually. "Returns None on
  expired tokens" and "Silently returns None when token expires" are
  duplicates.
- Two discoveries about the same function but covering different
  behaviors are **distinct**, not duplicates. E.g., "returns None on
  expired tokens" vs "uses constant-time comparison" — these are
  unrelated observations about the same function.
- Pay attention to `Also involves:` — two discoveries with overlapping
  `Also involves:` refs are more likely related.

## Phase 2: Resolve

Process each finding by type.

### Duplicates → Merge

Combine into a single discovery:
- Keep the **richer** wording (more detail, more context)
- Keep the **stronger** trust: `source: user` > `source: interaction` > `source: exploration`
- Keep the **stronger** status: `verified` > `uncertain` > `refuted`
- Merge `Also involves:` refs (union of both)
- Delete the weaker entry

Example:
```
BEFORE (two entries under same symbol):
- authenticate_user() returns None on expired tokens.
  _(verified, source: exploration)_
- When the token is expired, authenticate_user silently returns None
  instead of raising. 3 of 7 callers don't check.
  _(verified, source: exploration)_

AFTER (merged):
- authenticate_user() silently returns None on expired tokens instead
  of raising. 3 of 7 callers don't check the return value.
  _(verified, source: exploration)_
```

### Near-Duplicates → Absorb

The broader discovery absorbs the narrower one:
- Expand the broader entry to include any extra detail from the narrower
- Delete the narrower entry
- Preserve the stronger trust/status between the two

### Conflicts → Investigate

When two discoveries contradict each other:

1. Read the actual source code at the `file::symbol` location
2. Trace the logic to determine which claim is correct
3. If needed, write and run a short test script to verify
4. Mark the correct claim `verified`, the incorrect one `refuted`
5. If the incorrect claim was once true but code changed, update it
   to reflect the current behavior and mark it `verified`

If investigation takes more than a few minutes without resolution:
- Keep both discoveries
- Add a note: `(conflict unresolved — needs user input)`
- Ask the user to clarify at the end of the meditate session

### Cross-Scope Duplicates → Place Correctly

When the same discovery exists in both a per-file shadow and `_cross/`:

- If it involves 3+ files → keep in `_cross/`, remove from per-file
- If it involves 1-2 files → keep in per-file, remove from `_cross/`
- Update cross-references in both directions after moving

When a per-file discovery duplicates a `_prefs.md` entry:

- If it's truly project-wide (not tied to a specific symbol) → keep
  in `_prefs.md`, remove from per-file
- If it's specific to that symbol but happens to match a pref → keep
  both (they serve different purposes)

## Phase 3: Report

After all resolutions, print a summary:

```
Meditate Summary
================
  Files scanned:       42
  Duplicates merged:   7
  Near-dupes absorbed: 3
  Conflicts resolved:  2
  Conflicts escalated: 1
  Cross-scope fixed:   2
  Total entries removed: 12

Escalated (needs your input):
  src/auth.py::validate_token
    - "raises ValueError on invalid format" vs "returns False on invalid format"
    Both claims have evidence. Which behavior is correct?
```

## Parallelism

For large shadows (20+ files), use parallel subagents:

1. Partition shadow files into batches of ~10 files each
2. Launch one subagent per batch for Phase 1 (scan)
3. Each subagent outputs JSON-per-line findings (see Scan Output Format)
4. Orchestrator collects all JSON lines from all subagents
5. Auto-apply `merge` actions: use `edit` tool with `remove` as `old_str`,
   replace `keep` with `merged`
6. Auto-apply `conflict` actions where `resolution` is `verified_a` or
   `verified_b` — mark the loser `refuted`
7. Collect `escalate` items for user review
8. Run Phase 3 (report)

For smaller shadows, run everything in a single pass — the scan output
format is still useful for traceability.

## Dream Archive Hygiene (`_dreams/`)

Meditate performs consistency checks and field repair on `_dreams/`. It
does NOT delete or rewrite report prose (those are historical records),
but it DOES fix missing/wrong metadata in the index.

### Structural Checks

1. **Index consistency** — verify every folder in `_dreams/` has a row in
   `_dreams/_index.md`, and every row in the index has a matching folder.
   Fix mismatches (add missing rows, remove orphaned rows).

2. **Report completeness** — each `_dreams/<id>/` should contain at minimum
   a `report.md`. Flag any empty directories.

3. **Stale patches** — if `base_commit` in a report's frontmatter is more
   than 100 commits behind current HEAD, add a note to the index:
   `⚠️ patch may not apply cleanly`. Check with:
   ```bash
   git rev-list <base_commit>..HEAD --count 2>/dev/null
   ```

4. **Cross-reference integrity** — if a per-file discovery has a
   `Dream report: _dreams/<id>/` reference, verify that dream folder
   exists. Remove dangling references.

### Index Field Repair (run after Structural Checks)

Dream subagents sometimes write incomplete index rows (e.g., `unknown`
category/verdict, generic titles). `meditate-repair.py` (below)
auto-resolves these by reading each experiment's `report.md` frontmatter,
`manifest.json`, and verdict-section signals.

**Do NOT hand-edit 50+ rows.** Use the script. The agent's job is to
surface what the script CAN'T auto-fix:

- **Corrupted reports** — when `report.md`'s `dream_id` (frontmatter or
  body) doesn't match the folder name, the report was copy-pasted from
  another experiment. The script prints these to stderr and skips them.
  Do NOT auto-fix corruption — the content is wrong, not just the ID.
  Log them in the meditate summary for user review.
- **Ambiguous parent branches** — when no `manifest.json` exists for an
  experiment, the script falls back to slug heuristics (`-extend`,
  `-fix`, `-deeper`, `-improve`, `-integration`, `-cleanup`, `-metrics`,
  `-remaining` strongly suggest compounding from a sibling). If the
  heuristic match is not high-confidence, flag for user review rather
  than guessing.

### Applying Index Repairs

```bash
SKILL_DIR=""
for DIR in .github/skills/shadow-frog-meditate \
           .claude/skills/shadow-frog-meditate; do
    [ -d "$DIR" ] && SKILL_DIR="$DIR" && break
done

if [ -n "$SKILL_DIR" ] && [ -x "$SKILL_DIR/meditate-repair.py" ]; then
    python3 "$SKILL_DIR/meditate-repair.py"
else
    echo "meditate-repair.py not found; falling back to manual scan." >&2
fi
```

What it does:
- Backs up `.shadow/_dreams/_index.md` to `.bak` first
- Detects corrupted reports (frontmatter `dream_id` != folder name) and
  prints them to stderr — these rows are skipped, you resolve manually
- For every other row with `unknown`/empty category/verdict/title,
  resolves the canonical value from the report's frontmatter, manifest,
  or verdict section signals
- Title repair replaces generic forms (raw slug, "Dream Report: <slug>",
  "Dream t##: <slug>") with the first `# H1` or `## Summary` line

Verdict detection order is `manifest > VERDICT_SECTION signals >
whole-body signals`. Dead-end signals are checked BEFORE useful signals
so `not useful` doesn't match `useful`.

Idempotent — safe to rerun until output reports `0 repaired`.

Do NOT delete dream reports during meditate — only the user decides
what to keep or discard (via Phase 7 review or manual cleanup).

## Rules

- **Never delete a `source: user` discovery** without asking — user
  knowledge is the highest trust. If it conflicts with `source:
  exploration`, investigate thoroughly before concluding the user was wrong.
- **Preserve `Also involves:` refs** — when merging, take the union.
- **Update `_index.md`** after removing entries (discovery counts change).
- **Update `_meta/state.json`** — set `last_update_type: "meditate"`.
- **Don't touch `_prefs.md` placement** unless a pref is clearly
  duplicated verbatim in a per-file shadow.

## Format Compliance

**Every merged or rewritten discovery must exactly follow the canonical
format in `/shadow-frog`** (Discovery Format, Cross-Cutting, Preferences).
Re-read both the original entries and the spec before writing — a
malformed discovery is worse than a duplicate; it breaks the viewer
parser and downstream agents.

Meditate-specific rules:
- When merging, take the **union** of `labels: [...]` from both entries.
- When merging, preserve every `Also involves: file::symbol` from both
  entries (union, not intersection).
- `Dream report: _dreams/<id>/` references must survive the merge —
  re-attach to the merged entry if either original had one.
- Status (`verified`/`uncertain`/`refuted`) is taken from the stronger
  source: `user` ≻ `interaction` ≻ `verified` exploration ≻ `uncertain`.
- Discovery text stays **behavioral**, not a code summary — preserve the
  more behavioral wording when entries differ in style.
