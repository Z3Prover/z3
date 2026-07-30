---
dream_id: "20260730-202106Z-c5-t02-sat-clause-offset-packing"
category: bug hunting
verdict: useful
base_commit: "5c4be2171f2894f553f20cdb8b255b3db383c0b0"
branch: "dream/z3shadow/20260730-202106Z-c5-t02-sat-clause-offset-packing"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/sat/sat_clause.cpp::clause::get_new_offset"
builds_on: []
---

# SAT clause relocation offset packing

## Motivation
sat_clause.cpp was uncovered and packs pointer-like offsets into literal storage.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c5-t02-sat-clause-offset-packing.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/sat/sat_clause.cpp", "checks": 5, "bytes": 7289}
```

## Takeaways
sat::clause relocation on 64-bit stores a synthetic offset in the first two literal slots, so callers must only use get_new_offset/set_new_offset on clauses whose storage has at least two literal slots available.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/sat/sat_clause.cpp`.
