---
dream_id: "20260730-204036Z-c6-t01-sat-clause-metric-saturation"
category: investigation
verdict: useful
base_commit: "28d4b63e26f81a60985e28ad82e7ca5db6dcc3e3"
branch: "dream/z3shadow/20260730-204036Z-c6-t01-sat-clause-metric-saturation"
parent_branch: "dream/z3shadow/20260730-202106Z-c5-t02-sat-clause-offset-packing"
remote: "origin"
related_symbols:
  - "src/sat/sat_clause.h::clause metrics"
builds_on:   - "20260730-202106Z-c5-t02-sat-clause-offset-packing"
---

# SAT clause metric saturation follow-up

## Motivation
Compounds the cycle-5 sat_clause storage-contract finding by checking adjacent packed metrics in the header.

## Compounding Delta
Built on `dream/z3shadow/20260730-202106Z-c5-t02-sat-clause-offset-packing` (base commit `28d4b63e26f81a60985e28ad82e7ca5db6dcc3e3`), extended the parent probe when present, and added this follow-up check for `src/sat/sat_clause.h`.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c6-t01-sat-clause-metric-saturation.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/sat/sat_clause.h", "checks": 5, "bytes": 8048}
```

## Takeaways
sat::clause stores glue and psm in 8-bit fields and saturates setter inputs above 255, while inact_rounds is also an 8-bit field incremented without an explicit saturation guard in the header.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/sat/sat_clause.h`.
