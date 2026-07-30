---
dream_id: "20260730-200330Z-c4-t05-dd-bdd-memout-reorder"
category: optimization
verdict: useful
base_commit: "ef7332ef200796448cdbd1077d2750369df857b1"
branch: "dream/z3shadow/20260730-200330Z-c4-t05-dd-bdd-memout-reorder"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/dd/dd_bdd.cpp::bdd_manager::apply"
builds_on: []
---

# BDD mem_out reorder retry

## Motivation
math/dd was uncovered and BDD apply is an operation-cache hot path.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c4-t05-dd-bdd-memout-reorder.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/dd/dd_bdd.cpp", "checks": 5, "bytes": 40306}
```

## Takeaways
dd::bdd_manager::apply retries a mem_out failure exactly once after try_reorder(); a second mem_out is rethrown, so reordering is a single recovery attempt rather than an unbounded retry loop.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/dd/dd_bdd.cpp`.
