---
dream_id: "20260730-212534Z-c8-t01-solver-header-scope-contract"
category: investigation
verdict: useful
base_commit: "0aae5507dc08b402c67a592318da42408f0192ab"
branch: "dream/z3shadow/20260730-212534Z-c8-t01-solver-header-scope-contract"
parent_branch: "dream/z3shadow/20260730-211723Z-c7-t06-solver-consequences-recheck-loop"
remote: "origin"
related_symbols:
  - "src/solver/solver.h::solver interface"
builds_on:   - "20260730-211723Z-c7-t06-solver-consequences-recheck-loop"
---

# Solver header scope contract follow-up

## Motivation
Compounds the cycle-7 solver consequence loop by checking the abstract scope/check_sat API contract it relies on.

## Compounding Delta
Built on `dream/z3shadow/20260730-211723Z-c7-t06-solver-consequences-recheck-loop` (base commit `0aae5507dc08b402c67a592318da42408f0192ab`), extended the parent probe when present, and added this follow-up check for `src/solver/solver.h`.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c8-t01-solver-header-scope-contract.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/solver/solver.h", "checks": 5, "bytes": 11066}
```

## Takeaways
solver exposes push/pop/get_scope_level as mandatory implementation hooks, while convenience check_sat overloads forward assumption vectors to the core pointer/count API.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/solver/solver.h`.
