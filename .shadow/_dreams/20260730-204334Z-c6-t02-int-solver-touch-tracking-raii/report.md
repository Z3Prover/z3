---
dream_id: "20260730-204334Z-c6-t02-int-solver-touch-tracking-raii"
category: bug hunting
verdict: useful
base_commit: "fd5ae54bdd512d5ca83fbdb683a8f61823bc6f2e"
branch: "dream/z3shadow/20260730-204334Z-c6-t02-int-solver-touch-tracking-raii"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/lp/int_solver.cpp::check_return_helper"
builds_on: []
---

# LIA touched-row RAII restoration

## Motivation
math/lp int_solver.cpp was uncovered and uses scoped state around patching/check logic.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c6-t02-int-solver-touch-tracking-raii.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/lp/int_solver.cpp", "checks": 5, "bytes": 33068}
```

## Takeaways
lp::check_return_helper disables touched-row tracking on construction and restores the exact previous tracking flag in its destructor, so early returns during integer checks should not permanently change LRA row tracking.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/lp/int_solver.cpp`.
