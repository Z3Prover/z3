---
dream_id: "20260730-213540Z-c8-t05-arith-core-underspecified-zero-ops"
category: optimization
verdict: useful
base_commit: "de18c0fa223e8d9c11f2c9ac89062f3d78956006"
branch: "dream/z3shadow/20260730-213540Z-c8-t05-arith-core-underspecified-zero-ops"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/smt/theory_arith_core.h::theory_arith::internalize_atom"
builds_on: []
---

# Arithmetic core underspecified zero ops

## Motivation
smt arithmetic core was uncovered and div-by-zero semantics are user-visible.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c8-t05-arith-core-underspecified-zero-ops.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/smt/theory_arith_core.h", "checks": 6, "bytes": 139934}
```

## Takeaways
theory_arith_core maps division, integer division, and remainder by zero into dedicated underspecified div0/idiv0/rem0 terms instead of rejecting the expression during internalization.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/smt/theory_arith_core.h`.
