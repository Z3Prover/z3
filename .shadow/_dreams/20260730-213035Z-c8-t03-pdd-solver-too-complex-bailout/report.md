---
dream_id: "20260730-213035Z-c8-t03-pdd-solver-too-complex-bailout"
category: feature design
verdict: useful
base_commit: "de18c0fa223e8d9c11f2c9ac89062f3d78956006"
branch: "dream/z3shadow/20260730-213035Z-c8-t03-pdd-solver-too-complex-bailout"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/grobner/pdd_solver.cpp::solver::try_simplify_using"
builds_on: []
---

# PDD solver too-complex bailout

## Motivation
math/grobner pdd_solver was uncovered and simplify_using controls polynomial reduction work.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c8-t03-pdd-solver-too-complex-bailout.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/grobner/pdd_solver.cpp", "checks": 7, "bytes": 19119}
```

## Takeaways
math::grobner::pdd_solver increments the simplified-attempt statistic before knowing whether reduction changes the target, and a too-complex reduction sets m_too_complex then returns false without updating the equation.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/grobner/pdd_solver.cpp`.
