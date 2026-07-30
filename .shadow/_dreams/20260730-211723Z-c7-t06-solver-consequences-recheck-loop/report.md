---
dream_id: "20260730-211723Z-c7-t06-solver-consequences-recheck-loop"
category: security audit
verdict: useful
base_commit: "4d646fd910422ce0d78c3b0e3b8edcdfed3fb950"
branch: "dream/z3shadow/20260730-211723Z-c7-t06-solver-consequences-recheck-loop"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/solver/solver.cpp::solver::get_consequences_core"
builds_on: []
---

# Solver consequences recheck loop

## Motivation
solver.cpp was uncovered and get_consequences is a public API-facing helper.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c7-t06-solver-consequences-recheck-loop.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/solver/solver.cpp", "checks": 6, "bytes": 9790}
```

## Takeaways
solver::get_consequences_core performs an initial satisfiability check and then may issue one additional check_sat per candidate fixed variable, using temporary assumptions for Boolean constants and a scoped assertion for non-Boolean equalities.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/solver/solver.cpp`.
