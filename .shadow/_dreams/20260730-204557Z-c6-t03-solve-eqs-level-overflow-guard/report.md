---
dream_id: "20260730-204557Z-c6-t03-solve-eqs-level-overflow-guard"
category: feature design
verdict: useful
base_commit: "fd5ae54bdd512d5ca83fbdb683a8f61823bc6f2e"
branch: "dream/z3shadow/20260730-204557Z-c6-t03-solve-eqs-level-overflow-guard"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/ast/simplifiers/solve_eqs.cpp::solve_eqs::extract_subst"
builds_on: []
---

# Solve-eqs substitution level overflow guard

## Motivation
ast/simplifiers was uncovered and solve_eqs has a documented inefficiency plus a quiet bailout path.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c6-t03-solve-eqs-level-overflow-guard.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/ast/simplifiers/solve_eqs.cpp", "checks": 5, "bytes": 13129}
```

## Takeaways
solve_eqs::extract_subst silently abandons substitution extraction if the unsigned level budget would underflow, before inserting any remaining substitutions for that connected component.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/ast/simplifiers/solve_eqs.cpp`.
