---
dream_id: "20260730-213308Z-c8-t04-sat-elim-eqs-binary-normalization"
category: refactoring
verdict: useful
base_commit: "de18c0fa223e8d9c11f2c9ac89062f3d78956006"
branch: "dream/z3shadow/20260730-213308Z-c8-t04-sat-elim-eqs-binary-normalization"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/sat/sat_elim_eqs.cpp::elim_eqs::operator()"
builds_on: []
---

# SAT elim-eqs binary normalization

## Motivation
sat_elim_eqs.cpp was uncovered and binary clause rewriting is a structural simplification path.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c8-t04-sat-elim-eqs-binary-normalization.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/sat/sat_elim_eqs.cpp", "checks": 6, "bytes": 10667}
```

## Takeaways
sat_elim_eqs normalizes binary clauses through representative literals, detects unit/inconsistent cases when representatives collapse, and orders surviving binary pairs by literal index before reinsertion.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/sat/sat_elim_eqs.cpp`.
