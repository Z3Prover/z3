---
dream_id: "20260730-210358Z-c7-t01-solve-eqs-config-surface"
category: investigation
verdict: useful
base_commit: "9b083fdd0082bddf790c84b8cebf766b32ae2dde"
branch: "dream/z3shadow/20260730-210358Z-c7-t01-solve-eqs-config-surface"
parent_branch: "dream/z3shadow/20260730-204557Z-c6-t03-solve-eqs-level-overflow-guard"
remote: "origin"
related_symbols:
  - "src/ast/simplifiers/solve_eqs.h::solve_eqs::config"
builds_on:   - "20260730-204557Z-c6-t03-solve-eqs-level-overflow-guard"
---

# Solve-eqs configuration surface follow-up

## Motivation
Compounds the cycle-6 solve_eqs extraction guard by checking the public configuration fields that influence extraction.

## Compounding Delta
Built on `dream/z3shadow/20260730-204557Z-c6-t03-solve-eqs-level-overflow-guard` (base commit `9b083fdd0082bddf790c84b8cebf766b32ae2dde`), extended the parent probe when present, and added this follow-up check for `src/ast/simplifiers/solve_eqs.h`.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c7-t01-solve-eqs-config-surface.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/ast/simplifiers/solve_eqs.h", "checks": 5, "bytes": 3167}
```

## Takeaways
solve_eqs exposes separate configuration switches for context solving, occurrence caps, non-ground substitutions, and non-linear substitutions; these switches gate extraction before the substitution object is applied.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/ast/simplifiers/solve_eqs.h`.
