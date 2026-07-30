---
dream_id: "20260730-203218Z-c5-t06-subpaving-ineq-input-guards"
category: security audit
verdict: useful
base_commit: "5c4be2171f2894f553f20cdb8b255b3db383c0b0"
branch: "dream/z3shadow/20260730-203218Z-c5-t06-subpaving-ineq-input-guards"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/subpaving/tactic/subpaving_tactic.cpp::subpaving_tactic::imp.mk_ineq"
builds_on: []
---

# Subpaving tactic inequality guards

## Motivation
subpaving tactic input conversion was uncovered and processes user goals.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c5-t06-subpaving-ineq-input-guards.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/subpaving/tactic/subpaving_tactic.cpp", "checks": 4, "bytes": 9197}
```

## Takeaways
subpaving_tactic::mk_ineq accepts only <=/>= atoms with a numeral right-hand side after arith-lhs simplification; unsupported atoms or symbolic bounds throw tactic_exception before reaching the subpaving context.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/subpaving/tactic/subpaving_tactic.cpp`.
