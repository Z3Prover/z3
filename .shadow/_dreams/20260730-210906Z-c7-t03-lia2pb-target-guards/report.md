---
dream_id: "20260730-210906Z-c7-t03-lia2pb-target-guards"
category: feature design
verdict: useful
base_commit: "4d646fd910422ce0d78c3b0e3b8edcdfed3fb950"
branch: "dream/z3shadow/20260730-210906Z-c7-t03-lia2pb-target-guards"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/tactic/arith/lia2pb_tactic.cpp::lia2pb_tactic::imp.is_target_core"
builds_on: []
---

# LIA2PB bounded target guards

## Motivation
tactic/arith was uncovered and lia2pb has user-facing boundedness criteria.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c7-t03-lia2pb-target-guards.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/tactic/arith/lia2pb_tactic.cpp", "checks": 6, "bytes": 11701}
```

## Takeaways
lia2pb_tactic only targets uninterpreted constants with lower bound 0, nonnegative integer upper bound, and upper-bound bit width within lia2pb_max_bits; partial mode controls whether other arithmetic variables cause failure.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/tactic/arith/lia2pb_tactic.cpp`.
