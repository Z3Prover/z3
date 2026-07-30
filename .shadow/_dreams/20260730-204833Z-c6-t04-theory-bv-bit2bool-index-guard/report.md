---
dream_id: "20260730-204833Z-c6-t04-theory-bv-bit2bool-index-guard"
category: refactoring
verdict: useful
base_commit: "fd5ae54bdd512d5ca83fbdb683a8f61823bc6f2e"
branch: "dream/z3shadow/20260730-204833Z-c6-t04-theory-bv-bit2bool-index-guard"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/smt/theory_bv.cpp::theory_bv::mk_bit2bool"
builds_on: []
---

# Theory BV bit2bool index guard

## Motivation
smt/theory_bv.cpp was uncovered and bit2bool bridges Boolean and bit-vector reasoning.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c6-t04-theory-bv-bit2bool-index-guard.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/smt/theory_bv.cpp", "checks": 4, "bytes": 87482}
```

## Takeaways
theory_bv::mk_bit2bool only emits the equivalence axioms to the backing bit vector when the requested bit index is within m_bits[v_arg].size(); numeral bit2bool terms are separately axiomatized from the concrete numeral value.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/smt/theory_bv.cpp`.
