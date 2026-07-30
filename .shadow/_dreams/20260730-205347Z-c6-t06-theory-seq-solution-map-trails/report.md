---
dream_id: "20260730-205347Z-c6-t06-theory-seq-solution-map-trails"
category: security audit
verdict: useful
base_commit: "fd5ae54bdd512d5ca83fbdb683a8f61823bc6f2e"
branch: "dream/z3shadow/20260730-205347Z-c6-t06-theory-seq-solution-map-trails"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/smt/theory_seq.cpp::theory_seq::solution_map"
builds_on: []
---

# Sequence solution map trail rollback

## Motivation
smt/theory_seq.cpp was uncovered and solution_map rollback protects incremental sequence solving.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c6-t06-theory-seq-solution-map-trails.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/smt/theory_seq.cpp", "checks": 6, "bytes": 113319}
```

## Takeaways
theory_seq::solution_map invalidates its lookup cache on every update and on pop_scope; rollback deletes inserted mappings and restores overwritten mappings from the trail in reverse order.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/smt/theory_seq.cpp`.
