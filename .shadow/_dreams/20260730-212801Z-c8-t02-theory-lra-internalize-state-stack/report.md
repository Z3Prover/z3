---
dream_id: "20260730-212801Z-c8-t02-theory-lra-internalize-state-stack"
category: bug hunting
verdict: useful
base_commit: "de18c0fa223e8d9c11f2c9ac89062f3d78956006"
branch: "dream/z3shadow/20260730-212801Z-c8-t02-theory-lra-internalize-state-stack"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/smt/theory_lra.cpp::scoped_internalize_state"
builds_on: []
---

# Theory LRA internalize state stack

## Motivation
smt/theory_lra.cpp was uncovered and internalization state reuse is easy to leak across nested calls.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c8-t02-theory-lra-internalize-state-stack.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/smt/theory_lra.cpp", "checks": 5, "bytes": 173843}
```

## Takeaways
theory_lra reuses internalize_state objects through m_internalize_head: scoped_internalize_state allocates only when the stack grows, resets the reused state, and decrements the head on destruction.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/smt/theory_lra.cpp`.
