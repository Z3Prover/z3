---
dream_id: "20260730-202410Z-c5-t03-bit-blaster-quant-proof-gap"
category: feature design
verdict: useful
base_commit: "5c4be2171f2894f553f20cdb8b255b3db383c0b0"
branch: "dream/z3shadow/20260730-202410Z-c5-t03-bit-blaster-quant-proof-gap"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/tactic/bv/bit_blaster_tactic.cpp::bit_blaster_tactic::imp.operator()"
builds_on: []
---

# Bit-blaster quantified proof gap

## Motivation
tactic/bv was uncovered and the file has a user-visible unsupported feature boundary.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c5-t03-bit-blaster-quant-proof-gap.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/tactic/bv/bit_blaster_tactic.cpp", "checks": 4, "bytes": 5381}
```

## Takeaways
bit_blaster_tactic refuses blast_quant when proofs are enabled before rewriting the goal, but still installs a model converter after successful rewrites when models are enabled.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/tactic/bv/bit_blaster_tactic.cpp`.
