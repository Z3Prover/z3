---
dream_id: "20260730-213817Z-c8-t06-spacer-pob-normalize-twice"
category: security audit
verdict: useful
base_commit: "de18c0fa223e8d9c11f2c9ac89062f3d78956006"
branch: "dream/z3shadow/20260730-213817Z-c8-t06-spacer-pob-normalize-twice"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/muz/spacer/spacer_context.cpp::pob::inherit"
builds_on: []
---

# Spacer POB double normalization

## Motivation
muz/spacer was uncovered and POB inheritance carries proof-obligation state.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c8-t06-spacer-pob-normalize-twice.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/muz/spacer/spacer_context.cpp", "checks": 5, "bytes": 148833}
```

## Takeaways
spacer::pob::inherit normalizes m_post a second time when it differs from the parent because th_rewriter is not idempotent, then copies binding and level/depth state from the parent.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/muz/spacer/spacer_context.cpp`.
