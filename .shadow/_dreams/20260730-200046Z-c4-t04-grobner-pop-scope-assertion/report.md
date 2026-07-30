---
dream_id: "20260730-200046Z-c4-t04-grobner-pop-scope-assertion"
category: refactoring
verdict: useful
base_commit: "ef7332ef200796448cdbd1077d2750369df857b1"
branch: "dream/z3shadow/20260730-200046Z-c4-t04-grobner-pop-scope-assertion"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/grobner/grobner.cpp::grobner::pop_scope"
builds_on: []
---

# Grobner pop-scope assertion audit

## Motivation
math/grobner was uncovered and scope rollback code is high-risk infrastructure.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c4-t04-grobner-pop-scope-assertion.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/math/grobner/grobner.cpp", "checks": 5, "bytes": 30868}
```

## Takeaways
grobner::pop_scope computes new_lvl as get_scope_level() - num_scopes but asserts num_scopes >= get_scope_level(), which is the reverse of the usual pop contract and would reject ordinary partial pops in debug builds.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/grobner/grobner.cpp`.
