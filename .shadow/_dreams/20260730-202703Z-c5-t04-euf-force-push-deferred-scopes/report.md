---
dream_id: "20260730-202703Z-c5-t04-euf-force-push-deferred-scopes"
category: refactoring
verdict: useful
base_commit: "5c4be2171f2894f553f20cdb8b255b3db383c0b0"
branch: "dream/z3shadow/20260730-202703Z-c5-t04-euf-force-push-deferred-scopes"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/ast/euf/euf_egraph.cpp::egraph::force_push"
builds_on: []
---

# EUF egraph deferred scope materialization

## Motivation
ast/euf was uncovered and force_push is an implicit backtracking contract.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c5-t04-euf-force-push-deferred-scopes.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/ast/euf/euf_egraph.cpp", "checks": 5, "bytes": 42429}
```

## Takeaways
euf::egraph defers scope materialization in m_num_scopes until force_push(), which records the update limit, pushes the region scope, records the theory-equality qhead, and notifies plugins in one batch.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/ast/euf/euf_egraph.cpp`.
