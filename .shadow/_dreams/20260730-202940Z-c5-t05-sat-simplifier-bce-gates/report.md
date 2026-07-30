---
dream_id: "20260730-202940Z-c5-t05-sat-simplifier-bce-gates"
category: optimization
verdict: useful
base_commit: "5c4be2171f2894f553f20cdb8b255b3db383c0b0"
branch: "dream/z3shadow/20260730-202940Z-c5-t05-sat-simplifier-bce-gates"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/sat/sat_simplifier.cpp::simplifier::bce_enabled_base"
builds_on: []
---

# SAT simplifier BCE gating

## Motivation
sat_simplifier.cpp was uncovered and simplification gates affect hot SAT preprocessing.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c5-t05-sat-simplifier-bce-gates.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/sat/sat_simplifier.cpp", "checks": 6, "bytes": 78317}
```

## Takeaways
sat::simplifier enables blocked-clause elimination only after the delay and only when not incremental, not tracking assumptions, not using learned clauses in use-lists, and single-threaded.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/sat/sat_simplifier.cpp`.
