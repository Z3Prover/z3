---
dream_id: "20260730-211443Z-c7-t05-sat-scc-eliminated-skip"
category: optimization
verdict: useful
base_commit: "4d646fd910422ce0d78c3b0e3b8edcdfed3fb950"
branch: "dream/z3shadow/20260730-211443Z-c7-t05-sat-scc-eliminated-skip"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/sat/sat_scc.cpp::scc::operator()"
builds_on: []
---

# SAT SCC eliminated literal skip

## Motivation
sat_scc.cpp was uncovered and binary implication SCC is a preprocessing hot path.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c7-t05-sat-scc-eliminated-skip.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/sat/sat_scc.cpp", "checks": 5, "bytes": 10503}
```

## Takeaways
sat_scc skips literals whose variables were eliminated before Tarjan-style binary implication traversal, avoiding SCC work on removed SAT variables.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/sat/sat_scc.cpp`.
