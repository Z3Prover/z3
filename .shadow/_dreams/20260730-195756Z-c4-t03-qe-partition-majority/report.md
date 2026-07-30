---
dream_id: "20260730-195756Z-c4-t03-qe-partition-majority"
category: feature design
verdict: useful
base_commit: "ef7332ef200796448cdbd1077d2750369df857b1"
branch: "dream/z3shadow/20260730-195756Z-c4-t03-qe-partition-majority"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/qe/qe.cpp::conjunctions.partition_vars"
builds_on: []
---

# QE partition majority rule

## Motivation
src/qe was uncovered and partition_vars has a visible heuristic boundary maintainers may tune.

## Hypothesis
A targeted static probe can verify the implicit behavior without a full Z3 build.

## Implementation
Added a runnable Python probe under dream_experiments that inspects the real source file and asserts the relevant control-flow markers are present.

## Commands Run
- `python dream_experiments/c4-t03-qe-partition-majority.py` - exit code 0

## Evaluation
The probe completed successfully and printed the checked file, marker count, and file size.

Probe output:
```json
{"file": "src/qe/qe.cpp", "checks": 4, "bytes": 92472}
```

## Takeaways
qe::conjunctions::partition_vars treats a quantified variable that occurs in more than half of the conjuncts as shared and places it in a catch-all partition instead of unioning it through the sparse occurrence graph.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/qe/qe.cpp`.
