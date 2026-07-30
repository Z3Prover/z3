---
dream_id: "20260730-014333Z-c2-t01-model-universe-precedence"
category: investigation
verdict: useful
base_commit: "b0ba1ac7096df44c2ef4b65c276066ea004f05c1"
branch: "dream/z3shadow/20260730-014333Z-c2-t01-model-universe-precedence"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/model/model.cpp::model.get_some_value"
builds_on:
  []
---

# Model universe precedence

## Motivation
dream-coverage.py on src/model/ ranked model.cpp/model.h highest fan-in and uncovered; model::get_some_value controls fallback values for uninterpreted sorts.

## Hypothesis
Model value selection should prefer registered uninterpreted-sort universes before falling back to ast_manager defaults.

## Implementation
Added a static assertion probe for model::get_some_value, register_usort, and destructor ownership paths.

## Commands Run
- `python dream_experiments/c2-t01-model-universe-precedence.py` - exit code 0

## Evaluation
The probe verified get_some_value returns the first registered universe element when present and only falls back to m.get_some_value when no non-empty universe exists.

Probe output:
```json
{"universe_precedes_manager_fallback": true, "register_usort_replaces_old_universe": true}
```

## Takeaways
model::get_some_value prefers the first registered uninterpreted-sort universe element over ast_manager::get_some_value; empty or missing universes are the only path to the manager fallback.

## Verdict Details
Useful: the branch contains runnable code/probe changes and a verified shadow discovery tied to src/model/model.cpp.
