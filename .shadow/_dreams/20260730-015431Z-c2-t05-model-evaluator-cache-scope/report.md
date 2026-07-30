---
dream_id: "20260730-015431Z-c2-t05-model-evaluator-cache-scope"
category: optimization
verdict: useful
base_commit: "b0ba1ac7096df44c2ef4b65c276066ea004f05c1"
branch: "dream/z3shadow/20260730-015431Z-c2-t05-model-evaluator-cache-scope"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/model/model_evaluator.cpp::evaluator_cfg.expand_as_array"
builds_on:
  []
---

# Model evaluator cache scope

## Motivation
model_evaluator.cpp is uncovered and high fan-in; coverage plus source inspection showed an m_def_cache around as-array expansion.

## Hypothesis
m_def_cache may persist across top-level eval calls, or it may be per-evaluation only.

## Implementation
Added a static probe for expand_as_array cache insertion/lookup and imp::reset clearing behavior.

## Commands Run
- `python dream_experiments/c2-t05-model-evaluator-cache-scope.py` - exit code 0

## Evaluation
The probe verified expand_as_array caches array interpretations in m_def_cache, but imp::reset clears that cache with each evaluator reset.

Probe output:
```json
{"as_array_cache_lookup_and_insert": true, "cache_cleared_by_imp_reset": true}
```

## Takeaways
model_evaluator caches expanded as-array definitions in m_def_cache only within one evaluator reset cycle; imp::reset clears the cache, so repeated top-level eval calls recompute those expansions.

## Verdict Details
Useful: the branch contains runnable code/probe changes and a verified shadow discovery tied to src/model/model_evaluator.cpp.
