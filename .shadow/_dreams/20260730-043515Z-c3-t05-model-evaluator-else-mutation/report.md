---
dream_id: "20260730-043515Z-c3-t05-model-evaluator-else-mutation"
category: optimization
verdict: useful
base_commit: "87567253c5ebe08cff582307bf30ea1bd42b88e4"
branch: "dream/z3shadow/20260730-043515Z-c3-t05-model-evaluator-else-mutation"
parent_branch: "dream/z3shadow/20260730-015431Z-c2-t05-model-evaluator-cache-scope"
remote: "origin"
related_symbols:
  - "src/model/model_evaluator.cpp::evaluator_cfg.expand_as_array"
builds_on:   - "20260730-015431Z-c2-t05-model-evaluator-cache-scope"
---

# Model evaluator as-array else mutation

## Motivation
Cycle 2 established m_def_cache is reset-scoped; this follow-up compounds by inspecting what work is cached during as-array expansion.

## Compounding Delta
Built on `dream/z3shadow/20260730-015431Z-c2-t05-model-evaluator-cache-scope` and extended the parent probe/code path: Extended the cycle-2 model-evaluator probe and added a new probe checking fi->set_else, nested evaluator completion=false, pinning, and cache insertion order.

## Hypothesis
expand_as_array may mutate missing function else values before caching the expanded array definition.

## Implementation
Extended the cycle-2 model-evaluator probe and added a new probe checking fi->set_else, nested evaluator completion=false, pinning, and cache insertion order.

## Commands Run
- `python dream_experiments/c3-t05-model-evaluator-else-mutation.py` - exit code 0

## Evaluation
The probe verified missing else cases are filled from model.get_some_value before get_array_interp, then evaluated with model completion disabled and pinned in m_def_cache.

Probe output:
```json
{"fills_missing_else_before_array_interp": true, "nested_eval_completion_false": true, "result_pinned_and_cached": true}
```

## Takeaways
expand_as_array fills a missing function interpretation else branch with model.get_some_value before extracting the array interpretation, then evaluates it with model completion disabled and pins the cached result.

## Verdict Details
Useful: the branch contains runnable probe/code changes and a verified shadow discovery tied to src/model/model_evaluator.cpp.
