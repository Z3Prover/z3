---
dream_id: "20260729-222539Z-t01-params-fallback-probe"
category: investigation
verdict: useful
base_commit: "7c7ffbc9a48eb20c401357d320bcf27dd30b4819"
branch: "dream/z3shadow/20260729-222539Z-t01-params-fallback-probe"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/util/params.cpp::params::get_bool"
builds_on: []
---

# Params fallback probe

## Motivation
params_ref exposes fallback overloads in src/util/params.cpp, and callers depend on their precedence when layering global/module parameters.

## Hypothesis
The fallback overloads may key-check before type-checking and accidentally mask fallback values.

## Implementation
Added a Python assertion probe over params.cpp to verify the GET_VALUE2 macro and fallback-return bodies.

## Commands Run
- `python dream_experiments/t01-params-fallback-probe.py` — exit code 0

## Evaluation
The probe found the type guard is part of the key match, so mismatched primary entries fall through to fallback rather than masking it.

Probe output:
```json
{"fallback_overloads": 15, "macro_kind_guard": true}
```

## Takeaways
Fallback getters in params.cpp scan the primary set for both matching key and matching kind before consulting the fallback params_ref, so a key present with the wrong parameter kind does not block fallback lookup.

## Verdict Details
Useful: the branch contains a runnable probe and a verified shadow discovery tied to src/util/params.cpp.
