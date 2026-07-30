---
dream_id: "20260730-042331Z-c3-t01-nla-throttle-signature"
category: investigation
verdict: useful
base_commit: "3c0773d811ba972a15f614d9e8dfb46eee1286b4"
branch: "dream/z3shadow/20260730-042331Z-c3-t01-nla-throttle-signature"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/math/lp/nla_throttle.cpp::nla_throttle.insert_new_impl"
builds_on: []
---

# NLA throttle signature contract

## Motivation
Cycle 3 coverage planning pushed into previously untouched src/math/lp; nla_throttle.cpp is a small internal gate on nonlinear arithmetic lemma generation.

## Hypothesis
The throttle should return true only for repeated signatures and should encode lemma shapes into fixed signature slots.

## Implementation
Added a static probe over nla_throttle.cpp that verifies signature slot packing and insert_new_impl return/side-effect semantics.

## Commands Run
- `python dream_experiments/c3-t01-nla-throttle-signature.py` - exit code 0

## Evaluation
The probe confirmed every overload writes m_values slots before insert_new_impl, and insert_new_impl returns true for already-seen signatures while incrementing m_nla_throttled_lemmas.

Probe output:
```json
{"overloads_call_insert_new_impl": 5, "seen_returns_throttle_true": true}
```

## Takeaways
nla_throttle::insert_new_impl returns true to mean a signature was already seen and the caller should throttle; new signatures are inserted, trailed with insert_map, and return false.

## Verdict Details
Useful: the branch contains runnable probe/code changes and a verified shadow discovery tied to src/math/lp/nla_throttle.cpp.
