---
dream_id: "20260730-195156Z-c4-t01-nla-throttle-header-extension"
category: investigation
verdict: useful
base_commit: "86db932e2dca45436ecad5b5638a57c9147bd9a5"
branch: "dream/z3shadow/20260730-195156Z-c4-t01-nla-throttle-header-extension"
parent_branch: "dream/z3shadow/20260730-042331Z-c3-t01-nla-throttle-signature"
remote: "origin"
related_symbols:
  - "src/math/lp/nla_throttle.h::nla_throttle.signature"
builds_on:   - "20260730-042331Z-c3-t01-nla-throttle-signature"
---

# NLA throttle header signature width

## Motivation
Compounds the cycle-3 NLA throttle signature finding by checking the header contract that defines the signature representation.

## Compounding Delta
Built on `dream/z3shadow/20260730-042331Z-c3-t01-nla-throttle-signature` (base commit `86db932e2dca45436ecad5b5638a57c9147bd9a5`), extended the parent probe when present, and added this follow-up check for `src/math/lp/nla_throttle.h`.

## Hypothesis
The cpp-side slot packing is backed by a fixed-width zero-filled header representation.

## Implementation
Extended the parent NLA throttle probe and added a header contract probe.

## Commands Run
- `python dream_experiments/c4-t01-nla-throttle-header-extension.py` - exit code 0

## Evaluation
The probe found full-width zero initialization, memcmp equality, and eight-slot hashing.

Probe output:
```json
{"file": "src/math/lp/nla_throttle.h", "checks": 6, "bytes": 2766}
```

## Takeaways
nla_throttle signatures are fixed-width eight-slot records: construction zero-fills all slots, equality compares all eight slots, and hashing combines all eight slots, so every insert_new overload relies on unused slots remaining zero.

## Verdict Details
Useful: the branch contains a non-empty runnable probe and a verified per-file shadow discovery tied to `src/math/lp/nla_throttle.h`.
