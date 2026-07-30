---
dream_id: "20260729-223759Z-t03-sexpr-location-sentinel"
category: feature design
verdict: useful
base_commit: "7c7ffbc9a48eb20c401357d320bcf27dd30b4819"
branch: "dream/z3shadow/20260729-223759Z-t03-sexpr-location-sentinel"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/util/sexpr.h::sexpr_manager"
builds_on: []
---

# Sexpr location sentinel helper

## Motivation
src/util/sexpr.h records parser locations for S-expressions but exposes no helper for the absent-location sentinel.

## Hypothesis
A small has_location helper could remove repeated sentinel knowledge if all factories share the same default.

## Implementation
Added a Python probe that enumerates mk_* declarations and checks the accessors exported by sexpr.

## Commands Run
- `python dream_experiments/t03-sexpr-location-sentinel.py` - exit code 0

## Evaluation
The probe verified all factories consistently use UINT_MAX, making a helper feasible without changing stored representation.

Probe output:
```json
{"constructors_with_sentinel_defaults": 7, "raw_accessors": ["line", "pos"]}
```

## Takeaways
Every sexpr_manager mk_* factory defaults line and pos to UINT_MAX and sexpr only exposes raw get_line/get_pos accessors, so clients need to compare against UINT_MAX themselves to detect missing locations.

## Verdict Details
Useful: the branch contains a runnable probe and a verified shadow discovery tied to src/util/sexpr.h.
