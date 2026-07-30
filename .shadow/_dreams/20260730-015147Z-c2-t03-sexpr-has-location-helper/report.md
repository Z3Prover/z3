---
dream_id: "20260730-015147Z-c2-t03-sexpr-has-location-helper"
category: feature design
verdict: useful
base_commit: "8df2a1b28ca51c305f873ab180cea7673f424e2a"
branch: "dream/z3shadow/20260730-015147Z-c2-t03-sexpr-has-location-helper"
parent_branch: "dream/z3shadow/20260729-223759Z-t03-sexpr-location-sentinel"
remote: "origin"
related_symbols:
  - "src/util/sexpr.h::sexpr.has_location"
builds_on:
  - "20260729-223759Z-t03-sexpr-location-sentinel"
---

# Sexpr has_location helper

## Motivation
Cycle 1 found every sexpr factory uses UINT_MAX location sentinels but exposes only raw accessors; this experiment compounds by adding the helper the parent identified.

## Compounding Delta
Built on `dream/z3shadow/20260729-223759Z-t03-sexpr-location-sentinel` and modified/extended its concrete code path: Modified src/util/sexpr.h to add has_location() and extended the parent probe to assert the helper and unchanged factory defaults.

## Hypothesis
A header-only has_location() helper can encode the sentinel contract without changing sexpr layout or factory signatures.

## Implementation
Modified src/util/sexpr.h to add has_location() and extended the parent probe to assert the helper and unchanged factory defaults.

## Commands Run
- `python dream_experiments/c2-t03-sexpr-has-location-helper.py` - exit code 0

## Evaluation
The probe verified has_location() exists, checks both m_line and m_pos against UINT_MAX, and the seven factory defaults still use the same sentinels.

Probe output:
```json
{"has_location_header_only": true, "factory_defaults_preserved": 7}
```

## Takeaways
A sexpr::has_location() helper can be implemented header-only by checking both m_line and m_pos against UINT_MAX, preserving the existing factory default sentinel contract.

## Verdict Details
Useful: the branch contains runnable code/probe changes and a verified shadow discovery tied to src/util/sexpr.h.
