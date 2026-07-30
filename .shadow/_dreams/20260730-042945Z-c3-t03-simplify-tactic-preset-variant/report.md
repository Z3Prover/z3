---
dream_id: "20260730-042945Z-c3-t03-simplify-tactic-preset-variant"
category: feature design
verdict: useful
base_commit: "3c0773d811ba972a15f614d9e8dfb46eee1286b4"
branch: "dream/z3shadow/20260730-042945Z-c3-t03-simplify-tactic-preset-variant"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/tactic/core/simplify_tactic.cpp::mk_elim_and_tactic"
builds_on: []
---

# Simplify tactic preset variant

## Motivation
src/tactic/core was untouched in earlier cycles; simplify_tactic.cpp already exposes one preset variant, suggesting a maintainable pattern for adding future simplifier feature variants.

## Hypothesis
The elim-and tactic is not a separate implementation; it is a parameter preset over simplify_tactic that future variants can copy.

## Implementation
Added a probe that verifies mk_elim_and_tactic sets elim_and and wraps mk_simplify_tactic with using_params while parameter descriptors still come from th_rewriter.

## Commands Run
- `python dream_experiments/c3-t03-simplify-tactic-preset-variant.py` - exit code 0

## Evaluation
The probe confirmed feature variants can be expressed as params_ref presets instead of duplicating simplify_tactic::imp.

Probe output:
```json
{"elim_and_is_param_preset": true, "param_descrs_delegate_to_th_rewriter": true}
```

## Takeaways
mk_elim_and_tactic implements the elim-and feature as a params_ref preset over mk_simplify_tactic via using_params, while get_param_descrs delegates to th_rewriter; new simplify variants can follow this wrapper pattern instead of duplicating the tactic implementation.

## Verdict Details
Useful: the branch contains runnable probe/code changes and a verified shadow discovery tied to src/tactic/core/simplify_tactic.cpp.
