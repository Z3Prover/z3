---
dream_id: "20260730-044130Z-c3-t06-opt-objective-type-guards"
category: security audit
verdict: useful
base_commit: "3c0773d811ba972a15f614d9e8dfb46eee1286b4"
branch: "dream/z3shadow/20260730-044130Z-c3-t06-opt-objective-type-guards"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/opt/opt_context.cpp::context::scoped_state.add"
builds_on: []
---

# Optimize objective type guards

## Motivation
src/opt was untouched and opt_context.cpp accepts user-facing optimization objectives and soft constraints from API/parser layers.

## Hypothesis
The context should reject non-Boolean soft constraints and non-numeric/non-bit-vector objectives before they enter objective state.

## Implementation
Added a static adversarial probe over scoped_state::add overloads for soft constraints and objectives.

## Commands Run
- `python dream_experiments/c3-t06-opt-objective-type-guards.py` - exit code 0

## Evaluation
The probe verified soft constraints throw unless Boolean, and objectives throw unless bit-vector, integer, or real before insertion into m_objectives.

Probe output:
```json
{"soft_constraint_boolean_guard": true, "objective_sort_guard": true}
```

## Takeaways
opt::context::scoped_state::add rejects non-Boolean soft constraints and rejects objectives that are not bit-vector, integer, or real before appending them to optimization state.

## Verdict Details
Useful: the branch contains a runnable adversarial probe and a verified shadow discovery tied to src/opt/opt_context.cpp.
