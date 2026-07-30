---
dream_id: "20260729-223918Z-t04-lbool-ordinal-contract"
category: refactoring
verdict: useful
base_commit: "7c7ffbc9a48eb20c401357d320bcf27dd30b4819"
branch: "dream/z3shadow/20260729-223918Z-t04-lbool-ordinal-contract"
parent_branch: "master"
remote: "origin"
related_symbols:
  - "src/util/lbool.h::to_lbool"
builds_on: []
---

# lbool ordinal contract

## Motivation
src/util/lbool.h is a tiny high-fan-in utility whose behavior is implicit in enum integer values instead of named cases.

## Hypothesis
The implementation depends on ordinal arithmetic rather than switch cases, which is easy to break during cleanup.

## Implementation
Added a truth-table probe that asserts the enum declaration and arithmetic formulas match the expected three-valued logic table.

## Commands Run
- `python dream_experiments/t04-lbool-ordinal-contract.py` - exit code 0

## Evaluation
The probe confirmed both operator~ and to_lbool depend directly on -1/0/1 values.

Probe output:
```json
{"ordinals": {"l_false": -1, "l_undef": 0, "l_true": 1}, "negation_table": {"-1": 1, "0": 0, "1": -1}}
```

## Takeaways
lbool negation and bool conversion are arithmetic over the enum ordinals -1/0/1; refactors that make lbool a scoped enum or reorder values must preserve those exact numeric assignments.

## Verdict Details
Useful: the branch contains a runnable probe and a verified shadow discovery tied to src/util/lbool.h.
