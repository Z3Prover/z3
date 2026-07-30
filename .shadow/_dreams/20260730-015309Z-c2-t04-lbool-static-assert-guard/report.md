---
dream_id: "20260730-015309Z-c2-t04-lbool-static-assert-guard"
category: refactoring
verdict: useful
base_commit: "b795955cebc910b6bd2dd2fa75c540a2515a828e"
branch: "dream/z3shadow/20260730-015309Z-c2-t04-lbool-static-assert-guard"
parent_branch: "dream/z3shadow/20260729-223918Z-t04-lbool-ordinal-contract"
remote: "origin"
related_symbols:
  - "src/util/lbool.h::lbool"
builds_on:
  - "20260729-223918Z-t04-lbool-ordinal-contract"
---

# lbool static assert guard

## Motivation
Cycle 1 found lbool operators rely on enum ordinals; this experiment compounds by adding compile-time guards for that implicit contract.

## Compounding Delta
Built on `dream/z3shadow/20260729-223918Z-t04-lbool-ordinal-contract` and modified/extended its concrete code path: Modified src/util/lbool.h with ordinal static_asserts and extended the parent truth-table probe to verify the guards.

## Hypothesis
static_asserts immediately after the enum can document and mechanically guard the -1/0/1 contract without changing runtime code.

## Implementation
Modified src/util/lbool.h with ordinal static_asserts and extended the parent truth-table probe to verify the guards.

## Commands Run
- `python dream_experiments/c2-t04-lbool-static-assert-guard.py` - exit code 0

## Evaluation
The probe verified all three static_asserts are present and the arithmetic operator formulas remain unchanged.

Probe output:
```json
{"ordinal_guards": 3, "runtime_formulas_unchanged": true}
```

## Takeaways
lbool ordinal static_asserts can guard the arithmetic negation/conversion contract at compile time without changing operator~ or to_lbool runtime code.

## Verdict Details
Useful: the branch contains runnable code/probe changes and a verified shadow discovery tied to src/util/lbool.h.
