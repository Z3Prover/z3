# [nseq] Soundness bug: str.contains not preserved through concatenation

**Labels**: bug, c3, nseq, soundness

## Summary

The nseq solver returns `sat` for a benchmark that asserts:
1. `z` is a substring of `y` (`str.contains y z`)
2. `x = y ++ y`
3. `z` is NOT a substring of `x` (`not (str.contains x z)`)

The third assertion contradicts the first two, so the formula should be `unsat`.
The seq solver correctly returns `unsat`; nseq incorrectly returns `sat`.

## Affected benchmark

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `contains-4.smt2` | unsat | **sat** (WRONG) |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing example

```smt2
; contains-4.smt2 — EXPECTED: unsat, nseq returns: sat
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (str.contains y z))
(assert (= x (str.++ y y)))
(assert (not (str.contains x z)))
(check-sat)
```

## Analysis

If `str.contains y z` is true, then `y = L ++ z ++ R` for some `L`, `R`.
Then `x = y ++ y = L ++ z ++ R ++ L ++ z ++ R`, so `z` is a substring of `x`.
Therefore `not (str.contains x z)` is a contradiction.

The nseq solver should derive this via the combination of:
- `contains_true_axiom`: `str.contains y z` → `y = f1 ++ z ++ f2` (skolems)
- The equality `x = y ++ y`
- The Nielsen graph constraint that propagates the concatenation decomposition

The root cause may be that the nseq solver does not propagate `str.contains` facts
through word equation equalities in the Nielsen graph. When `x = y ++ y` is processed
as a word equation, the contains constraint on `y` should propagate to derive a contains
constraint on `x`, but this inference appears to be missing.

## Files to investigate

- `src/ast/rewriter/seq_axioms.cpp` — `contains_true_axiom`, `unroll_not_contains`
- `src/smt/seq/seq_nielsen.h` / `seq_nielsen.cpp` — word equation propagation
- `src/smt/theory_nseq.cpp` — `assign_eh` for contains, `populate_nielsen_graph`
