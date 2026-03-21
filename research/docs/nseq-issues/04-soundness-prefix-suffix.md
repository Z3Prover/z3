# [nseq] Soundness bug: str.prefixof / str.suffixof interaction not fully axiomatized

**Labels**: bug, c3, nseq, soundness

## Summary

The nseq solver returns `sat` for several benchmarks involving `str.prefixof`,
`str.suffixof`, and `str.at` where the correct answer is `unsat`. The seq solver
handles all these cases correctly.

## Affected benchmarks

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `prefix-suffix.smt2` | unsat | **sat** (WRONG) |
| `failedProp.smt2` | unsat | **sat** (WRONG) |
| `failedProp2.smt2` | unsat | **sat** (WRONG) |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing examples

```smt2
; prefix-suffix.smt2 — EXPECTED: unsat, nseq returns: sat
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(assert (not (=> (and (str.prefixof a b) (str.suffixof b a)) (= a b))))
(check-sat)
```

The above asserts: `(a prefix b) AND (b suffix a) AND a ≠ b`.
This is unsatisfiable: if `a` is a prefix of `b` and `b` is a suffix of `a`,
then `|a| ≤ |b|` and `|b| ≤ |a|`, so `|a| = |b|`. Combined with the prefix and
suffix conditions, this forces `a = b`.

```smt2
; failedProp.smt2 — EXPECTED: unsat, nseq returns: sat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.prefixof x (str.at x 1)) (= x ""))))
(check-sat)
```

The above asserts: `(str.prefixof x (str.at x 1)) ≠ (x = "")`.
`str.at x 1` is the second character of `x` (as a length-1 string).
`str.prefixof x (str.at x 1)` is true only when `x` is a prefix of a single character,
which means `x = ""` or `x` is that single character (but then `x` is a prefix of itself only
if `len(x) ≤ 1`). This equivalence should hold: `str.prefixof x (str.at x 1) ↔ x = ""`.
So the assertion is `unsat`.

```smt2
; failedProp2.smt2 — EXPECTED: unsat, nseq returns: sat (same pattern with suffixof)
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (str.suffixof x (str.at x 1)) (= x ""))))
(check-sat)
```

## Analysis

For `prefix-suffix.smt2`, the current axioms for `prefix_axiom` and `suffix_axiom`
introduce skolem variables but may not derive the length equality `|a| = |b|` from the
combined prefix+suffix condition, or may not then propagate this to `a = b`.

For `failedProp.smt2` and `failedProp2.smt2`, the issue involves interaction between
`str.at`, `str.prefixof`/`str.suffixof`, and string-integer length constraints. The
nseq solver may not properly resolve the combination of:
1. The `at_axiom` (generating constraints on `str.at x 1`)
2. The `prefix_axiom`/`suffix_axiom` (decomposing the prefix/suffix relationship)
3. The arithmetic constraint linking lengths

## Files to investigate

- `src/ast/rewriter/seq_axioms.cpp` — `prefix_axiom`, `suffix_axiom`, `prefix_true_axiom`, `suffix_true_axiom`, `at_axiom`
- `src/smt/theory_nseq.cpp` — `assign_eh` for prefix/suffix, `final_check_eh`
- `src/smt/seq/seq_nielsen.cpp` — length propagation in Nielsen graph
