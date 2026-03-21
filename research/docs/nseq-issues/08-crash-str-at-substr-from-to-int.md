# [nseq] Crashes: str.at / str.substr / str.from_int / str.to_int in complex formulas

**Labels**: bug, c3, nseq, crash

## Summary

The nseq solver crashes or returns errors on benchmarks that combine `str.at`,
`str.substr`, `str.from_int`, and `str.to_int` with regex constraints, length
constraints, or positional arithmetic. The seq solver handles all these correctly.

## Affected benchmarks

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `str.at.smt2` | sat | **bug/crash** |
| `str.at-2.smt2` | sat | **bug/crash** |
| `str.from_int_6.smt2` | sat | **bug/crash** |
| `str.to_int_5.smt2` | unsat | **bug/crash** |
| `str.to_int_6.smt2` | unknown | **bug/crash** |
| `substring.smt2` | sat | **bug/crash** |
| `substring2.smt2` | sat | **bug/crash** |
| `substring2b.smt2` | sat | **bug/crash** |
| `is-digit-2.smt2` | sat | **bug/crash** |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing examples

```smt2
; str.at.smt2 — EXPECTED: sat, nseq crashes
(set-logic QF_S)
(declare-const x String)
(assert (= (str.at x 2) "x"))
(assert (= (str.at x 3) "y"))
(check-sat)
```

```smt2
; str.from_int_6.smt2 — EXPECTED: sat, nseq crashes
(declare-const w String)
(declare-const x Int)
(declare-const y Int)
(assert (= (str.substr w 0 3) (str.from_int x)))
(assert (= (str.substr w 10 3) (str.from_int y)))
(assert (> x (* 2 y)))
(assert (>= y 0))
(check-sat)
```

```smt2
; str.to_int_5.smt2 — EXPECTED: unsat, nseq crashes
(declare-const w String)
(assert (= (str.to_int (str.substr w 0 10)) 123))
(assert (= (str.to_int (str.substr w 10 10)) 321))
(check-sat)
```

```smt2
; substring.smt2 — EXPECTED: sat, nseq crashes
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun n () Int)
(assert (= y (str.substr x n 5)))
(assert (>= (str.len x) (+ n 5)))
(assert (= (str.at y 0) "a"))
(assert (> n 0))
(check-sat)
```

```smt2
; is-digit-2.smt2 — EXPECTED: sat, nseq crashes
(set-logic QF_S)
(declare-fun x () String)
(assert (str.is_digit (str.at x 1)))
(assert (str.is_digit (str.at x 2)))
(check-sat)
```

## Analysis

These benchmarks all combine position-indexed string operations (`str.at`, `str.substr`)
with either:
- Direct string equality constraints on the extracted substring/character
- Integer conversion operations (`str.from_int`, `str.to_int`)
- Character classification (`str.is_digit`)
- Arithmetic constraints on positions (`n > 0`, `len(x) >= n + 5`)

The axioms for these operations (`at_axiom`, `extract_axiom`, `itos_axiom`, `stoi_axiom`,
`is_digit_axiom`) are defined in `seq_axioms.cpp` and are triggered via `relevant_eh` →
`dequeue_axiom`. The individual axioms appear to be implemented.

The crashes likely stem from one or more of:

1. **Interaction with variable-offset substring**: When `str.at x i` uses a variable
   index `i` (e.g., `str.at x 1` where `1` is a concrete integer, but the axiom
   creates skolems that interact with the Nielsen graph's variable positions),
   the resulting constraints may cause assertion failures.

2. **Double-application of str.at**: In `str.at.smt2`, two `str.at` constraints on the
   same variable `x` at different positions (2 and 3) must simultaneously hold.
   The `at_axiom` introduces skolem variables for each, and their combination in the
   Nielsen graph may not be handled correctly.

3. **Nested substr + conversion**: In `str.from_int_6.smt2` and `str.to_int_5.smt2`,
   the combination of `str.substr` extracting a sub-region plus integer conversion
   creates constraints that span the string/arithmetic boundary in ways the nseq
   solver's axiom-enqueuing mechanism may not handle.

4. **str.is_digit on str.at result**: In `is-digit-2.smt2`, `str.is_digit (str.at x 1)`
   requires the `is_digit_axiom` to be applied to the result of `at_axiom`. The nseq
   solver may not propagate the `relevant_eh` trigger through the composed term.

## Files to investigate

- `src/ast/rewriter/seq_axioms.cpp` — `at_axiom`, `extract_axiom`, `itos_axiom`, `stoi_axiom`, `is_digit_axiom`
- `src/smt/theory_nseq.cpp` — `relevant_eh` (check if nested terms trigger axiom enqueuing), `dequeue_axiom`
- `src/smt/seq/seq_nielsen.cpp` — handling of position-indexed skolem variables
