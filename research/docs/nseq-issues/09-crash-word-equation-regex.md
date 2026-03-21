# [nseq] Crashes: word equation + regex benchmarks (various operations)

**Labels**: bug, c3, nseq, crash

## Summary

The nseq solver crashes or errors on a variety of benchmarks involving combinations of
word equations with regex constraints, contains, replace_all, and SLIA arithmetic.
These represent missing or incomplete operation support in the nseq solver.

## Affected benchmarks

| File | seq verdict | nseq verdict | Operations involved |
|------|-------------|--------------|---------------------|
| `concat-001.smt2` | sat | **bug/crash** | word equation + regex (old syntax) |
| `contains-1.smt2` | unsat | **bug/crash** | contains in equality context |
| `contains-7.smt2` | sat | **bug/crash** | str.replace_all |
| `nonlinear-2.smt2` | sat | **bug/crash** | `a = b ++ b` + regex |
| `noodles-unsat8.smt2` | unknown | **bug/crash** | complex word equation |
| `noodles-unsat10.smt2` | unsat | **bug/crash** | complex word equation |
| `norn-benchmark-9i.smt2` | sat | **bug/crash** | old-syntax regex + complex |
| `pcp-1.smt2` | sat | **bug/crash** | SLIA + complex string ops |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing examples

```smt2
; concat-001.smt2 — EXPECTED: sat, nseq crashes
; Uses old-style str.in.re syntax and unambiguous regex constraints
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (str.in.re x (re.* (str.to.re "ab"))))
(assert (str.in.re y (re.* (str.to.re "c"))))
(assert (str.in.re z (str.to.re "cccc")))
(assert (= z (str.++ x y)))
(check-sat)
```

```smt2
; contains-1.smt2 — EXPECTED: unsat, nseq crashes
; str.contains used inside an equality with a boolean literal
(set-logic QF_S)
(declare-const x String)
(assert (not (= (str.contains "A" x) true)))
(check-sat)
```

```smt2
; contains-7.smt2 — EXPECTED: sat, nseq crashes
; str.replace_all used with regex constraints
(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const res String)
(assert (= res (str.replace_all x y z)))
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (not (str.in_re y (re.* (str.to_re "ab")))))
(assert (not (= res "")))
(check-sat)
```

```smt2
; nonlinear-2.smt2 — EXPECTED: sat, nseq crashes
; Non-linear word equation: a = b ++ b (self-concatenation)
(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)
(assert (= a (str.++ b b)))
(assert (str.in.re a (re.++ (re.* (str.to.re "(")) (re.+ (str.to.re ")")))))
(check-sat)
```

## Analysis of individual crash causes

### concat-001.smt2
Uses the old SMT-LIB `str.in.re` / `str.to.re` syntax with a word equation
`z = x ++ y` where all three variables have concrete regex constraints. If the nseq
solver's parser or internalization does not correctly handle the old-style `str.to.re`
synonym, the membership constraint may not be registered correctly.

### contains-1.smt2
The formula `(not (= (str.contains "A" x) true))` creates a Boolean atom of the form
`(= <bool-expr> true)` rather than the direct `str.contains` predicate.
In `assign_eh`, the direct check `is_contains(e)` will NOT match `(= (str.contains "A" x) true)`.
The catch-all `push_unhandled_pred()` fires, but the outer negation means the atom
`(= (str.contains "A" x) true)` is assigned to false. This should cause `FC_GIVEUP`,
but may manifest as a crash if the solver mishandles the boolean variable assignment.

**Fix**: Normalize `(= <bool-expr> true/false)` patterns in `assign_eh` or during
internalization, or add specific handling for `str.contains` embedded in boolean equalities.

### contains-7.smt2
Uses `str.replace_all` which is handled by `replace_all_axiom`. The crash may occur
when `replace_all_axiom` interacts with regex constraints on the arguments in ways
the Nielsen graph doesn't support.

### nonlinear-2.smt2
The word equation `a = b ++ b` is a non-linear equation (variable `b` appears twice
on the RHS). The Nielsen graph supports some non-linear equations, but this specific
combination with a regex constraint `a ∈ (re.* "(") ++ (re.+ ")")` — which constrains
characters — may expose a gap in the non-linear handling.

### noodles-unsat8 / noodles-unsat10
These are word equations from the Oliver Markgraf OSTRICH benchmark set. They involve
multiple variables with complex concatenation patterns and regex constraints. The crashes
suggest that the combination of 3+ variable word equations with disjunctive regex
constraints exceeds what the current nseq Nielsen graph implementation can handle.

## Files to investigate

- `src/smt/theory_nseq.cpp` — `assign_eh` (boolean-equality pattern for contains), `internalize_atom`
- `src/ast/rewriter/seq_axioms.cpp` — `replace_all_axiom`, contains axioms
- `src/smt/seq/seq_nielsen.cpp` — non-linear equation handling, `generate_extensions`
- `src/ast/seq_decl_plugin.cpp` — old-style synonym mapping (str.in.re / str.to.re)
