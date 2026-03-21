# [nseq] Soundness bug: str.replace with empty-string input returns sat instead of unsat

**Labels**: bug, c3, nseq, soundness

## Summary

The nseq solver returns `sat` on benchmarks where the correct answer is `unsat` when
`str.replace` is applied to an empty input string and the result is constrained to an
impossible value. The seq solver correctly returns `unsat` for all of these cases.

## Affected benchmarks (Ostrich suite, c3 branch)

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `replace-special.smt2` | unsat | **sat** (WRONG) |
| `replace-special-4.smt2` | unsat | **sat** (WRONG) |
| `replace-special-5.smt2` | unsat | **sat** (WRONG) |
| `simple-replace-4b.smt2` | unsat | **sat** (WRONG) |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing examples

```smt2
; replace-special.smt2 — EXPECTED: unsat, nseq returns: sat
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (not (= (= "B" (str.replace "" x "A")) false)))
(check-sat)
```

```smt2
; replace-special-4.smt2 — EXPECTED: unsat, nseq returns: sat
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.replace "" (str.replace "" x "A") "B")
               (str.substr "B" 0 (str.len x)))))
(check-sat)
```

```smt2
; simple-replace-4b.smt2 — EXPECTED: unsat, nseq returns: sat
(set-logic QF_S)
(declare-fun x_7 () String)
(declare-fun x_11 () String)
(declare-fun x_12 () String)
(assert (= x_7 (str.replace (str.++ x_11 x_12) "e" "a")))
(assert (= x_7 "hello"))
(check-sat)
```

## Analysis

`replace_axiom` in `src/ast/rewriter/seq_axioms.cpp` generates clauses for
`r = str.replace u s t`:

- `~(u="") ∨ (s="") ∨ (r=u)` — empty input without empty pattern gives `r = u`
- `~(s="") ∨ (r = t ++ u)` — empty pattern gives `r = t ++ u`
- `contains(u,s) ∨ r = u` — no occurrence gives `r = u`

For `replace-special.smt2` with `u=""`:
- If `s=""`: `r = "A" ++ "" = "A"`, but `r = "B"` → contradiction → unsat
- If `s≠""`: `r = u = ""`, but `r = "B"` → contradiction → unsat

The clauses are individually correct, but the nseq Nielsen graph apparently fails to
derive the contradiction when the result `r` is constrained via equality to an impossible
constant. The likely root cause is incomplete propagation of the result equality through
the egraph into the replace axiom conclusions.

For `simple-replace-4b.smt2`, the issue is that `str.replace (x_11 ++ x_12) "e" "a" = "hello"`
is unsatisfiable because "hello" contains 'l', which cannot be produced by replacing 'e'→'a' in
any string, yet nseq claims sat.

## Files to investigate

- `src/ast/rewriter/seq_axioms.cpp` — `replace_axiom`
- `src/smt/theory_nseq.cpp` — `dequeue_axiom`, `populate_nielsen_graph`
