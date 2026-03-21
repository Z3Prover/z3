# [nseq] Soundness bug: str.indexof unsound when combined with regex membership

**Labels**: bug, c3, nseq, soundness

## Summary

The nseq solver returns `sat` for benchmarks that constrain `str.indexof` to values
impossible given the regex membership of the input string. The seq solver correctly
returns `unsat` for these cases.

## Affected benchmarks

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `indexof_const_index_unsat.smt2` | unsat | **sat** (WRONG) |
| `indexof_var_unsat.smt2` | unsat | **sat** (WRONG) |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing examples

```smt2
; indexof_const_index_unsat.smt2 — EXPECTED: unsat, nseq returns: sat
(set-info :status unsat)
(declare-fun a () String)
(declare-fun i () Int)
(declare-fun j () Int)
(assert (str.in_re a (re.union (str.to_re "hhhbbb") (str.to_re "bhhh"))))
(assert (= (str.indexof a "hhh" j) i))
(assert (= i 2))
(assert (> j 0))
(check-sat)
```

```smt2
; indexof_var_unsat.smt2 — EXPECTED: unsat, nseq returns: sat
(set-info :status unsat)
(declare-fun a () String)
(declare-fun i () Int)
(declare-fun j () Int)
(assert (str.in_re a (re.union (str.to_re "hhhbbb") (str.to_re "bhhh"))))
(assert (= (str.indexof a "hhh" j) i))
(assert (> i 1))
(check-sat)
```

## Analysis

For `indexof_const_index_unsat.smt2`:
- `a ∈ {hhhbbb, bhhh}` (two possibilities)
- `str.indexof a "hhh" j = 2` with `j > 0`
- In "hhhbbb", "hhh" appears at index 0 only (but j > 0 means the search starts after index 0)
- In "bhhh", "hhh" appears at index 1, but with j > 0 the only valid return would be 1, not 2
- So i = 2 is impossible → unsat

The `indexof_axiom` in `seq_axioms.cpp` generates arithmetic constraints for indexof,
but these constraints may not be sufficiently tight when combined with concrete regex
membership constraints. Specifically, the nseq solver does not appear to combine the
regex membership information with the indexof position constraints to derive the
contradiction.

The root cause is likely that nseq's `indexof_axiom` generates axioms about `str.indexof`
without leveraging the concrete alphabet constraints imposed by regex membership. The
seq solver may do additional propagation (e.g., via character-level analysis of the
regex language) that nseq does not perform.

## Files to investigate

- `src/ast/rewriter/seq_axioms.cpp` — `indexof_axiom`
- `src/smt/seq/seq_regex.h` / `seq_regex.cpp` — regex membership propagation
- `src/smt/theory_nseq.cpp` — interaction between regex constraints and arithmetic axioms
