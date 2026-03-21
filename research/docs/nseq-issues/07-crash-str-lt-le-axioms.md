# [nseq] Crashes: str.< and str.<= axiom handling failures

**Labels**: bug, c3, nseq, crash

## Summary

The nseq solver crashes (returns "bug" in the benchmark runner) on formulas involving
`str.<` (lexicographic less-than) and `str.<=` (lexicographic less-than-or-equal)
string comparison predicates in contexts where they interact with length constraints
and character-level reasoning.

## Affected benchmarks

| File | seq verdict | nseq verdict |
|------|-------------|--------------|
| `str-leq11.smt2` | sat | **bug/crash** |
| `str-leq12.smt2` | sat | **bug/crash** |
| `str-leq13.smt2` | sat | **bug/crash** |
| `str-lt.smt2` | sat | **bug/crash** |
| `str-lt2.smt2` | sat | **bug/crash** |

Data from: https://github.com/Z3Prover/z3/discussions/9071

## Reproducing examples

```smt2
; str-leq11.smt2 — EXPECTED: sat, nseq crashes
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= 1 (str.len x)))
(assert (str.<= "a" x))
(assert (str.<= x "c"))
(check-sat)
```

```smt2
; str-lt.smt2 — EXPECTED: sat, nseq crashes
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= 1 (str.len x)))
(assert (str.< "A" x))
(assert (str.< x "C"))
(check-sat)
```

## Analysis

The nseq solver handles `str.<` and `str.<=` via `lt_axiom` and `le_axiom` in
`seq_axioms.cpp`, triggered from `relevant_eh` → `dequeue_axiom`. The `assign_eh`
for these predicates is a no-op with comment "axioms added via relevant_eh → dequeue_axiom".

The `lt_axiom` generates clauses involving:
- Skolem variables `x`, `y`, `z` (common prefix and suffixes)
- Skolem character variables `c`, `d`
- Prefix and character-comparison constraints

The crash likely occurs because:
1. The `lt_axiom` / `le_axiom` introduces character-comparison constraints (via `seq.mk_lt`)
   that require character-level arithmetic reasoning (e.g., comparing character codes).
   If the nseq solver's arithmetic integration does not correctly handle these
   character-code comparisons, it may crash or give incorrect results.

2. The `lt_axiom` clauses reference the Boolean literal for the `str.<` predicate itself
   (via `expr_ref lt = expr_ref(n, m)`). If `n` is used both as a term and as a literal
   reference, and nseq has an inconsistency in how it maps the Bool var to the expression,
   this could cause a null dereference or assertion failure.

3. The interaction between the length constraint `len(x) = 1` and the lt/le axioms'
   prefix-based decomposition may produce contradictory or unresolvable constraints
   in the Nielsen graph.

### What str-leq11 requires

For `len(x) = 1`, `"a" ≤ x ≤ "c"` (lexicographically): x ∈ {"a", "b", "c"}.
The solver needs to find x = "a", "b", or "c". This is straightforward with
character-range reasoning.

## Files to investigate

- `src/ast/rewriter/seq_axioms.cpp` — `lt_axiom`, `le_axiom`
- `src/smt/theory_nseq.cpp` — `assign_eh` for is_lt/is_le, `relevant_eh`, `dequeue_axiom`
- `src/smt/seq/seq_nielsen.cpp` — character-level constraint handling
