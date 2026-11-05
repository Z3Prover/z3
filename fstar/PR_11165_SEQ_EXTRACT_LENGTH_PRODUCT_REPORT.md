# Audit: PR #11165 — Avoid regex unfolding for provably out-of-range substring offsets

**PR:** https://github.com/Z3Prover/z3/pull/11165
**Fixes:** issue #11157
**Files changed:** `src/ast/rewriter/seq_rewriter.cpp`, `src/test/seq_rewriter.cpp` (tests only)

## Summary

`seq_rewriter::mk_seq_extract` (i.e. `(str.substr a offset size)` /
`(seq.extract a offset size)`) already simplified to the empty
sequence for *constant* out-of-range offsets. The reported regression
(#11157) involved a *symbolic* offset of the shape `(str.len a) *
(str.len a)` — algebraically always `>= len(a)`, but not a numeral, so
the existing constant-offset check didn't fire. Without the
simplification, the query fell through to unrolling a regex-membership
constraint over the (unbounded, string-length-dependent) `substr`
result and hit Z3's "reached max unfolding" limit, returning `unknown`
instead of the correct `unsat`.

The fix (src/ast/rewriter/seq_rewriter.cpp:976–1005) adds a new case to
`mk_seq_extract`: flatten the offset expression `b` through nested `*`
applications (DAG-size-bounded via a `visited` set), and if the
flattened multiset of factors consists of (a) at least one occurrence
of `(str.len a)` and (b) every other factor a numeral `>= 1`, then the
offset is provably `>= len(a)`, so the extract simplifies directly to
`(as seq.empty _)` — independent of the `size` argument.

## Formalization

New file: `Z3SeqExtractLengthProduct.fst` (built directly on the
existing `Z3SeqTheory.fst` model of `extract`/`extract_nat`, reused
rather than re-derived).

The rewrite's soundness reduces to one clean arithmetic fact plus one
semantic fact about `extract`, both proved here:

1. **`lemma_coeff_times_power_ge_base`** — for a natural number `n`
   (standing for `len(a)`, always `>= 0`) and positive integers `c, k`
   (the numeral coefficient and the count of `len(a)` factors):
   `c * n^k >= n`.
   - Proved via `lemma_pow_ge_self` (`n^k >= n` for any `k >= 1`, by
     induction on `k`: if `n = 0` both sides are `0`; if `n >= 1`
     multiplying by `n >= 1` never shrinks the running product) and
     `lemma_scale_ge_self` (`c * m >= m` for `c >= 1`, trivial for
     `nat`).

2. **`lemma_extract_oob`** (and its helper `lemma_extract_nat_oob`,
   proved by induction directly on `Z3SeqTheory.fst`'s `extract_nat`) —
   `extract s pos ln == empty` whenever `pos >= len s`, for *any*
   `ln`. This is exactly the semantic fact the new C++ branch relies
   on to ignore the `size` operand once the offset-dominates-length
   condition holds; it was not previously stated as a standalone lemma
   in `Z3SeqTheory.fst`, so it is proved here against that file's
   existing `extract`/`extract_nat` definitions (no new semantics
   introduced).

3. **`lemma_extract_length_power_offset_empty`** — the rewrite's full
   correctness, combining the two: for any sequence `s`, positive
   integers `c, k`, and any `size`,
   `extract s (c * pow (len s) k) size == empty`.
   This is the direct F* mirror of the new C++ branch's conclusion.

All three are proved with no `admit`/`assume`.

## Scope / what is not modeled

- The AST-level traversal in the C++ fix (flattening nested `seq.*`
  `*`-applications with a `ptr_buffer`/`obj_hashtable` visited-set to
  bound DAG size, and syntactically recognizing `str.len a` vs. other
  numeral factors) is ordinary tree-walking bookkeeping with no
  independent semantic content beyond correctly extracting the `c`,
  `k` this file's arithmetic lemma is stated over; it is not
  re-modeled, consistent with this audit series' treatment of other
  purely-syntactic traversal helpers (e.g. the `Uninterp` shape
  classification in `Z3ArrayGiveUp.fst`).
- The PR's own regression tests additionally check: (a) the rewrite
  does *not* fire for offsets that are not provably `>= len(a)` (e.g.
  `len(s) * len(t)` with an independent `t`, or a factor of `0`, or
  `len(s)^2 - 1`), and (b) an end-to-end regex/MBQI scenario across
  several random seeds now returns `unsat`. These are coverage/negative
  checks on the same classifier shape and traversal code, not new
  arithmetic content; the single positive-case theorem above is the
  property whose absence caused the regression.

## Verification

```
cd C:\z3\fstar
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqExtractLengthProduct.fst
```

Expected / actual output:
```
Verified module: Z3SeqExtractLengthProduct
All verification conditions discharged successfully
```

## Conclusion

The new rewrite in PR #11165 is sound: whenever the offset of a
`substr`/`extract` flattens to a product containing at least one
`str.len a` factor and only numeral factors `>= 1`, the offset is
provably `>= len(a)`, so (by `Z3SeqTheory.fst`'s own `extract`
semantics) the result is always the empty sequence, regardless of the
requested size. This closes the completeness gap (`unknown` via regex
unfolding timeout) reported in issue #11157 without weakening
soundness.
