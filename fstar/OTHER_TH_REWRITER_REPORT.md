# Other `th_rewriter.cpp` Plugins — Coverage Survey and Formalization Report

`src/ast/rewriter/th_rewriter.cpp` dispatches to nine theory-specific
rewriter plugins (`m_b_rw`, `m_a_rw`, `m_bv_rw`, `m_ar_rw`, `m_dt_rw`,
`m_f_rw`, `m_dl_rw`, `m_pb_rw`, `m_seq_rw`, `m_char_rw`, `m_rec_rw`,
`m_fs_rw`). This report surveys *all* of them, cross-references the
plugins already covered by earlier audits in this project, and adds new
coverage for the previously-unaudited `finite_set_rewriter.cpp`.

## Plugin-by-plugin status

| Plugin field | `.cpp` file | Status | Report |
|---|---|---|---|
| `m_b_rw` | `bool_rewriter.cpp` | ✅ covered | [`BOOL_ARITH_REWRITER_REPORT.md`](../BOOL_ARITH_REWRITER_REPORT.md) |
| `m_a_rw` | `arith_rewriter.cpp` | ✅ covered | [`BOOL_ARITH_REWRITER_REPORT.md`](../BOOL_ARITH_REWRITER_REPORT.md) |
| `m_bv_rw` | `bv_rewriter.cpp` | ✅ covered (first pass) | [`BV_REWRITER_REPORT.md`](../BV_REWRITER_REPORT.md) |
| `m_ar_rw` | `array_rewriter.cpp` | ✅ covered | [`ARRAY_REWRITER_REPORT.md`](../ARRAY_REWRITER_REPORT.md) |
| `m_dt_rw` | `datatype_rewriter.cpp` | ✅ covered (full) | [`DATATYPE_REWRITER_REPORT.md`](../DATATYPE_REWRITER_REPORT.md) |
| `m_f_rw` | `fpa_rewriter.cpp` | ✅ covered | [`FPA_REPORT.md`](../FPA_REPORT.md) |
| `m_seq_rw` | `seq_rewriter.cpp` | ✅ covered | [`SEQ_REWRITER_REPORT.md`](../SEQ_REWRITER_REPORT.md) |
| `m_fs_rw` | `finite_set_rewriter.cpp` | ✅ newly covered (this report) | below + [`Z3FiniteSetTheory.fst`](Z3FiniteSetTheory.fst) |
| `m_dl_rw` | `dl_rewriter.cpp` | ⚪ reviewed, trivial | below |
| `m_char_rw` | `char_rewriter.cpp` | ⚪ reviewed, trivial | below |
| `m_pb_rw` | `pb_rewriter.cpp` | ✅ covered (first pass) | [`PB_REWRITER_REPORT.md`](../PB_REWRITER_REPORT.md) |
| `m_rec_rw` | `recfun_rewriter.cpp` | ✅ covered (termination argument) | [`RECFUN_REWRITER_REPORT.md`](../RECFUN_REWRITER_REPORT.md) |

## `finite_set_rewriter.cpp` — newly formalized

`finite_set_rewriter.cpp` (added 2025) implements Z3's finite-set sort
(`set.empty`/`set.singleton`/`set.union`/`set.intersect`/`set.difference`/
`set.subset`/`set.in`/`set.size`/`set.range`/`set.map`/`set.filter`). It is
*distinct* from the extensional-array-based "set" family in
`array_rewriter.cpp` (an `(Array I Bool)`), modeled already in
`Z3ArrayTheory.fst`. `Z3FiniteSetTheory.fst` models it the same way —
extensionally-quotiented membership predicates via
`FStar.FunctionalExtensionality`'s `idx ^-> v`, but with a `prop` (rather
than `bool`) codomain, since `set.map`'s direct-image semantics is
naturally existential and an arbitrary element type need not support a
decidable membership test for the image set. Converting a pointwise `<==>`
fact into the `==`-based `feq` that `extensionality`'s `SMTPat` expects
requires `FStar.PropositionalExtensionality.apply`; this bridging step is
packaged once as `lemma_set_eq_from_iff` and reused by every identity
lemma.

| # | `.cpp` function | Rewrite | Lemma | Status |
|---|---|---|---|---|
| 1 | `mk_union` | `union(x,x) = x` | `lemma_union_idem` | ✅ |
| 2 | `mk_union` | `union(x,∅) = x`, `union(∅,x) = x` | `lemma_union_empty_r/l` | ✅ |
| 3 | `mk_union` | `union(x, intersect(x,y)) = x` (both orders) | `lemma_union_absorb_r/l` | ✅ |
| 4 | `mk_intersect` | `intersect(x,x) = x` | `lemma_intersect_idem` | ✅ |
| 5 | `mk_intersect` | `intersect(x,∅) = ∅`, `intersect(∅,x) = ∅` | `lemma_intersect_empty_r/l` | ✅ |
| 6 | `mk_intersect` | `intersect(x, union(x,y)) = x` (both orders) | `lemma_intersect_absorb_r/l` | ✅ |
| 7 | `mk_intersect` | `intersect(range(l1,u1),range(l2,u2)) = range(max(l1,l2),min(u1,u2))` | `lemma_intersect_ranges` | ✅ |
| 8 | `mk_difference` | `difference(x,x) = ∅` | `lemma_difference_self` | ✅ |
| 9 | `mk_difference` | `difference(x,∅) = x` | `lemma_difference_empty_r` | ✅ |
| 10 | `mk_difference` | `difference(∅,x) = ∅` | `lemma_difference_empty_l` | ✅ |
| 11 | `mk_subset` | `subset(x,x) <=> True`, `subset(∅,x) <=> True` | `lemma_subset_refl`, `lemma_subset_empty_l` | ✅ |
| 12 | `mk_subset` | `subset(x,∅) <=> x = ∅` | `lemma_subset_empty_r` | ✅ |
| 13 | `mk_subset` | general case: `subset(x,y) <=> intersect(x,y) = x` | `lemma_subset_iff_intersect` | ✅ |
| 14 | `mk_in` | `in(x,∅) <=> False` | `lemma_in_empty` | ✅ |
| 15 | `mk_in` | `in(x,singleton(y)) <=> x = y` | `lemma_in_singleton` | ✅ |
| 16 | `mk_in` | `in(x,range(lo,hi)) <=> lo<=x<=hi` | `lemma_in_range` | ✅ |
| 17 | `mk_size` | `size(∅)=0`, `size(singleton(x))=1`, `size(range(lo,hi))=ite(lo>hi,0,hi-lo+1)` | `size_empty`, `size_singleton`, `size_range` (+ `lemma_size_range_nonneg` sanity check) | ✅ |
| 18 | `mk_map` | `map(f,∅) = ∅` | `lemma_map_empty` | ✅ |
| 19 | `mk_map` | `map(f,singleton(x)) = singleton(f(x))` | `lemma_map_singleton` | ✅ |
| 20 | `mk_map` | `map(f, union(s,t)) = union(map(f,s), map(f,t))` | `lemma_map_union` | ✅ |
| 21 | `mk_map` (non-rewrite) | `map` does **not** distribute over `intersect`/`difference` (confirmed by the `.cpp`'s own comment) | `lemma_map_intersect_not_distributive` (explicit countermodel: `f=const false`, `s={true}`, `t={false}`) | ✅ (soundness-of-*not*-rewriting confirmed) |
| 22 | `mk_filter` | `filter(p,∅) = ∅` | `lemma_filter_empty` | ✅ |
| 23 | `mk_filter` | `filter(p,singleton(x)) = ite(p(x),singleton(x),∅)` | `lemma_filter_singleton` | ✅ |
| 24 | `mk_filter` | `filter(p,union(s,t)) = union(filter(p,s),filter(p,t))` | `lemma_filter_union` | ✅ |
| 25 | `mk_filter` | `filter(p,intersect(s,t)) = intersect(filter(p,s),filter(p,t))` | `lemma_filter_intersect` | ✅ |
| 26 | `mk_filter` | `filter(p,difference(s,t)) = difference(filter(p,s),filter(p,t))` | `lemma_filter_difference` | ✅ |

26/26 target rewrite families verified, zero `admit`/`assume`.

### Not covered (deferred, with rationale)

| Mechanism | Reason for deferral |
|---|---|
| `mk_eq_core`'s min-heap canonicalization (`min`/`get_min`/`is_less`/`from_unique_values`) | A model-finder decision procedure that normalizes `union`/`intersect`/`difference` expressions into a sorted "heap" of singletons/ranges so two *unique-valued* sets can be compared for disequality conclusively. Its correctness reduces entirely to the union/intersect/difference identities already verified above (#1–#10) plus a "distinct unique values are not equal" fact; the search/canonicalization strategy itself is solver engineering, analogous to `array_rewriter.cpp`'s deferred `has_index_set` expansion and `squash_store` search. |
| `set.map`'s interaction with `set.filter`/general n-ary chains | Not separately rewritten in the `.cpp`; `mk_map`/`mk_filter` recurse one constructor at a time, exactly as modeled. |

## `dl_rewriter.cpp` — reviewed, no dedicated lemma file

46 lines total, one function (`mk_app_core`, `OP_DL_LT` only): numeral
folding (`v1 < v2` on two concrete datalog numerals), irreflexivity
(`x < x <=> false`), `x < 0 <=> false`, and `0 < x <=> 0 <> x` for
non-negative `x`. Every one of these is a direct instance of integer order
facts (`<` irreflexive, `0` is the least non-negative numeral) that Z3's
own SMT arithmetic theory — and F*'s `int`/`nat` arithmetic — already
decides natively; writing a dedicated `.fst` lemma for each would only
restate `x < x` is `False` as an F* tautology, adding no verification
value. Reviewed in full; no soundness-relevant content beyond basic
integer order.

## `char_rewriter.cpp` — reviewed, no dedicated lemma file

92 lines total: `char` is Z3's bounded-code-point sort, represented
internally as an unsigned integer `0 <= n <= max_char`. Its five rewrites
(`mk_char_le`'s three short-circuits plus general numeral comparison,
`mk_char_to_int`, `mk_char_from_bv`, `mk_char_to_bv` — always `BR_FAILED`,
i.e. no rewrite — and `mk_char_is_digit`) are all direct projections onto
plain integer comparison/range-membership, with no bit-vector-style
packing, heuristic search, or algebraic identity distinct from "compare
two bounded naturals" / "check a numeral falls in `['0','9']`". As with
`dl_rewriter.cpp`, formalizing these as separate F* lemmas would only
restate integer facts already decided natively; reviewed in full, no
soundness-relevant content beyond bounded-integer comparison.

## `pb_rewriter.cpp` — now covered (first pass)

See [`PB_REWRITER_REPORT.md`](../PB_REWRITER_REPORT.md) and
[`Z3PbTheory.fst`](Z3PbTheory.fst) for the full write-up: formalizes the
core truth-preserving normalization identities (negative-coefficient
literal flip, trivial-true/trivial-false detection, tight-inequality →
all-literals-true, unit-coefficient → at-least-one-true, single-term
coefficient capping), deferring the gcd-based cutting-plane reduction and
the general slack-based conjunction/disjunction construction to a further
follow-up.

## `recfun_rewriter.cpp` — now covered (termination argument)

See [`RECFUN_REWRITER_REPORT.md`](../RECFUN_REWRITER_REPORT.md) and
[`Z3RecfunTheory.fst`](Z3RecfunTheory.fst) for the full write-up:
formalizes the structural-descent fact (`is_decreasing_arg`'s accessor
chains strictly shrink a structural size measure, so no infinite
unfolding sequence can exist) that certifies termination of recursive
function unfolding; the substitution step itself reuses
`Z3SimplifierTheory.fst`'s generic substitution-congruence lemma.

## Verification status

`Z3FiniteSetTheory.fst` compiles cleanly with `fstar.exe` (Z3 4.13.3
backend), zero `admit`/`assume`, as part of the project's full
clean-recompile check. `Z3PbTheory.fst` and `Z3RecfunTheory.fst` (added in
a follow-up pass) likewise compile cleanly with zero `admit`/`assume`.
