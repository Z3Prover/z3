# Array Rewriter Formalization Report

Formalization file: [`fstar/Z3ArrayTheory.fst`](fstar/Z3ArrayTheory.fst)
Subject: `src/ast/rewriter/array_rewriter.cpp`

## Model

Z3 models an `(Array I V)` sort as an *extensional* function from index to
value. We formalize this directly with F*'s
`FStar.FunctionalExtensionality.(^->)` restricted-arrow type:

```fstar
type arr (idx:eqtype) (v:Type) = idx ^-> v
```

This type's `==` equality is *already* extensionally quotiented (the
library's `extensionality` axiom: `a == b <==> (forall i. a i == b i)`, with
an `SMTPat` on `feq` so the fact fires automatically). This matches Z3's own
array extensionality axiom with zero additional proof burden, so
`mk_eq_core`'s rewrites literally *are* instances of the library's main
lemma applied to `select`.

Primitive operations modeled: `select`, `store`, `const_arr`
(`(as const ...)`), `map1`/`map2` (unary/binary `(_ map f)` — sufficient to
justify every identity `array_rewriter.cpp` proves, all of which push a
unary or binary function through), `arr_ite` (array-valued term-level
`ite`), and `set_t idx = arr idx bool` with `set_union`/`set_intersect`/
`set_complement`/`set_difference` built from `map2`/`map1`.

`idx` is required to be an `eqtype` (decidable equality), matching Z3's
requirement that array index sorts support `=`.

## Coverage table

| # | `array_rewriter.cpp` site | Rewrite | Lemma | Status |
|---|---|---|---|---|
| 1 | `mk_select_same_store` (`l_true`) | `select(store(a,I,v),I) = v` | `lemma_select_store_same` | ✅ |
| 2 | `mk_select_same_store` (`l_false`) / `mk_select_core` | `select(store(a,I,v),J) = select(a,J)`, `I≠J` | `lemma_select_store_diff` | ✅ |
| 3 | `mk_select_same_store` (`is_const`) | `select(const(c),I) = c` | `lemma_select_const` | ✅ |
| 4 | `mk_select_core` (`is_ite`) | `select(ite(c,a1,a2),J) = ite(c,select(a1,J),select(a2,J))` | `lemma_select_ite` | ✅ |
| 5 | `mk_select_same_store` (`is_lambda`) | `select(λi.f(i), I) = f(I)` | `lemma_select_lambda` | ✅ |
| 6 | `mk_store_core` (duplicate index) / `squash_store`'s 1-step building block | `store(store(a,I,v),I,w) = store(a,I,w)` | `lemma_store_same_twice` | ✅ |
| 7 | `mk_store_core` (`m_sort_store`, `I≠J`) | `store(store(a,I,v),J,w) = store(store(a,J,w),I,v)` | `lemma_store_commute` | ✅ |
| 8 | `mk_store_core` (redundant write) | `store(a,I,select(a,I)) = a` | `lemma_store_redundant` | ✅ |
| 9 | `mk_store_core` (constant-write collapse) | `store(const(v),I,v) = const(v)` | `lemma_store_const_same` | ✅ |
| 10 | `mk_lambda_core` (array eta) | `λi.select(a,i) = a` | `lemma_lambda_eta` | ✅ |
| 11 | `mk_map_core` (defining property) | `select(map_f(a1,a2),I) = f(select(a1,I),select(a2,I))` | `lemma_select_map2`, `lemma_select_map1` | ✅ |
| 12 | `mk_map_core` (push-through-store, same index) | `map_f(store(a1,J,v1),store(a2,J,v2)) = store(map_f(a1,a2),J,f(v1,v2))` | `lemma_map2_store` | ✅ |
| 13 | `mk_map_core` (all-constant) | `map_f(const(c1),const(c2)) = const(f(c1,c2))` | `lemma_map2_const` | ✅ |
| 14 | `mk_map_core` (all-lambda) | `map_f(λi.g1(i), λi.g2(i)) = λi.f(g1(i),g2(i))` | `lemma_map2_lambda` | ✅ |
| 15 | `mk_set_union` | `union(a,b) = map_or(a,b)` | `set_union` + `lemma_set_union_select` | ✅ |
| 16 | `mk_set_intersect` | `intersect(a,b) = map_and(a,b)` | `set_intersect` + `lemma_set_intersect_select` | ✅ |
| 17 | `mk_set_complement` | `complement(a) = map_not(a)` | `set_complement` + `lemma_set_complement_select` | ✅ |
| 18 | `mk_set_difference` | `difference(a,b) = intersect(a,complement(b))` | `set_difference` (definitional) | ✅ |
| 19 | `mk_set_subset` | `subset(a,b) <=> difference(a,b) = ∅` | `set_subset_iff` (proved equivalent to pointwise `∀i. a(i) ⟹ b(i)`) | ✅ |
| 20 | `mk_eq_core` (extensionality axiom itself) | `a = b <=> ∀i. select(a,i) = select(b,i)` | `lemma_array_extensionality` | ✅ |
| 21 | `mk_eq_core` (`const = const`) | `const(c1) = const(c2) <=> c1 = c2` | `lemma_eq_const_const` | ✅ |
| 22 | `mk_eq_core` (`const = λ`) | `const(c) = λi.f(i) <=> ∀i. f(i) = c` | `lemma_eq_const_lambda` | ✅ |
| 23 | `mk_eq_core` (`λ = λ`) | `λi.f(i) = λi.g(i) <=> ∀i. f(i) = g(i)` | `lemma_eq_lambda_lambda` | ✅ |

23/23 target rewrite families verified, zero `admit`/`assume`.

**Note on #21** (`lemma_eq_const_const`): requires an explicit index witness
`i0:idx` as a parameter. SMT-LIB array index sorts are always non-empty, but
`eqtype` alone does not guarantee this to F* — without a witness, `∀i:idx. c1
= c2` is vacuously true when `idx` is uninhabited, which would make the
`<==>` false. This mirrors the real semantics (Z3 sorts are never empty).

## Not covered (deferred, with rationale)

| Mechanism | Location | Reason for deferral |
|---|---|---|
| Partial-equality (PEQ) rules | `mk_app_core`, `is_partial_eq`/`store_ext` dispatch | `theory_array`-internal bookkeeping term (`PEQ`), not a semantic rewrite of array values — it is a search/propagation device, analogous to deferred solver-internal heuristics in other reports. |
| `squash_store`'s general n-level search | `mk_store_core` | Iteratively re-applies the 1-step dedup/commute identities (#6/#7, already verified) to an arbitrarily long chain of nested stores; the search/termination strategy itself is not a distinct semantic rule. |
| AC-flattening of nested `and`/`or` maps | `mk_map_core`, `m().is_and(f)`/`m().is_or(f)` branches | Associative-commutative sorting/flattening search over map trees, analogous to the heuristic equation-solving rewrites deferred in `BV_REWRITER_REPORT.md`; not a new semantic identity beyond #11–14. |
| Finite-domain array-equality expansion (`has_index_set`/`add_store`/`is_expandable_store`/`expand_store`/`has_large_domain`/`domain_is_larger_than`) | `mk_eq_core`, lines ~723–1020 | A case-split/quantifier-elimination heuristic that expands `store`-chain equalities into a finite conjunction of index-value equalities when the domain is small or uninterpreted; its correctness reduces to repeated application of extensionality (#20) and the store/select identities above (#1–#9), already covered, but the expansion search itself (deciding *which* finite conjunction to emit) is solver-engineering, not a new semantic law. The `#if 0`-guarded `has_index_set` "lambda friendly" variant is additionally dead code. |
| True n-ary `map`/n-ary `store`/`select` on multi-dimensional arrays | throughout | Modeled here via the unary/binary `map1`/`map2` building blocks, which suffice to justify every identity actually proved (all are unary or binary `f`); a fully n-ary treatment would not change any proved lemma's statement, only its arity. |

## Verification status

`Z3ArrayTheory.fst` compiles cleanly with `fstar.exe` (Z3 4.13.3 backend),
zero `admit`/`assume`, as part of the project's full clean-recompile check.
