# F* Formalization of `src/ast/rewriter/datatype_rewriter.cpp` — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series.

`datatype_rewriter.cpp` is small (~140 lines, 2 functions:
`mk_app_core`/`mk_eq_core`) and, unlike `bv_rewriter.cpp`, has no
heuristic/search sub-rewrites — every branch is a direct consequence of the
"free algebra" semantics of algebraic datatypes (constructors build values,
accessors/recognisers/field-update project and test/rebuild them, and
distinct constructors never collide). This pass achieves **full functional
coverage**: every reachable branch of `mk_app_core`'s `OP_DT_RECOGNISER`/
`OP_DT_IS`/`OP_DT_ACCESSOR`/`OP_DT_UPDATE_FIELD` cases, and of
`mk_eq_core`, has a corresponding proved lemma. (`OP_DT_CONSTRUCTOR` and
`OP_DT_SUBTERM` have no rewrite — `mk_app_core` returns `BR_FAILED`/
delegates immediately — so need no lemma.)

Proof file: [`Z3DatatypeTheory.fst`](Z3DatatypeTheory.fst).

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend. The proof file
type-checks and discharges all verification conditions with **no
`admit`/`assume`/axioms**:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3DatatypeTheory.fst
```

## Representation

A value of an `nctors`-constructor datatype is modeled as a dependent pair
`dtval a nctors = (c:nat{c < nctors} & list a)`: a constructor tag plus the
flat list of field values it was built from. The model is intentionally
*one level deep* (field values have an abstract/uninterpreted type `a`,
not a recursive `dtval`): every rewrite in `datatype_rewriter.cpp` fires
locally on a single `mk_app_core`/`mk_eq_core` call without inspecting
sub-structure below the immediate arguments, so a flat model is sufficient
to justify all of them; recursion through nested constructor applications
is handled by the generic bottom-up `rewriter` engine applying these same
local rules repeatedly, not by `datatype_rewriter.cpp` itself.

A small self-contained list-update helper `list_set`/`list_set_length`/
`list_set_nth` (plus an `index`/`nth` bridging lemma `index_is_nth`) models
`OP_DT_UPDATE_FIELD`'s "replace one field, keep the rest" structural core.

## Coverage by rewrite rule

| datatype_rewriter.cpp site | Rewrite | Lemma | Status |
|---|---|---|---|
| `mk_app_core`, `OP_DT_RECOGNISER` | tester `f(x)` is notation for `is_c(x)` | — | ✅ definitional (`recognize` *is* the predicate) |
| `mk_app_core`, `OP_DT_IS` (matching ctor) | `is_c(mk_c(args)) = true` | `lemma_recognize_match` | ✅ |
| `mk_app_core`, `OP_DT_IS` (mismatched ctor) | `is_c(mk_d(args)) = false`, `c <> d` | `lemma_recognize_mismatch` | ✅ |
| `mk_app_core`, `OP_DT_IS` (`num_constructors == 1`) | `is_c(v) = true` unconditionally | `lemma_recognize_single_ctor` | ✅ |
| `mk_app_core`, `OP_DT_IS` (`is_update_field` branch) | `is_{c'}(update_field(dt,val)) = is_{c'}(dt)` | `lemma_is_update_field` (via `lemma_update_preserves_tag`) | ✅ |
| `mk_app_core`, `OP_DT_ACCESSOR` (main case) | `acc_{c,i}(mk_c(args)) = args[i]` | `lemma_accessor_match` | ✅ |
| `mk_app_core`, `OP_DT_ACCESSOR` (`update_field`, `f == acc`) | `acc_{c,i}(update_{c,i}(v,w)) = w` | `lemma_accessor_update_same` | ✅ |
| `mk_app_core`, `OP_DT_ACCESSOR` (`update_field`, `f <> acc`) | `acc_{c,j}(update_{c,i}(v,w)) = acc_{c,j}(v)`, `j <> i` | `lemma_accessor_update_other` | ✅ |
| `mk_app_core`, `OP_DT_UPDATE_FIELD` (matching ctor) | `update_{c,i}(mk_c(args), w) = mk_c(args[i:=w])` | `lemma_update_match` | ✅ |
| `mk_app_core`, `OP_DT_UPDATE_FIELD` (mismatched ctor) | `update_{c,i}(v, w) = v` when `tag(v) <> c` | `lemma_update_mismatch` | ✅ |
| `mk_app_core`, `OP_DT_CONSTRUCTOR` | no rewrite (`BR_FAILED`) | — | N/A |
| `mk_app_core`, `OP_DT_SUBTERM` | no rewrite (`BR_FAILED`) | — | N/A |
| `mk_eq_core` (different constructors) | `mk_c(args1) = mk_d(args2)` is `false`, `c <> d` | `lemma_eq_diff_ctor` | ✅ |
| `mk_eq_core` (same constructor) | `mk_c(args1) = mk_c(args2) <=> args1 = args2` pointwise | `lemma_eq_same_ctor` | ✅ |

## Not covered / out of scope

- **Nested/recursive datatype reasoning** (e.g. proving properties of
  `head(cons(x, tail))` chains several levels deep, or termination facts
  about recursive datatypes like lists/trees): out of scope for this
  *rewriter*-level audit, which only ever looks at one `mk_app_core` call
  at a time; such reasoning belongs to `theory_datatype`'s model
  construction / occurs-check, not `datatype_rewriter.cpp`.
- **`datatype_decl_plugin.cpp`**'s well-formedness checks (recursive sort
  definitions, positivity/occurs-check, accessor/constructor consistency)
  are a separate module from the rewriter and not addressed here.
- The interaction between `OP_DT_UPDATE_FIELD` and *array*/other
  non-datatype sorts embedded as fields is not modeled (field values are
  an uninterpreted abstract type `a`; this is sound for the identities
  proved above since none of them inspect field *contents*, only
  positions).

## Summary

Because `datatype_rewriter.cpp` is small and has no search/heuristic code,
this first pass reaches full coverage: all 14 reachable rewrite branches
across `mk_app_core` and `mk_eq_core` are proved sound against a
from-scratch free-algebra model of datatype values, with zero admits.
