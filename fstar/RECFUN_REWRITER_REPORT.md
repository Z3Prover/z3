# F* Formalization of `src/ast/rewriter/recfun_rewriter.cpp` — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series.

`recfun_rewriter.cpp` unfolds a call `f(args)` to a user-defined recursive
function into its (substituted) right-hand side, `d.get_rhs()`, under one
of two conditions:

1. **every argument is already a fully-evaluated value** (`m.is_value`),
   in which case the call is simply being evaluated — unfolding is sound
   by definition of what the recursive function's equation means, the
   same "sound by construction" status as numeral constant-folding
   elsewhere in this audit series (bit-vector/arithmetic rewriters); or
2. **some argument position `i` is a ground constructor application**,
   *and* `is_decreasing_arg(f, i, true)` has certified that every
   recursive call to `f` inside `d`'s body threads position `i` only
   through a **strict chain of datatype accessors** applied to the very
   same formal parameter — ruling out the possibility that the body
   *rebuilds* a constructor term for position `i` from unrelated data and
   recurses on something that isn't actually smaller (the scenario the
   `.cpp`'s own comment calls out: `(f (tail s) (mk (proj_1 t) ...))`
   recursing on a sequence `s`).

Case 2's **termination guarantee** — that this accessor-chain discipline
actually prevents the unfolding rewrite from looping forever — is the
genuinely new semantic content formalized here. The substitution step
itself (`var_subst`) is the generic ground-term substitution congruence
already proved, independent of this file, in `Z3SimplifierTheory.fst`
(`lemma_subst_cong`/`lemma_subst_cong_args`).

Proof file: [`Z3RecfunTheory.fst`](Z3RecfunTheory.fst).

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3RecfunTheory.fst
```

Type-checks and discharges all verification conditions with **no
`admit`/`assume`/axioms**.

## Representation

A ground datatype value is modeled recursively as `dval = DCon of tag:nat
* args:list dval` — a constructor tag plus a (possibly empty) list of
field sub-values, which may themselves be further `DCon` applications
(unlike `Z3DatatypeTheory.fst`'s flat, one-level `dtval`, this model is
*recursive*, since the termination argument is precisely about nested
constructor structure). `size`/`size_list` (mutually recursive) count the
total number of constructor applications nested inside a value — a
structural measure in which accessor projection is always strictly
decreasing.

## Coverage

| `.cpp` site | Property | Lemma | Status |
|---|---|---|---|
| (implicit: `OP_DT_ACCESSOR` applied to a ground constructor term) | projecting any field out of a constructor application yields a strictly smaller value | `lemma_accessor_decreases` / `lemma_accessor_step_decreases` | ✅ |
| `is_decreasing_arg`'s accessor-chain walk (`while (is_app(a) && u.is_accessor(a)) a = to_app(a)->get_arg(0)`) | a nonempty ("strict") chain of accessor steps, if it succeeds, strictly decreases the size of the original value | `lemma_chain_decreases` (uses `lemma_fold_step`/`lemma_fold_none`) | ✅ |
| **`is_decreasing_arg`'s termination guarantee** (why requiring a strict accessor chain on every recursive call makes unfolding terminate) | no infinite sequence of accessor-guarded unfoldings can exist, since it would give an infinite strictly-decreasing sequence of natural numbers (impossible) | `lemma_decreasing_arg_unfolding_terminates` (uses the general `lemma_no_infinite_descent`) | ✅ |
| `mk_app_core`'s `safe_to_subst` (all-value-arguments) branch | unfolding a call whose arguments are all already values | — | N/A — sound by definition, same status as constant folding elsewhere in this audit series |
| `var_subst`'s capture-avoiding substitution | substitution congruence | `Z3SimplifierTheory.fst`'s `lemma_subst_cong`/`lemma_subst_cong_args` | ✅ (proved elsewhere, reused here by reference) |

## Not yet covered (deferred to follow-up passes)

- **`is_decreasing_arg`'s exact syntactic check** (walking `subterms::all`
  of the body to find every occurrence of the de Bruijn-indexed formal
  parameter, confirming each is used only as an accessor/recognizer/`is`
  argument, and — in the `allow_any_accessor` branch — confirming every
  recursive call to `f` passes a strict accessor chain of that parameter
  at the matching position) is not itself formalized as a decision
  procedure; this report formalizes *why* the property it checks for
  (accessor-chain descent) guarantees termination, not that the `.cpp`'s
  AST traversal correctly decides that property.
- **`is_recfun_with_ground_recursion_args`**: a related but distinct
  predicate (used by the model finder, not the rewriter) classifying
  whether a term has at least one ground, decreasing, datatype-sorted
  argument among possibly-non-ground (uninterpreted-sort) arguments; not
  modeled here.
- **Mutual/multiple recursive functions and multiple simultaneously
  decreasing argument positions**: the model here captures a single
  decreasing argument's descent; Z3's recursive-function framework allows
  mutual recursion across several functions, which would need a
  multi-measure (lexicographic or mutual) well-founded order to fully
  capture — deferred.

## Summary

This pass formalizes the structural-descent fact that makes
`is_decreasing_arg`'s accessor-chain discipline a sound termination
certificate: datatype accessors strictly shrink a structural size
measure, so no infinite chain of accessor-guarded unfoldings can exist.
Combined with the substitution-congruence lemma already proved in
`Z3SimplifierTheory.fst`, this covers the two semantically load-bearing
facts behind `recfun_rewriter.cpp`'s unfolding rewrite; the `.cpp`'s own
AST-traversal decision procedure for recognizing the accessor-chain
pattern is deferred to a follow-up pass.
