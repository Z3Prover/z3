# `ast/simplifiers` Formalization Report — First Pass

Formalization file: [`fstar/Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst)
(built on the pre-existing generic AST model in
[`fstar/Z3AstTheory.fst`](Z3AstTheory.fst)).

## Scope decision

`src/ast/simplifiers/` contains 29 files, ranging from 12 to 1274 lines.
Reading across all of them, the large majority of their logic is
*search/scheduling* machinery specific to each file (which subterm to visit
next, how to track proof/unsat-core dependencies through a rewrite, when to
stop iterating, bit-blasting/slicing encodings, congruence-closure
bookkeeping) layered on top of a **small number of recurring semantic
primitives**. Rather than spread a first pass thin across all 29 files, this
pass formalizes those recurring primitives directly and precisely, each
anchored to one representative file, and documents the rest as a
file-by-file follow-up queue (below) for later passes — consistent with the
"first pass establishes core theories, then follow-up passes increase
coverage" approach used for the bit-vector/array/datatype audits.

Two primitives were identified and formalized this pass:

1. **Quantifier/connective distributivity** (`distribute_forall.cpp`):
   `forall x. (F1/\.../\Fn) <=> (forall x.F1)/\.../\(forall x.Fn)`, and the
   dual `exists`/`or` law. This is a textbook-valid first-order law.
2. **Ground-term substitution congruence** (`propagate_values.cpp`, and —
   by the same underlying lemma — `solve_eqs.cpp`/
   `solve_context_eqs.cpp`/`extract_eqs.cpp`): replacing every occurrence of
   a closed sub-term by another closed sub-term that denotes the same value
   preserves the enclosing formula's meaning. This is the semantic
   justification for *every* simplifier in the directory that works by
   "found `x` equals some value/term `v`; rewrite all its occurrences to
   `v`" (propagate_values's `m_subst`, solve_eqs's substitution map,
   extract_eqs's `expr_substitution` consumers, and the demodulator).

## Model

`Z3AstTheory.fst` (pre-existing, built for the regex track) already supplies
exactly the right level of abstraction: a generic expression AST (`Var`/
`App`/`Quantifier`, de Bruijn-indexed), a well-sortedness/closedness
judgment, and a denotational semantics (`eval`) parameterized by an
arbitrary `interpretation value` — a domain-polymorphic model of FOL
semantics, not committed to any one theory. `Z3SimplifierTheory.fst` adds:

- The distributivity lemmas are stated directly with F*'s own
  `forall`/`exists`/`prop` connectives over an abstract domain `dom:Type`
  (not via `Z3AstTheory`'s `expr`/`eval`): F*'s classical-logic quantifiers
  *are* Tarskian FOL quantifiers, so this is a faithful formalization, not
  an analogy. The n-ary (list-of-conjuncts) case the `.cpp` actually
  implements is proved by induction from the binary case.
- `subst`/`subst_args`: a plain syntactic replace-all-occurrences function
  over `Z3AstTheory.expr`.
- `lemma_subst_cong`/`lemma_subst_cong_args`: proved by structural induction
  over `expr`, using `Z3AstTheory`'s pre-existing `closed`/
  `lemma_closed_eval_env_irrelevant` machinery to justify substituting
  under quantifier binders without variable-capture concerns (a *closed*
  replacement term's denotation cannot depend on which binders enclose the
  position being replaced).

## Coverage table

| # | `.cpp` site | Property | Lemma | Status |
|---|---|---|---|---|
| 1 | `distribute_forall.cpp`, `is_forall` case (binary) | `forall x.(F1/\F2) <=> (forall x.F1)/\(forall x.F2)` | `lemma_forall_distributes_and` | ✅ |
| 2 | `distribute_forall.cpp`, `is_exists` case (binary) | `exists x.(F1\/F2) <=> (exists x.F1)\/(exists x.F2)` | `lemma_exists_distributes_or` | ✅ |
| 3 | `distribute_forall.cpp`, `is_forall` + `flatten_and` (n-ary, as actually implemented) | `forall x.(F1/\.../\Fn) <=> (forall x.F1)/\.../\(forall x.Fn)` | `lemma_forall_distributes_and_list` | ✅ |
| 4 | `distribute_forall.cpp`, `is_exists` + `flatten_or` (n-ary, as actually implemented) | `exists x.(F1\/.../\Fn) <=> (exists x.F1)\/.../\(exists x.Fn)` | `lemma_exists_distributes_or_list` | ✅ |
| 5 | `propagate_values.cpp`'s `process_fml`/`add_sub` (and, structurally, `solve_eqs.cpp`/`solve_context_eqs.cpp`/`extract_eqs.cpp`'s substitution-application step) | substituting a closed term `a` by a closed, denotationally-equal term `b` throughout any expression preserves its meaning | `lemma_subst_cong`, `lemma_subst_cong_args` | ✅ |

5/5 target properties verified, zero `admit`/`assume`.

**Note on #5**: `add_sub`'s three concrete registration cases (`x` shared
and `¬x` present ⟹ register `x := false`; `f` shared ⟹ register
`f := true`; `x = y` with `y` a value ⟹ register `x := y`) are all
*instances* of the same `lemma_subst_cong` fact with a different
denotationally-equal closed pair — documented in the file rather than
re-proved three times, since re-proving would only re-derive
`lemma_subst_cong` with concrete `old_`/`new_` plugged in.

## Not covered in this pass (file-by-file follow-up queue)

| File | Lines | What it adds beyond the primitives above |
|---|---|---|
| `solve_eqs.cpp` / `solve_context_eqs.cpp` / `extract_eqs.cpp` | 334/306/488 | *Which* equations are safe to orient and extract as substitutions (acyclicity/occurs-check, choosing a solved form, interaction with Boolean structure) — the substitution-application step itself is `lemma_subst_cong` (done), but the equation-solving search is not yet formalized. |
| `eliminate_predicates.cpp` | 932 | Macro/definition-elimination for predicate symbols defined by a single Horn-like equation — a substitution-like soundness argument but over a different granularity (relation symbols, not sub-terms) and with cyclicity/polarity side conditions. |
| `elim_unconstrained.cpp` | 416 | Soundness of replacing a sub-term that provably has no back-reference (occurs in no other constraint) with a fresh variable — a *satisfiability-preserving* (not meaning-preserving) rewrite, a strictly different and harder property than `lemma_subst_cong`'s meaning-preservation. |
| `euf_completion.cpp` | 1274 | Congruence-closure-based rewriting under a maintained equivalence relation; the core congruence rule is related to but more general than `lemma_subst_cong` (closure under *all* ground equalities simultaneously, not one at a time). |
| `bound_propagator.cpp` / `bound_manager.cpp` / `bound_simplifier.cpp` / `bv_bounds_simplifier.cpp` / `bv_divrem_bounds.cpp` | 865/269/592/60/34 | Interval-arithmetic soundness (`x in [lo,hi] /\ y in [lo',hi'] ==> x+y in [lo+lo', hi+hi']`-style propagation rules). |
| `bit_blaster.cpp` / `bv1_blaster.cpp` / `bv_slice.cpp` | 64/276/195 | Bit-vector-to-Boolean encoding correctness (each bit-vector operation's blasted Boolean circuit computes the same function as `Z3BvTheory.fst`'s semantics) — a natural extension of the existing bit-vector audit. |
| `card2bv.cpp` | 47 | Cardinality-constraint-to-bit-vector/Boolean encoding soundness (relates to the deferred `pb_rewriter.cpp` PB-constraint semantics). |
| `max_bv_sharing.cpp` | 55 | Pure structural hash-consing/sharing (no semantic rewrite — provably a no-op on meaning by construction, not meaningfully formalizable beyond that one-line observation). |
| `dominator_simplifier.cpp` | 266 | A generic "simplify dominated sub-formula under a context" traversal scheduler layered over an arbitrary `simplifier_plugin`; its soundness reduces to whatever plugin it is parameterized with. |
| `demodulator_simplifier.cpp` | 193 | Equation-as-rewrite-rule application (`lhs ~> rhs` from a universally-quantified equation) — a quantified generalization of `lemma_subst_cong` (substitution under a matching substitution for the equation's free variables, not just ground terms). |
| `leibniz_simplifier.cpp` | 168 | Named directly after the congruence law `lemma_subst_cong` formalizes; its generalization replaces one *argument position* of a congruence class representative, a natural near-term follow-up. |
| `lambda_simplifier.cpp` | 164 | Lambda-lifting/array-comprehension-specific rewriting, relates to `Z3ArrayTheory.fst`'s eta/beta lemmas (`mk_lambda_core`). |
| `reduce_args_simplifier.cpp` | 379 | Argument-position congruence-based reduction (replacing `f(..., t, ...)` occurrences sharing an argument value) — another near-term extension of `lemma_subst_cong`. |
| `factor_simplifier.cpp` | 247 | Polynomial/term factoring normalization. |
| `fold_unfold.cpp` | 365 | Recursive-function fold/unfold rewriting, relates to `recfun_rewriter.cpp` (deferred in `OTHER_TH_REWRITER_REPORT.md`). |
| `recfun_finder.cpp` | 483 | Recursive-function definition discovery (a syntactic classification pass, not a rewrite). |
| `linear_equation.cpp` | 257 | Linear-arithmetic equation normal-form bookkeeping (Gaussian-elimination-style). |
| `model_reconstruction_trail.cpp` | 259 | Bookkeeping to reconstruct a model for the original formula from a model of the simplified one — correctness of *this* is actually the most important cross-cutting property of the whole directory (every simplifier above needs its reconstruction step to be inverse-correct), and is the natural top priority for the next follow-up pass. |
| `dependent_expr_state.cpp` | 133 | Generic container/dependency-tracking infrastructure shared by all simplifiers above (not itself a semantic rewrite). |
| `randomizer.cpp` | 12 | Test-only shuffling utility, no semantic content. |

## Verification status

`Z3SimplifierTheory.fst` compiles cleanly with `fstar.exe` (Z3 4.13.3
backend), zero `admit`/`assume` (only pre-existing-style `decreases`-clause
warnings inherited from `Z3AstTheory.fst`'s mutually-recursive `expr`/
`list expr` definitions, not errors), as part of the project's full
clean-recompile check.
