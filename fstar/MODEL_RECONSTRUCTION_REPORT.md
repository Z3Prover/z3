# `model_reconstruction_trail.cpp` Formalization Report

Formalization file: [`fstar/Z3ModelReconstructionTheory.fst`](Z3ModelReconstructionTheory.fst)
(built on [`fstar/Z3AstTheory.fst`](Z3AstTheory.fst) and
[`fstar/Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst)).

## Why this file

`SIMPLIFIERS_REPORT.md`'s follow-up queue flagged
`model_reconstruction_trail.cpp` as "the most important cross-cutting
property of the whole directory": every simplifier formalized so far (and
every one still queued) eliminates some symbol or sub-formula from the
problem on the understanding that a *model of the simplified problem* can
always be turned back into a *model of the original problem* by replaying
how it was eliminated. `model_reconstruction_trail.cpp` is exactly the
mechanism that performs this replay (`replay`, `get_model_converter`), so
its correctness is a standing soundness assumption behind every other file
in the directory, not an independent, isolable rewrite rule the way (e.g.)
`distribute_forall.cpp`'s law is.

## Scope decision

The `.cpp` supports three kinds of trail entry (`src/ast/simplifiers/model_reconstruction_trail.h/.cpp`):

1. **`is_def()`** (`replace_vars_trail`/`updt_trail` registering
   `macro_replacer`-style function definitions): an eliminated symbol `f`
   of arity `n >= 0` is replaced throughout the problem by a body with `n`
   formal parameters (`f(x1,...,xn) ~> def(x1,...,xn)`). Reconstructing
   `f`'s value in the model requires evaluating `def` with the formals
   bound to the actual call's arguments.
2. **`is_subst()`** (`expr_replacer`-style ground substitution): one
   *closed* sub-term is replaced by another throughout the problem — this
   is exactly `Z3SimplifierTheory.subst`/`lemma_subst_cong`'s territory,
   already covered.
3. **"Loose" entries** (`is_loose_subst()`/`is_loose_constraint()`/general
   loose): a scheduling decision, not a rewrite — when a removed formula's
   free variables become newly relevant again (intersect `cond`'s free
   variables during replay), the entry is deactivated and the formula is
   re-inserted into the state instead of being used to extend the model.

This first pass formalizes case 1 **restricted to arity 0** (`f` an
eliminated *constant*, `def` a *closed* definition) — the shape actually
produced by `propagate_values.cpp`, `solve_eqs.cpp`,
`solve_context_eqs.cpp`, and `extract_eqs.cpp` (a shared atom/variable
found equal to a closed term; see their entries in `SIMPLIFIERS_REPORT.md`)
— and states the fact that is genuinely *new* relative to the already-proved
`lemma_subst_cong`: that lemma fixes an interpretation and relates two
*terms* under it; model reconstruction instead fixes an already-performed
term rewrite and relates two *interpretations* (the one found for the
simplified problem, and its canonical, mechanically-constructed extension
for the original one), showing the extension is forced to agree with the
syntactic substitution that produced the simplified problem in the first
place. This is the precise soundness content of
`generic_model_converter::add`/`convert` as driven by `replay`.

Case 2 is already covered (no new work needed: `lemma_subst_cong` *is* the
soundness argument for `is_subst()` entries, with the roles of "formula"
and "term being eliminated" matching exactly). Case 1 with arity `> 0` and
case 3 are deferred (see below).

## Model

New in `Z3ModelReconstructionTheory.fst`:

- `update_interp i f g`: the interpretation agreeing with `i` on every
  uninterpreted symbol except `f`, whose interpretation is replaced by `g`
  — the semantic counterpart of `generic_model_converter::add(f, def)`
  installing one new model entry.
- `macro_interp i0 def rho0`: the constant function `f` is given by a `def`
  entry — `def` evaluated under the model built so far (`i0`). `rho0` is an
  arbitrary ambient environment, needed only because `eval` is total and
  `value` is otherwise fully abstract (no inhabitant can be conjured
  without one); since `def` is required *closed*, `rho0`'s actual content
  never affects the result (`lemma_macro_interp_env_irrelevant`, via
  `Z3AstTheory.lemma_closed_eval_env_irrelevant`).
- `lemma_sorts_match_nil`: a small helper (`sorts_match args [] ==> args =
  []`) needed to rule out ill-formed arity mismatches when reasoning about
  `f`'s unique (empty-argument) occurrence.
- `lemma_model_reconstruction`/`lemma_model_reconstruction_args` (mutually
  recursive, by structural induction on `expr`/`list expr`, mirroring
  `lemma_subst_cong`'s shape): the main theorem. For any closed `def`,
  arity-0 uninterpreted `f`, well-formed `e`, and any two environments
  `rho0` (fixed once, seeding `macro_interp`) and `rho` (the one `e` is
  evaluated under, which *does* change — shifted — when recursing under a
  `Quantifier`):
  ```
  eval (update_interp i0 f (macro_interp i0 def rho0)) e rho
    == eval i0 (subst e (App f []) def) rho
  ```
  i.e. evaluating `e` under the canonically-extended model agrees with
  evaluating `e`'s already-performed elimination rewrite under the
  original (simplified-problem) model. Composing this lemma along the
  whole trail — oldest elimination's extension applied first, each
  building on the previous one's extended model, exactly as `replay`
  iterates the trail — reconstructs a model of the fully original,
  pre-simplification problem from a model of the final simplified one.

### A subtlety the proof had to get right

An initial attempt built the extended interpretation `i1` once at the top
of the induction using the *same* environment variable that also gets
shifted (`shift vs rho`) when recursing under a `Quantifier`. Since
`macro_interp i0 def (shift vs rho)` and `macro_interp i0 def rho` are
different F* closures (even though *semantically* equal, because `def` is
closed), and plain F* function types (`list value -> value`, as used in
`interpretation`'s fields) have no built-in extensionality axiom, this made
`i1` a syntactically different interpretation at each recursion depth,
which the typechecker could not reconcile. The fix: give the theorem two
separate environment parameters — `rho0` (only ever used to seed
`macro_interp`, held fixed through the whole recursion) and `rho` (the
environment `e` is evaluated under, which does get shifted). This keeps
`i1` a single, syntactically fixed interpretation throughout, sidestepping
any need for function extensionality.

## Coverage table

| # | `.cpp` entry kind | Property | Lemma | Status |
|---|---|---|---|---|
| 1 | `is_subst()` (`expr_replacer`, ground substitution) | reconstructing a model by inverting a closed-term-for-closed-term substitution | `Z3SimplifierTheory.lemma_subst_cong` (already proved; applies directly) | ✅ |
| 2 | `is_def()`, arity 0 (`macro_replacer`, eliminated constant) | extending a model of the simplified problem by assigning the eliminated constant's definition reconstructs a model of the original problem | `lemma_model_reconstruction`, `lemma_model_reconstruction_args` | ✅ |
| 3 | `is_def()`, arity > 0 (eliminated function symbol with formal parameters) | same, generalized to functions: requires De Bruijn-index shifting of `def` when inlined under nested binders (`f(t1,...,tn)` occurring under a quantifier needs `def`'s formal-parameter references renumbered relative to that quantifier's own bound variables) | — | ❌ deferred |
| 4 | "loose" entries (`is_loose_subst()`/`is_loose_constraint()`/general) | correctness of *re-inserting* a removed formula instead of extending the model, when its free variables become newly relevant during replay | — | ❌ deferred |
| 5 | `hide_trail` entries | a hidden symbol must not be reported in the externally-visible model | — | ❌ deferred (no semantic content beyond "don't report `f`"; not a soundness-relevant rewrite) |
| 6 | `get_model_converter`/`append`'s chaining of successive trail entries into one `generic_model_converter` | composing `lemma_model_reconstruction` along a whole trail (a `list` of `(f, def)` pairs applied in sequence) reconstructs a model for the whole original problem | — | ❌ deferred (a straightforward `List.Tot.fold`-style iteration of the single-entry lemma already proved; not yet spelled out as its own lemma) |

2/6 rows covered (the two that matter most in practice: the already-proved
ground-substitution case, and the new arity-0 definition case), zero
`admit`/`assume`.

## Not covered (deferred, documented for a later follow-up pass)

- **Arity-`n > 0` macro definitions** (row 3): the real soundness content
  generalizing `lemma_model_reconstruction` is unchanged (evaluate `def`
  with formals bound to actuals, under the model built so far), but
  *stating* it precisely requires a capture-avoiding "instantiate formals
  `Var 0..n-1` with the actual argument expressions, shifting any of
  `def`'s own de Bruijn indices that cross a binder" operation — a small
  but real additional piece of substitution machinery beyond what
  `Z3SimplifierTheory.subst`'s ground, non-shifting substitution provides.
- **Loose re-insertion entries** (row 4): this is a *scheduling* soundness
  argument ("is it still safe to treat this symbol as fully eliminated, or
  must the original constraint be re-examined because a newly-visible
  variable makes it relevant again") rather than a rewrite-preserves-
  meaning argument; formalizing it meaningfully would require modeling the
  trail's *replay state machine* (which formulas are currently "active" vs
  "removed"), not just a single elimination step in isolation.
- **Trail composition** (row 6): mechanical given row 2, deferred only for
  lack of time in this pass — a `list`-indexed induction applying
  `lemma_model_reconstruction` once per trail entry, each time with `i0`
  replaced by the previous step's extended interpretation.

## Verification status

`Z3ModelReconstructionTheory.fst` compiles cleanly with `fstar.exe` (Z3
4.13.3 backend), zero `admit`/`assume`, as part of the project's full
clean-recompile check.
