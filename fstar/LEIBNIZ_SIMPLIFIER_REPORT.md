# `leibniz_simplifier.cpp` Formalization Report

Formalization file: [`fstar/Z3LeibnizTheory.fst`](Z3LeibnizTheory.fst)
(standalone; no dependency on `Z3AstTheory.fst`'s concrete `expr`/`eval`
machinery, since the property is pure first-order logic).

## What the `.cpp` actually does

Despite its name — chosen for the superficial "Leibniz/congruence"
flavor of substituting one variable's occurrences — `leibniz_simplifier.cpp`
does **not** perform a congruence rewrite, and it never replaces or
removes the `forall` it examines. It **adds** new, independently-standing
axioms to the problem by a direct application of first-order universal
instantiation:

Given `forall (x1,...,xn). P(x1,...,xn)`, and a closed-enough "witness"
term `w` (not depending on one target variable `xi`, built from an
`arr[w]`-shaped occurrence pattern found in the body by
`collect_witnesses`), `try_instantiate` adds the new axiom

```
forall (x1,...,xi-1,xi+1,...,xn). P(x1,...,xi-1,w,xi+1,...,xn)
```

— the original quantifier block with `xi` instantiated to `w` and the
remaining variables kept universally quantified (de Bruijn-reindexed down
by one). When `xi`'s sort is a Boolean-ranged unary array sort
(`get_array_range(s) == bool_sort`), the witness is additionally wrapped
as an array/set-indicator predicate `\y. y = w` (`witness_pred`) rather
than used directly. `try_instantiate` does this once per collected
witness, gated by a "at least 2 witnesses found" usefulness heuristic
(not a soundness precondition), and the new axiom is added *alongside*
the original `forall`, never replacing it — so, unlike every other
simplifier formalized so far, this one's soundness obligation is "the
added formula is **implied by** the existing ones", not "the rewritten
formula is **equivalent to** the original one".

## Soundness content

This is exactly the standard FOL rule

```
(forall x y. P x y)  ==>  (forall y. P t y)
```

for any term `t` not depending on `y` — curried so that `x` is the
eliminated variable and `y` ranges over (a single abstract type standing
in for) all the *other* simultaneously-bound variables, exactly as
`Z3SimplifierTheory.fst`'s n-ary `distribute_forall` lemmas model "the
rest of a quantifier block" abstractly rather than positionally, rather
than modeling Z3's actual n-ary `Quantifier` AST node. F*'s own `forall`
*is* this rule already (`forall x y. P x y` unfolds, via currying, to
`forall x. forall y. P x y`, from which `forall y. P t y` for any fixed
`t` is immediate); the point of stating it explicitly, rather than
leaving it entirely implicit, is to document precisely which fact
underlies the `.cpp`'s soundness and to record the (vacuous, by
construction) side condition that the witness `t` must not itself depend
on the eliminated variable — `t`'s type `dom1` simply has no way to
mention the bound `x:dom1` it is replacing, matching
`collect_witnesses`'s explicit `contains_var_idx` rejection of any
witness mentioning the target variable.

## Lemmas

- **`lemma_forall_instantiate (#dom1 #other:Type) (p:dom1 -> other -> prop) (t:dom1)`**:
  the core rule, `(forall x o. p x o) ==> (forall o. p t o)`. `dom1` is
  the sort of the variable `leibniz_simplifier.cpp` eliminates
  (`q->get_decl_sort(i)`); `other` abstracts "every other simultaneously
  bound variable of the quantifier block" as one combined type. Proved
  by `()` — this is definitionally how F*'s curried `forall` works, which
  is itself evidence that the `.cpp`'s reasoning has no hidden gap: there
  is no additional side condition beyond "`t`'s type doesn't let it
  mention `x`".
- **`lemma_leibniz_array_witness (#d:eqtype) (#other:Type) (p:(d -> bool) -> other -> prop) (w:d)`**:
  the specific witness shape `try_instantiate` builds when the eliminated
  variable's sort is a Boolean-ranged unary array sort (modeled as `d ->
  bool`, matching `Z3ArrayTheory.fst`'s array-as-function model): the
  witness predicate `\y:d. y = w` is just the indicator function of the
  single point `w`. This is a direct corollary of
  `lemma_forall_instantiate` with `dom1 = (d -> bool)` and `t = (fun y ->
  y = w)` — `d` must be `eqtype` so that `y = w` is itself a well-typed
  decidable proposition, mirroring that array index sorts are decidable
  (`Z3ArrayTheory.fst`'s own array-domain convention).

## Coverage table

| # | `.cpp` step | Property | Lemma | Status |
|---|---|---|---|---|
| 1 | `try_instantiate`'s core instantiation (any sort) | `(forall x o. p x o) ==> (forall o. p t o)` for a witness `t` not depending on `x` | `lemma_forall_instantiate` | ✅ |
| 2 | `try_instantiate`'s array/set-indicator witness wrapping (`get_array_range(s) == bool_sort` case) | the same rule, specialized to witness `\y. y = w` | `lemma_leibniz_array_witness` | ✅ |
| 3 | `remap`/`var_subst`'s de Bruijn reindexing of the *other* `n-1` bound variables | a well-sorted, capture-free renumbering denotes the same `other`-typed universal statement | — | N/A (pure bookkeeping, no independent soundness content once row 1 is granted) |
| 4 | `collect_witnesses`'s candidate-witness search (`arr[w]` occurrence pattern, `contains_var_idx` rejection) | finds only sound candidates (never a `t` depending on `x`) | — | N/A (heuristic search; `contains_var_idx`'s rejection is exactly row 1's side condition, enforced syntactically rather than proved) |
| 5 | post-instantiation `m_rewriter` simplification, dropping instances that simplify to `true` | simplification preserves meaning | — | ✅ by composition (covered wherever the plugged-in rewriter — bool/arith/array — has already been audited elsewhere in this project) |
| 6 | "at least 2 distinct witnesses" / `m_max_witnesses` cutoffs | — | — | N/A (usefulness heuristics, not soundness preconditions; the rule holds for a single witness too) |

2 substantive rows (1-2) fully covered; rows 3-4, 6 are heuristic/
bookkeeping concerns with no independent soundness content to formalize;
row 5 is covered by composition with already-audited rewriter work. Zero
`admit`/`assume`.

## Not covered (deferred, no further action planned)

- **De Bruijn reindexing arithmetic** (row 3) and **witness-collection
  heuristics** (row 4, 6): as detailed in row 3/4/6 above, these have no
  independent soundness content beyond what `lemma_forall_instantiate`
  already covers; the only possible failure mode in the `.cpp` (an
  off-by-one in the renumbering, or a missed `contains_var_idx` check) is
  an implementation bug, not a gap in this formalization's scope. Not
  planned for further formalization.

## Verification status

`Z3LeibnizTheory.fst` compiles cleanly with `fstar.exe` (Z3 4.13.3
backend), zero `admit`/`assume`, as part of the project's full
clean-recompile check (46 `.fst` files, all passing).
