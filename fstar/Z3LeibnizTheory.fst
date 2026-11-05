module Z3LeibnizTheory

(*
   F* formalization of `src/ast/simplifiers/leibniz_simplifier.cpp`'s
   soundness, as a follow-up pass to `SIMPLIFIERS_REPORT.md`'s first
   pass.

   Despite its name (chosen for the Leibniz/congruence *flavor* of
   substituting one variable's uses), this simplifier does not
   perform a rewrite at all -- it never replaces or removes the
   `forall` it examines. It *adds* new, independently-standing axioms
   to the problem by a direct application of first-order universal
   instantiation: given `forall (x1,...,xn). P(x1,...,xn)`, and a
   closed-enough "witness" term `w` (not depending on one target
   variable `xi`, built from an occurrence pattern `arr[w]` found in
   the body, see `collect_witnesses`), it adds the new axiom
   `forall (x1,...,xi-1,xi+1,...,xn). P(x1,...,w,...,xn)` -- the
   original quantifier block with `xi` instantiated to `w` and the
   remaining variables kept universally quantified. `try_instantiate`
   does this once per collected witness (if there are at least 2, a
   usefulness heuristic, not a soundness precondition), reindexing the
   remaining de Bruijn variables down by one and wrapping `w` itself
   as an array/set-indicator predicate `\y. y = w` when `xi`'s sort is
   a Boolean-ranged unary array sort (`try_instantiate`'s loop over
   `m_array.is_array(s)`/`get_array_range(s) == bool_sort`).

   Soundness content: this is *exactly* the standard FOL rule
   "(forall x y. P x y) ==> (forall y. P t y)" for any term `t` not
   depending on `y` -- curried so that `x` is the eliminated variable
   and `y` ranges over (a single abstract type standing in for) all
   the *other* simultaneously-bound variables, exactly as
   `Z3SimplifierTheory.fst`'s n-ary `distribute_forall` lemmas model
   "the rest of a quantifier block" abstractly rather than
   positionally. F*'s own `forall` *is* this rule already (`forall
   x y. P x y` unfolds, via currying, to `forall x. forall y. P x
   y`, from which `forall y. P t y` for any fixed `t` is immediate);
   stating it explicitly below, rather than leaving it entirely
   implicit, documents precisely which fact underlies the `.cpp`'s
   soundness and records the (vacuous, by construction) side
   condition that the witness `t` must not itself depend on the
   eliminated variable -- `t`'s type `dom1` simply has no way to
   mention the bound `x:dom1` it is replacing, matching
   `collect_witnesses`'s explicit `contains_var_idx` rejection of any
   witness mentioning the target variable.
*)

/// The core rule: instantiating one variable of a (curried, two-level)
/// universal statement at a fixed witness `t`, while keeping the
/// other variable(s) (abstracted as the single type `other`) universally
/// quantified, is a valid consequence. `dom1` is the sort of the
/// variable `leibniz_simplifier.cpp` eliminates (`q->get_decl_sort(i)`,
/// always a unary-array-to-bool sort in the `.cpp`, but the rule holds
/// for any sort); `other` abstracts "every other simultaneously bound
/// variable of the quantifier block" as one combined type, matching
/// `Z3SimplifierTheory.fst`'s treatment of quantifier blocks.
let lemma_forall_instantiate (#dom1 #other:Type) (p:dom1 -> other -> prop) (t:dom1)
  : Lemma (requires (forall (x:dom1) (o:other). p x o))
          (ensures (forall (o:other). p t o))
  = ()

/// The specific witness shape `try_instantiate` builds when the
/// eliminated variable's sort is a Boolean-ranged unary array sort
/// (`get_array_range(s) = bool_sort`, modeled here as `d -> bool`,
/// matching `Z3ArrayTheory.fst`'s array-as-function model): the
/// witness predicate `\y:d. y = w` (`witness_pred` in the `.cpp`) is
/// just the indicator function of the single point `w`. Applying
/// `lemma_forall_instantiate` with `dom1 = (d -> bool)` and `t = (fun
/// y -> y = w)` is exactly `try_instantiate`'s construction; this
/// corollary spells out that specialization so the "witness predicate"
/// terminology is traceable directly to a term of the general lemma
/// above (no new proof content -- `()` suffices given the general
/// lemma, since `t = (fun y -> y = w) : d -> bool` is just one
/// instance of a `dom1`-typed witness).
let lemma_leibniz_array_witness (#d:eqtype) (#other:Type) (p:(d -> bool) -> other -> prop) (w:d)
  : Lemma (requires (forall (arr:d -> bool) (o:other). p arr o))
          (ensures (forall (o:other). p (fun y -> y = w) o))
  = lemma_forall_instantiate #(d -> bool) #other p (fun y -> y = w)

(* ----------------------------------------------------------------- *)
(* Not covered (deferred, documented in LEIBNIZ_SIMPLIFIER_REPORT.md)  *)
(* ----------------------------------------------------------------- *)

(* The de Bruijn reindexing of the *other* `n-1` bound variables
   (`remap`/`var_subst` in `try_instantiate`) and the construction of
   `collect_witnesses`'s candidate witness set from `arr[w]` select
   occurrences are pure bookkeeping/heuristic-search concerns with no
   independent soundness content once `lemma_forall_instantiate` is
   granted: any well-sorted, variable-capture-free renumbering of "the
   other decls" into a smaller quantifier block denotes the same
   `other`-typed universal statement this file's `other` type abstracts
   away, by construction (the only possible failure mode -- getting a
   de Bruijn index wrong -- is a bug in the renumbering arithmetic, not
   a gap in the soundness argument). Likewise `m_rewriter`'s
   post-instantiation simplification and dropping instances that
   simplify to `true` (`m.is_true(simplified)`) are sound by
   construction of whatever rewriter is plugged in (already covered,
   where exercised, by the bool/arith/array rewriter audits), and the
   "need >= 2 distinct witnesses" / `m_max_witnesses` cutoffs are
   usefulness heuristics, not soundness preconditions -- the rule holds
   for a single witness too. *)
