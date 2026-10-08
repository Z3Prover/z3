module Z3SimplifierTheory

(*
   F* formalization of the core semantic properties underlying two
   `src/ast/simplifiers/*.cpp` preprocessors, as the first pass of the
   "ast/simplifiers" audit stage.

   Scope decision for this first pass: `ast/simplifiers` contains 29
   files; most of their logic is *search/scheduling* machinery (which
   subterm to rewrite next, how to track dependencies for unsat cores,
   when to stop iterating) built on top of a small number of recurring
   *semantic* primitives. This pass formalizes those two recurring
   primitives directly, each exercised by one representative file, with
   later passes expected to extend coverage file-by-file:

     1. `distribute_forall.cpp`'s quantifier/connective distributivity
        law (`forall x. (F1 /\ ... /\ Fn)  <=>  (forall x.F1) /\ ... /\
        (forall x.Fn)`, and the dual for `exists`/`or`) -- a standard
        valid first-order law, stated and discharged directly using
        F*'s own `forall`/`exists` as the semantic quantifiers (which
        is a faithful, not merely suggestive, formalization: F*'s
        classical-logic `forall`/`exists` connectives obey exactly the
        Tarskian semantics this rewrite relies on).

     2. `propagate_values.cpp`'s (and, by the same argument,
        `solve_eqs.cpp`/`solve_context_eqs.cpp`/`extract_eqs.cpp`'s)
        core soundness primitive: substituting a *closed* sub-term `a`
        by another closed sub-term `b` throughout a formula preserves
        the formula's meaning, provided `a` and `b` denote the same
        value under every interpretation (`m_subst.insert(x, v, dep)`
        followed by rewriting every occurrence of `x` to `v`). This is
        proved as a generic congruence/Leibniz-substitution lemma over
        `Z3AstTheory`'s expression model, by structural induction on
        the host expression.
*)

open Z3AstTheory

(* ----------------------------------------------------------------- *)
(* distribute_forall.cpp                                               *)
(* ----------------------------------------------------------------- *)

/// `forall x. (F1 /\ F2) <=> (forall x. F1) /\ (forall x. F2)` --
/// `rw_cfg::reduce_quantifier`'s `is_forall` case for two conjuncts
/// (the general n-ary `flatten_and` case follows by repeated
/// application, see `lemma_forall_distributes_and_list` below). Proved
/// directly: this is a standard valid first-order law (distributivity
/// of a universal quantifier over conjunction), and F*'s own
/// `forall`/`exists` connectives have exactly the semantics this
/// relies on, so stating it with F*'s logical connectives *is* the
/// formalization, not merely an analogy to one.
let lemma_forall_distributes_and (#dom:Type) (p q:dom -> prop)
  : Lemma ((forall (x:dom). p x /\ q x) <==> (forall (x:dom). p x) /\ (forall (x:dom). q x))
  = ()

/// Dual: `exists x. (F1 \/ F2) <=> (exists x. F1) \/ (exists x. F2)` --
/// `rw_cfg::reduce_quantifier`'s `is_exists` case.
let lemma_exists_distributes_or (#dom:Type) (p q:dom -> prop)
  : Lemma ((exists (x:dom). p x \/ q x) <==> (exists (x:dom). p x) \/ (exists (x:dom). q x))
  = ()

/// The n-ary case the `.cpp` actually implements (`flatten_and` then
/// one `forall` per conjunct): `forall x. (F1/\.../\Fn) <=>
/// (forall x.F1) /\ ... /\ (forall x.Fn)`, modeling the conjunct list
/// as `ps : list (dom -> prop)` and folding both directions with the
/// same `/\`. `all_hold ps x` is "every conjunct holds at `x`";
/// `all_forall ps` is "every conjunct's own `forall` holds".
let rec all_hold (#dom:Type) (ps:list (dom -> prop)) (x:dom) : prop =
  match ps with
  | [] -> True
  | p :: ps' -> p x /\ all_hold ps' x

let rec all_forall (#dom:Type) (ps:list (dom -> prop)) : prop =
  match ps with
  | [] -> True
  | p :: ps' -> (forall (x:dom). p x) /\ all_forall ps'

let rec lemma_forall_distributes_and_list (#dom:Type) (ps:list (dom -> prop))
  : Lemma (ensures (forall (x:dom). all_hold ps x) <==> all_forall ps)
  = match ps with
    | [] ->
      assert_norm (all_forall #dom [] == True);
      let aux (x:dom) : Lemma (all_hold #dom [] x == True) = assert_norm (all_hold #dom [] x == True) in
      FStar.Classical.forall_intro aux
    | p :: ps' ->
      lemma_forall_distributes_and_list ps';
      lemma_forall_distributes_and p (fun x -> all_hold ps' x);
      assert_norm (all_forall (p :: ps') == ((forall (x:dom). p x) /\ all_forall ps'));
      let aux (x:dom) : Lemma (all_hold (p :: ps') x == (p x /\ all_hold ps' x)) =
        assert_norm (all_hold (p :: ps') x == (p x /\ all_hold ps' x)) in
      FStar.Classical.forall_intro aux

/// Dual n-ary case for `exists`/`or` (`is_exists`/`flatten_or`).
let rec any_holds (#dom:Type) (ps:list (dom -> prop)) (x:dom) : prop =
  match ps with
  | [] -> False
  | p :: ps' -> p x \/ any_holds ps' x

let rec any_exists (#dom:Type) (ps:list (dom -> prop)) : prop =
  match ps with
  | [] -> False
  | p :: ps' -> (exists (x:dom). p x) \/ any_exists ps'

let rec lemma_exists_distributes_or_list (#dom:Type) (ps:list (dom -> prop))
  : Lemma (ensures (exists (x:dom). any_holds ps x) <==> any_exists ps)
  = match ps with
    | [] ->
      assert_norm (any_exists #dom [] == False);
      let aux (x:dom) : Lemma (any_holds #dom [] x == False) = assert_norm (any_holds #dom [] x == False) in
      FStar.Classical.forall_intro aux
    | p :: ps' ->
      lemma_exists_distributes_or_list ps';
      lemma_exists_distributes_or p (fun x -> any_holds ps' x);
      assert_norm (any_exists (p :: ps') == ((exists (x:dom). p x) \/ any_exists ps'));
      let aux (x:dom) : Lemma (any_holds (p :: ps') x == (p x \/ any_holds ps' x)) =
        assert_norm (any_holds (p :: ps') x == (p x \/ any_holds ps' x)) in
      FStar.Classical.forall_intro aux

(* Not covered (deferred, documented in the report): the pattern-free
   precondition `!old_q->get_num_patterns() && !old_q->get_num_no_patterns()`
   is a performance/pattern-duplication-avoidance guard, not a
   soundness precondition -- the distributivity law above is valid
   with or without patterns present, since patterns are merely
   e-matching hints with no effect on a quantifier's denotation. This
   module's `dom -> prop` model has no notion of patterns at all,
   which is the right level of abstraction: patterns are outside the
   soundness-relevant semantics. *)

(* ----------------------------------------------------------------- *)
(* propagate_values.cpp (and, by the same lemma, solve_eqs.cpp /       *)
(* solve_context_eqs.cpp / extract_eqs.cpp's shared substitution core) *)
(* ----------------------------------------------------------------- *)

/// Substitute every syntactic occurrence of `old_` by `new_` in `e`.
/// Sound (see `lemma_subst_cong` below) whenever `old_`/`new_` are
/// *closed* (ground) terms that denote the same value under every
/// interpretation: substituting under a binder is then capture-free,
/// since a closed term's meaning cannot depend on which binders
/// enclose the occurrence being replaced. This matches
/// `propagate_values.cpp`'s actual usage: `m_subst.insert(x, v, dep)`
/// only ever registers substitutions for *shared* sub-expressions
/// (`x`, a Boolean atom or a variable found equal to a value `v`),
/// which are necessarily ground/ordinary terms at the point of
/// substitution, never a quantifier's bound variable itself.
let rec subst (e old_ new_ : expr) : expr =
  if e = old_ then new_
  else match e with
       | Var _ _ -> e
       | App f args -> App f (subst_args args old_ new_)
       | Quantifier qk bound_sorts body -> Quantifier qk bound_sorts (subst body old_ new_)

and subst_args (args:list expr) (old_ new_ : expr) : list expr =
  match args with
  | [] -> []
  | a :: args' -> subst a old_ new_ :: subst_args args' old_ new_

/// The soundness property: if `old_` and `new_` are both closed and
/// denote the same value in every environment (equivalently, under
/// the single empty environment, by
/// `lemma_closed_eval_env_irrelevant`), then replacing every
/// occurrence of `old_` by `new_` inside any `e` does not change `e`'s
/// denotation. This is exactly the semantic justification for
/// `propagate_values::process_fml`'s rewrite-via-substitution step
/// (and, structurally, for every other simplifier in this directory
/// that rewrites by registering and applying a "replace this
/// sub-term by that value" substitution: `solve_eqs.cpp`,
/// `solve_context_eqs.cpp`, `extract_eqs.cpp`'s `expr_substitution`
/// consumers).
let rec lemma_subst_cong
    (#value:Type) (i:interpretation value) (e old_ new_ : expr) (rho:env value)
  : Lemma (requires quant_extensional i /\ closed old_ /\ closed new_ /\
                     (forall (rho':env value). eval i old_ rho' == eval i new_ rho'))
          (ensures eval i (subst e old_ new_) rho == eval i e rho)
  = if e = old_ then ()
    else match e with
         | Var _ _ -> ()
         | App f args -> lemma_subst_cong_args i args old_ new_ rho
         | Quantifier qk bound_sorts body ->
           let n = List.Tot.length bound_sorts in
           let aux (vs:list value{List.Tot.length vs = n})
             : Lemma (eval i (subst body old_ new_) (shift vs rho) == eval i body (shift vs rho))
             = lemma_subst_cong i body old_ new_ (shift vs rho)
           in
           FStar.Classical.forall_intro aux

and lemma_subst_cong_args
    (#value:Type) (i:interpretation value) (args:list expr) (old_ new_ : expr) (rho:env value)
  : Lemma (requires quant_extensional i /\ closed old_ /\ closed new_ /\
                     (forall (rho':env value). eval i old_ rho' == eval i new_ rho'))
          (ensures eval_args i (subst_args args old_ new_) rho == eval_args i args rho)
  = match args with
    | [] -> ()
    | a :: args' ->
      lemma_subst_cong i a old_ new_ rho;
      lemma_subst_cong_args i args' old_ new_ rho

/// `add_sub`'s two concrete substitution-registration cases are
/// instances of `lemma_subst_cong`, not separate lemmas: `x` found
/// shared and `not(x)` present registers `x := false`
/// (`eval i x rho == eval i (App false_decl []) rho`, i.e. `x`
/// denoting the same thing as literal `false`, is exactly the
/// `old_ == new_`-under-every-environment hypothesis above with
/// `old_ = x`, `new_ = false`); likewise `f` shared registers
/// `f := true`, and `x = y` with `y` a value registers `x := y`. All
/// three are the same congruence fact, applied with a different pair
/// of denotationally-equal closed terms.
