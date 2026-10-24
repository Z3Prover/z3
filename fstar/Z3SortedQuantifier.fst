module Z3SortedQuantifier

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3Definitions
module R = Z3ResolutionProofTheory
module BR = Z3BooleanRewrite
module SB = Z3BinderSubstitution
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let rec quantifier_free (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App _ args -> quantifier_free_args args
  | Quantifier _ _ _ _ -> false

and quantifier_free_args (args:list expr) : Tot bool (decreases args) =
  match args with [] -> true | e :: rest -> quantifier_free e && quantifier_free_args rest

(* This constrains the logical operator, not the validity of a proof rule. *)
let forall_elimination_model (#base:sort -> Type0) (s:S.checked_schema)
                             (bc:S.boolean_carrier base)
                             (other:V.interpretation base (S.signature s)) : prop =
  forall (bound:list sort)
         (body:V.arguments base (S.signature s) (L.rev bound) ->
               V.value base (S.signature s) bool_sort)
         (vs:V.arguments base (S.signature s) (L.rev bound)).
    T.truth_value s bc (other.quantification Forall_k bound bool_sort body) ==>
    T.truth_value s bc (body vs)

let check (args:list expr) (formula:expr) : bool =
  match formula with
  | App f [App n [Quantifier Forall_k bs t body]; inst] ->
    D.scoped [] formula &&
    f = BR.connective_decl BR.Disjunction [App n [Quantifier Forall_k bs t body]; inst] &&
    n = R.not_decl && t = bool_sort &&
    D.scoped_args [] args && sorts_match (L.rev args) (L.rev bs) &&
    quantifier_free body && SB.substitute (L.rev args) body = Some inst
  | _ -> false

let lemma_forall_elimination (#base:sort -> Type0) (s:S.checked_schema)
                             (bc:S.boolean_carrier base)
                             (other:V.interpretation base (S.signature s))
                             (bound:list sort)
                             (body:V.arguments base (S.signature s) (L.rev bound) ->
                                   V.value base (S.signature s) bool_sort)
                             (vs:V.arguments base (S.signature s) (L.rev bound))
  : Lemma (requires forall_elimination_model s bc other)
          (ensures T.truth_value s bc (other.quantification Forall_k bound bool_sort body) ==>
                   T.truth_value s bc (body vs)) =
  ()

let rec lemma_lookup (#base:sort -> Type0) (sigma:V.signature)
                     (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                     (args:list expr) (ss:list sort)
                     (n:nat{n < L.length ss /\ n < L.length (ss @ [])})
                     (t:sort) (term:expr)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\ D.scoped [] term /\
                    SB.arguments args n t == Some term)
          (ensures V.extend sigma [] ss (V.evaluate_args sigma i [] rho args ss) rho n ==
                   V.evaluate sigma i [] rho term)
          (decreases args) =
  match args, ss with
  | _ :: rest, _ :: tail ->
    if n > 0 then lemma_lookup sigma i rho rest tail (n - 1) t term
  | _, _ -> ()

let rec lemma_substitute (#base:sort -> Type0) (sigma:V.signature)
                         (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                         (args:list expr) (ss:list sort) (body result:expr)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\
                    D.scoped (ss @ []) body /\ D.scoped [] result /\ quantifier_free body /\
                    SB.substitute args body == Some result)
          (ensures V.evaluate sigma i (ss @ [])
                     (V.extend sigma [] ss (V.evaluate_args sigma i [] rho args ss) rho) body ==
                   V.evaluate sigma i [] rho result)
          (decreases body) =
  match body, result with
  | Var n t, _ ->
    LP.append_l_nil ss;
    lemma_lookup sigma i rho args ss n t result
  | App f xs, App _ ys ->
    lemma_substitute_args sigma i rho args ss xs ys f.domain
  | _, _ -> ()

and lemma_substitute_args (#base:sort -> Type0) (sigma:V.signature)
                          (i:V.interpretation base sigma) (rho:V.environment base sigma [])
                          (args:list expr) (ss:list sort) (xs ys:list expr) (domain:list sort)
  : Lemma (requires D.scoped_args [] args /\ sorts_match args ss /\
                    D.scoped_args (ss @ []) xs /\ D.scoped_args [] ys /\
                    sorts_match xs domain /\ sorts_match ys domain /\ quantifier_free_args xs /\
                    SB.apply_args (SB.arguments args) xs == Some ys)
          (ensures V.evaluate_args sigma i (ss @ [])
                     (V.extend sigma [] ss (V.evaluate_args sigma i [] rho args ss) rho) xs domain ==
                   V.evaluate_args sigma i [] rho ys domain)
          (decreases xs) =
  match xs, ys, domain with
  | x :: rest, y :: tail, _ :: remaining ->
    lemma_substitute sigma i rho args ss x y;
    lemma_substitute_args sigma i rho args ss rest tail remaining
  | _, _, _ -> ()

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_equality base) (other:V.interpretation base (S.signature s))
                (args:list expr) (formula:expr)
  : Lemma (requires forall_elimination_model s bc other /\ check args formula)
          (ensures T.truth s bc eq other formula) =
  match formula with
  | App f [App n [Quantifier Forall_k bs t body]; inst] ->
    let sigma = S.signature s in
    let i = T.interpretation s bc eq other in
    let rho = T.empty_environment sigma in
    let scope = L.rev bs in
    let actuals = L.rev args in
    Z3QuantifierInstantiation.lemma_scoped_reverse_acc [] args [];
    let vs = V.evaluate_args sigma i [] rho actuals scope in
    let function_body = V.typed_body sigma bs bool_sort
      (V.evaluate_body sigma i [] rho bs body) in
    LP.append_l_nil scope;
    lemma_substitute sigma i rho actuals scope body inst;
    T.lemma_negation s bc eq other n (Quantifier Forall_k bs t body);
    T.lemma_nary s bc eq other f [App n [Quantifier Forall_k bs t body]; inst]
      Z3BoundedBoolEquiv.Or;
    assert (T.evaluate s bc eq other (Quantifier Forall_k bs t body) ==
            other.quantification Forall_k bs bool_sort function_body);
    lemma_forall_elimination s bc other bs function_body vs;
    assert (function_body vs == V.evaluate sigma i [] rho inst)
  | _ -> ()
