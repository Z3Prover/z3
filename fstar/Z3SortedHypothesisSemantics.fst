module Z3SortedHypothesisSemantics

open Z3AstTheory
module H = Z3HypothesisSemantics
module C = Z3ClausalSemantics
module R = Z3ClauseSyntax
module D = Z3ExprScope
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module B = Z3BoundedBoolEquiv
module L = FStar.List.Tot
module P = Z3ProofTheory
module Ops = Z3CanonicalOps

let valid (scope:list sort) (e:expr) : bool =
  D.scoped scope e && get_sort e = bool_sort

let rec lemma_or_atoms (rho:C.valuation) (es:list expr)
  : Lemma (B.geval_args rho B.Or (L.map B.Atom es) == C.clause_holds rho es)
          (decreases es) =
  match es with
  | [] -> ()
  | _ :: rest -> lemma_or_atoms rho rest

let rec lemma_boolean_sorts (ss:list sort)
  : Lemma (Ops.boolean_sorts ss == T.boolean_sorts ss) (decreases ss) =
  match ss with [] -> () | _ :: rest -> lemma_boolean_sorts rest

let rec lemma_valid_args (scope:list sort) (es:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope es /\ sorts_match es ss /\ T.boolean_sorts ss)
          (ensures H.valid_list (valid scope) es)
          (decreases es) =
  match es, ss with
  | [], [] -> ()
  | _ :: rest, _ :: tail -> lemma_valid_args scope rest tail
  | _, _ -> ()

let lemma_valid_clause (scope:list sort) (e:expr)
  : Lemma (requires valid scope e)
          (ensures H.valid_list (valid scope) (R.formula_clause e)) =
  match e with
  | App f args ->
    if Ops.canonical_or f then (
      lemma_boolean_sorts f.domain;
      lemma_valid_args scope args f.domain)
  | _ -> ()

let lemma_complement (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (a b:expr)
  : Lemma (requires valid scope a /\ valid scope b /\ C.complementary a b)
          (ensures T.truth_at s bc eq other scope rho a ==
                   not (T.truth_at s bc eq other scope rho b)) =
  if P.is_not a = Some b then (
    T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 a;
    match a with | App _ [_] -> () | _ -> ())
  else if P.is_not b = Some a then (
    T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 b;
    match b with | App _ [_] -> () | _ -> ())
  else (
    T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 a;
    T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 b;
    match a, b with | App _ [], App _ [] -> () | _, _ -> ())

let lemma_clause (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                 (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                 (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires valid scope e)
          (ensures T.truth_at s bc eq other scope rho e ==
                   C.clause_holds (T.truth_at s bc eq other scope rho) (R.formula_clause e)) =
  T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 e;
  match e with
  | App f args ->
    if Ops.canonical_or f then (
      lemma_boolean_sorts f.domain;
      T.lemma_evaluate_core_at s bc eq other scope rho f args;
      T.lemma_boolean_arguments_at s bc eq other scope rho args f.domain B.Or;
      lemma_or_atoms (T.truth_at s bc eq other scope rho) args)
    else if Ops.canonical_false f && args = [] then ()
    else ()
  | _ -> ()

let lemma_model (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : Lemma (H.complements_from_false (T.truth_at s bc eq other scope rho) (valid scope) /\
           H.clause_from_formula (T.truth_at s bc eq other scope rho) (valid scope)) =
  let complement (a b:expr)
    : Lemma (valid scope a /\ valid scope b /\ C.complementary a b /\
             not (T.truth_at s bc eq other scope rho b) ==>
             T.truth_at s bc eq other scope rho a) =
    let aux (_:squash (valid scope a /\ valid scope b /\ C.complementary a b /\
                       not (T.truth_at s bc eq other scope rho b)))
      : Lemma (T.truth_at s bc eq other scope rho a) =
      lemma_complement s bc eq other scope rho a b in
    FStar.Classical.impl_intro aux in
  let clause (e:expr)
    : Lemma (valid scope e /\ not (T.truth_at s bc eq other scope rho e) ==>
             not (C.clause_holds (T.truth_at s bc eq other scope rho) (R.formula_clause e))) =
    if valid scope e then lemma_clause s bc eq other scope rho e in
  FStar.Classical.forall_intro_2 complement;
  FStar.Classical.forall_intro clause
