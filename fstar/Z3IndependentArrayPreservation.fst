module Z3IndependentArrayPreservation

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3ExprScope
module TR = Z3TypedRoot
module AI = Z3IndependentArrayInterpretation
module Root = Z3SortedRootDocument
module FE = FStar.FunctionalExtensionality
module L = FStar.List.Tot

let rec lemma_evaluate (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                       (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                       (e:expr{D.scoped scope e /\ safe (S.signature sch) e})
  : Lemma (
    V.evaluate (S.signature sch) (TR.standard u sch (AI.symbols u sch uf)) scope rho e ==
    V.evaluate (S.signature sch) (TR.standard u sch uf) scope rho e)
    (decreases %[(V.expression_size e <: nat); (0 <: nat)]) =
  let sigma = S.signature sch in
  let newer = TR.standard u sch (AI.symbols u sch uf) in
  let older = TR.standard u sch uf in
  match e with
  | Var _ _ -> ()
  | App f args ->
    lemma_arguments u sch uf scope rho args f.domain;
    if not (L.mem f sigma) then
      AI.lemma_preserves_application u sch uf f (V.evaluate_args sigma older scope rho args f.domain)
  | Quantifier k bound _ body ->
    let left = V.evaluate_body sigma newer scope rho bound body in
    let right = V.evaluate_body sigma older scope rho bound body in
    let pointwise (vs:TR.targuments u sch (L.rev bound)) : Lemma (left vs == right vs) =
      lemma_evaluate u sch uf (L.rev bound @ scope)
        (V.extend sigma scope (L.rev bound) vs rho) body in
    FStar.Classical.forall_intro pointwise;
    assert (FE.feq_g left right);
    FE.extensionality_g (TR.targuments u sch (L.rev bound)) (fun _ -> V.tree (TR.carrier u)) left right;
    assert (left == right);
    AI.lemma_preserves_quantification u sch uf k bound (get_sort body)
      (V.typed_body sigma bound (get_sort body) left)

and lemma_arguments (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                    (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature sch) scope)
                    (es:list expr{D.scoped_args scope es /\ safe_args (S.signature sch) es})
                    (ss:list sort{sorts_match es ss})
  : Lemma (
    V.evaluate_args (S.signature sch) (TR.standard u sch (AI.symbols u sch uf)) scope rho es ss ==
    V.evaluate_args (S.signature sch) (TR.standard u sch uf) scope rho es ss)
    (decreases %[(V.expressions_size es <: nat); (1 <: nat)]) =
  match es, ss with
  | e :: rest, s :: remaining ->
    V.lemma_sort_eq (get_sort e) s;
    lemma_evaluate u sch uf scope rho e;
    lemma_arguments u sch uf scope rho rest remaining
  | _, _ -> ()

let rec lemma_truths (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                     (es:list expr{safe_args (S.signature sch) es})
  : Lemma (
    Root.root_truths u sch (TR.standard u sch (AI.symbols u sch uf)) es ==
    Root.root_truths u sch (TR.standard u sch uf) es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if D.scoped [] e && get_sort e = bool_sort then
      lemma_evaluate u sch uf [] (Root.empty_root u sch) e;
    lemma_truths u sch uf rest

let lemma_eligible_truths (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
                          (fuel:nat) (es:list expr{eligible (S.signature sch) fuel es})
  : Lemma (
    Root.root_truths u sch (TR.standard u sch (AI.symbols u sch uf)) es ==
    Root.root_truths u sch (TR.standard u sch uf) es) =
  lemma_truths u sch uf es
