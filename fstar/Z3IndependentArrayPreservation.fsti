module Z3IndependentArrayPreservation

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module D = Z3ExprScope
module TR = Z3TypedRoot
module AI = Z3IndependentArrayInterpretation
module Root = Z3SortedRootDocument

let rec safe (sigma:V.signature) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var _ _ -> true
  | App f args -> None? (AI.target sigma f) && safe_args sigma args
  | Quantifier _ _ _ body -> safe sigma body

and safe_args (sigma:V.signature) (es:list expr) : Tot bool (decreases es) =
  match es with
  | [] -> true
  | e :: rest -> safe sigma e && safe_args sigma rest

let eligible (sigma:V.signature) (fuel:nat) (es:list expr) : Tot bool =
  match arguments_budget fuel es with
  | None -> false
  | Some _ -> safe_args sigma es

val lemma_evaluate (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature sch) scope)
  (e:expr{D.scoped scope e /\ safe (S.signature sch) e})
  : Lemma (
    V.evaluate (S.signature sch) (TR.standard u sch (AI.symbols u sch uf)) scope rho e ==
    V.evaluate (S.signature sch) (TR.standard u sch uf) scope rho e)

val lemma_arguments (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  (scope:list sort) (rho:V.environment (TR.carrier u) (S.signature sch) scope)
  (es:list expr{D.scoped_args scope es /\ safe_args (S.signature sch) es})
  (ss:list sort{sorts_match es ss})
  : Lemma (
    V.evaluate_args (S.signature sch) (TR.standard u sch (AI.symbols u sch uf)) scope rho es ss ==
    V.evaluate_args (S.signature sch) (TR.standard u sch uf) scope rho es ss)

val lemma_truths (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  (es:list expr{safe_args (S.signature sch) es})
  : Lemma (
    Root.root_truths u sch (TR.standard u sch (AI.symbols u sch uf)) es ==
    Root.root_truths u sch (TR.standard u sch uf) es)

val lemma_eligible_truths (u:TR.uninterpreted) (sch:S.checked_schema) (uf:TR.symbols u sch)
  (fuel:nat) (es:list expr{eligible (S.signature sch) fuel es})
  : Lemma (
    Root.root_truths u sch (TR.standard u sch (AI.symbols u sch uf)) es ==
    Root.root_truths u sch (TR.standard u sch uf) es)
