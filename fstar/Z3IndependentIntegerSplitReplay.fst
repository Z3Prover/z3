module Z3IndependentIntegerSplitReplay

open Z3AstTheory
open FStar.List.Tot
module A = Z3LinearArithmeticAst
module AR = Z3SortedArithmetic
module D = Z3ExprScope
module G = Z3LpGomorySyntax
module I = Z3IndependentIntegerSplit
module L = FStar.List.Tot
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let check (c:G.certificate) (conclusion:expr) (facts:list expr) : bool =
  D.scoped [] c.split && get_sort c.split = A.int_s &&
  D.scoped [] conclusion && get_sort conclusion = bool_sort &&
  R.formula_clause conclusion = [conclusion] &&
  AR.check_contradiction (A.assumptions conclusion (facts @ [G.branch false c])) c.below &&
  AR.check_contradiction (A.assumptions conclusion (facts @ [G.branch true c])) c.above

let rec lemma_append_truth (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s)) (facts:list expr) (extra:expr)
  : Lemma (requires T.truths s bc model other facts /\ T.truth s bc model other extra)
          (ensures T.truths s bc model other (facts @ [extra]))
          (decreases facts) =
  match facts with
  | [] -> ()
  | _ :: rest -> lemma_append_truth s bc model other rest extra

let rec lemma_assumptions (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s)) (facts:list expr) (conclusion:expr)
  : Lemma (requires T.truths s bc model other facts /\ not (T.truth s bc model other conclusion) /\
                    R.formula_clause conclusion == [conclusion])
          (ensures AR.assumptions_hold s bc model other (A.assumptions conclusion facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | _ :: rest -> lemma_assumptions s bc model other rest conclusion

let lemma_branch (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (c:G.certificate) (conclusion:expr) (facts:list expr) (upper:bool)
  : Lemma (requires check c conclusion facts /\ T.truths s bc model other facts /\
                    T.truth s bc model other (G.branch upper c))
          (ensures T.truth s bc model other conclusion) =
  if not (T.truth s bc model other conclusion) then (
    let branch = G.branch upper c in
    let weights = if upper then c.above else c.below in
    lemma_append_truth s bc model other facts branch;
    lemma_assumptions s bc model other (facts @ [branch]) conclusion;
    AR.lemma_check_contradiction s bc model other
      (A.assumptions conclusion (facts @ [branch])) weights)

let lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (c:G.certificate) (conclusion:expr) (facts:list expr)
  : Lemma (requires check c conclusion facts /\ T.truths s bc model other facts)
          (ensures T.truth s bc model other conclusion) =
  I.lemma_split s bc model other [] (T.empty_environment (S.signature s)) c;
  if T.truth s bc model other (G.branch false c)
  then lemma_branch s bc model other c conclusion facts false
  else lemma_branch s bc model other c conclusion facts true
