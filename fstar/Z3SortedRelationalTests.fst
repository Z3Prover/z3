module Z3SortedRelationalTests

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module D = Z3ExprScope
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Cong = Z3CongruenceSyntax
module Rule = Z3RelationalRuleSyntax
module SC = Z3SortedRelational
module Node = Z3UnifiedNode
module CS = Z3ClausalSemantics

let int_s = SortApp IntSymbol []
let scope = [bool_sort; bool_sort; bool_sort; int_s]
let p = Var 0 bool_sort
let q = Var 1 bool_sort
let z = Var 2 bool_sort
let f : func_decl =
  { decl_name = "f"; domain = [bool_sort; bool_sort]; range = int_s;
    interp = None; int_params = [] }
let left = App f [p; p]
let right = App f [q; p]
let facts = [U.Observational p q]

let observational_congruence (#base:sort -> Type0) (s:S.checked_schema)
                              (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                              (other:V.interpretation base (S.signature s))
                              (rho:V.environment base (S.signature s) scope)
  : Lemma (requires T.observations_agree_at s bc eq other scope rho p q)
          (ensures T.evaluate_at s bc eq other scope rho left ==
                   T.evaluate_at s bc eq other scope rho right) =
  assert_norm (D.scoped scope left /\ D.scoped scope right /\
               Cong.step U.Observation left right facts);
  SC.lemma_checked_congruence s bc eq other scope rho U.Observation left right facts

let exact_recognizer ()
  : Lemma (Cong.step U.Equality p p [] /\
           not (Cong.step U.Equality left right facts) /\
           not (Cong.step U.Observation right left facts) /\
           not (Cong.step U.Observation left right [])) =
  assert_norm (Cong.step U.Equality p p [] /\
               not (Cong.step U.Equality left right facts) /\
               not (Cong.step U.Observation right left facts) /\
               not (Cong.step U.Observation left right []))

let sorted_relational_steps (#base:sort -> Type0) (s:S.checked_schema)
                            (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                            (other:V.interpretation base (S.signature s))
                            (rho:V.environment base (S.signature s) scope)
  : Lemma (requires T.observations_agree_at s bc eq other scope rho p q /\
                    T.observations_agree_at s bc eq other scope rho q z)
          (ensures T.evaluate_at s bc eq other scope rho p ==
                   T.evaluate_at s bc eq other scope rho z /\
                   T.evaluate_at s bc eq other scope rho q ==
                   T.evaluate_at s bc eq other scope rho p) =
  let forward = [U.Observational p q; U.Observational q z] in
  let reverse = [U.Observational q z; U.Observational p q] in
  assert_norm (D.scoped scope p /\ D.scoped scope q /\ D.scoped scope z /\
               Rule.step U.Reflexivity U.Equality p p [] /\
               Rule.step U.Symmetry U.Observation q p [U.Observational p q] /\
               Rule.step U.Transitivity U.Observation p z forward /\
               Rule.step U.TransitivityPath U.Observation p z reverse /\
               not (Rule.step U.Transitivity U.Equality p z forward));
  SC.lemma_checked_step s bc eq other scope rho U.Reflexivity U.Equality p p [];
  SC.lemma_checked_step s bc eq other scope rho U.Symmetry U.Observation q p [U.Observational p q];
  SC.lemma_checked_step s bc eq other scope rho U.Transitivity U.Observation p z forward;
  SC.lemma_checked_step s bc eq other scope rho U.TransitivityPath U.Observation p z reverse

let sorted_iff_observational (#base:sort -> Type0) (s:S.checked_schema)
                             (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                             (other:V.interpretation base (S.signature s))
                             (rho:V.environment base (S.signature s) scope)
  : Lemma (requires T.evaluate_at s bc eq other scope rho p ==
                    T.evaluate_at s bc eq other scope rho q)
          (ensures T.observations_agree_at s bc eq other scope rho p q) =
  assert_norm (D.scoped scope p /\ D.scoped scope q /\
               U.well_formed (U.Observational p q) /\
               Rule.step U.IffObservational U.Observation p q [U.Equal p q]);
  SC.lemma_checked_judgment s bc eq other scope rho U.IffObservational
    (U.Observational p q) [U.Equal p q]

let core_check (kind:U.rule) (concl:U.judgment) (premises:list U.judgment) : bool =
  match U.relational concl with
  | Some (r, a, b) -> Rule.step kind r a b premises
  | None -> false

let rejected_theory _ _ _ = false
let rejected_binder _ _ _ _ = false
let congruence_node : U.proof_node = {
  U.kind = U.Congruence;
  U.conclusion = U.Observational left right;
  U.premises = [{ U.conclusion = U.Observational p q; U.hypotheses = [] }];
}

let sorted_default_dispatch (#base:sort -> Type0) (s:S.checked_schema)
                            (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                            (other:V.interpretation base (S.signature s))
                            (rho:V.environment base (S.signature s) scope)
  : Lemma (requires T.observations_agree_at s bc eq other scope rho p q)
          (ensures SC.judgment_holds s bc eq other scope rho congruence_node.U.conclusion) =
  assert_norm (Some? (Node.check_node_with_membership core_check rejected_theory rejected_binder
                       [] false [] (fun _ -> false) congruence_node) /\
               D.scoped scope left /\ D.scoped scope right);
  SC.lemma_checked_node s bc eq other scope rho core_check rejected_theory rejected_binder
    [] false [] (fun _ -> false) congruence_node

let conditional_node : U.proof_node = {
  U.kind = U.Transitivity;
  U.conclusion = U.Observational p z;
  U.premises = [
    { U.conclusion = U.Observational p q; U.hypotheses = [p; q] };
    { U.conclusion = U.Observational q z; U.hypotheses = [q; z] }
  ];
}

let conditional_fact : U.checked_fact = {
  U.conclusion = U.Observational p z;
  U.hypotheses = [p; z; q];
}

let sorted_conditional_dispatch (#base:sort -> Type0) (s:S.checked_schema)
                                (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                                (other:V.interpretation base (S.signature s))
                                (rho:V.environment base (S.signature s) scope)
  : Lemma (requires SC.facts_hold s bc eq other scope rho conditional_node.U.premises)
          (ensures SC.fact_holds s bc eq other scope rho conditional_fact /\
                   (CS.conj_holds (T.truth_at s bc eq other scope rho) [p; z; q] ==>
                    T.observations_agree_at s bc eq other scope rho p z)) =
  assert_norm (U.premise_hypotheses conditional_node.U.premises == [p; z; q] /\
               Node.check_node_with_membership core_check rejected_theory rejected_binder
                 [] false [] (fun _ -> false) conditional_node == Some (conditional_fact, 0) /\
               D.scoped scope p /\ D.scoped scope z);
  SC.lemma_checked_fact_node s bc eq other scope rho core_check rejected_theory rejected_binder
    [] false [] (fun _ -> false) conditional_node conditional_fact
