module Z3SortedRelational

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module D = Z3ExprScope
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Reach = Z3RelationalReachability
module Cong = Z3CongruenceSyntax
module Rule = Z3RelationalRuleSyntax
module L = FStar.List.Tot
module Node = Z3UnifiedNode
module SK = Z3SkolemSyntax
module H = Z3HypothesisSemantics
module CS = Z3ClausalSemantics

let related (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
            (scope:list sort) (rho:V.environment base (S.signature s) scope)
            (a b:expr) : prop =
  a == b \/
  (D.scoped scope a /\ D.scoped scope b /\
   T.evaluate_at s bc eq other scope rho a == T.evaluate_at s bc eq other scope rho b)

let judgment_holds (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                   (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (j:U.judgment) : prop =
  match j with
  | U.Holds e -> T.truth_at s bc eq other scope rho e
  | U.Equal a b ->
    if D.scoped scope a && D.scoped scope b then
      T.evaluate_at s bc eq other scope rho a == T.evaluate_at s bc eq other scope rho b
    else False
  | U.Observational a b ->
    if D.scoped scope a && D.scoped scope b then
      T.observations_agree_at s bc eq other scope rho a b
    else False

let judgments_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (js:list U.judgment) : Tot prop =
  H.judgments_hold (judgment_holds s bc eq other scope rho) js

let fact_holds (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
               (scope:list sort) (rho:V.environment base (S.signature s) scope)
               (p:U.checked_fact) : prop =
  H.fact_holds (T.truth_at s bc eq other scope rho)
               (judgment_holds s bc eq other scope rho) p

let facts_hold (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope)
                (ps:list U.checked_fact) : Tot prop =
  H.facts_hold (T.truth_at s bc eq other scope rho)
               (judgment_holds s bc eq other scope rho) ps

let lemma_edge (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
               (scope:list sort) (rho:V.environment base (S.signature s) scope)
               (r:U.relation) (j:U.judgment) (a b:expr)
  : Lemma (requires judgment_holds s bc eq other scope rho j /\ U.edge r j == Some (a, b))
          (ensures related s bc eq other scope rho a b) =
  match r, j with
  | U.Observation, U.Observational x y ->
    T.lemma_observations_values_at s bc eq other scope rho x y
  | _, _ -> ()

let rec lemma_edges (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (r:U.relation) (js:list U.judgment)
  : Lemma (requires judgments_hold s bc eq other scope rho js)
          (ensures Reach.edges_hold (related s bc eq other scope rho) r js)
          (decreases js) =
  match js with
  | [] -> ()
  | j :: rest ->
    (match U.edge r j with
     | Some (a, b) -> lemma_edge s bc eq other scope rho r j a b
     | None -> ());
    lemma_edges s bc eq other scope rho r rest

let rec lemma_arguments (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (xs ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args scope xs /\ D.scoped_args scope ys /\
                    sorts_match xs ss /\ sorts_match ys ss /\
                    Reach.arguments_related (related s bc eq other scope rho) xs ys)
          (ensures T.evaluate_arguments_at s bc eq other scope rho xs ss ==
                   T.evaluate_arguments_at s bc eq other scope rho ys ss)
          (decreases xs) =
  match xs, ys, ss with
  | [], [], [] -> ()
  | x :: rest, y :: tail, t :: remaining ->
    V.lemma_sort_eq (get_sort x) t;
    V.lemma_sort_eq (get_sort y) t;
    lemma_arguments s bc eq other scope rho rest tail remaining
  | _, _, _ -> ()

let lemma_congruence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
                     (r:U.relation) (f:func_decl) (xs ys:list expr) (js:list U.judgment)
  : Lemma (requires D.scoped scope (App f xs) /\ D.scoped scope (App f ys) /\
                    judgments_hold s bc eq other scope rho js /\
                    U.fast_arguments_match r xs ys js)
          (ensures T.evaluate_at s bc eq other scope rho (App f xs) ==
                   T.evaluate_at s bc eq other scope rho (App f ys)) =
  U.lemma_fast_arguments_match r xs ys js;
  lemma_edges s bc eq other scope rho r js;
  Reach.lemma_arguments (related s bc eq other scope rho) r xs ys js;
  lemma_arguments s bc eq other scope rho xs ys f.domain

let lemma_checked_congruence (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                             (scope:list sort) (rho:V.environment base (S.signature s) scope)
                             (r:U.relation) (a b:expr) (js:list U.judgment)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\
                    judgments_hold s bc eq other scope rho js /\ Cong.step r a b js)
          (ensures T.evaluate_at s bc eq other scope rho a ==
                   T.evaluate_at s bc eq other scope rho b) =
  if a <> b then
    match a, b with
    | App f xs, App _ ys -> lemma_congruence s bc eq other scope rho r f xs ys js
    | _, _ -> ()

let lemma_relation_laws (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : Lemma (Reach.symmetric (related s bc eq other scope rho) /\
           Reach.transitive (related s bc eq other scope rho)) =
  let sym (a b:expr)
    : Lemma (requires related s bc eq other scope rho a b)
            (ensures related s bc eq other scope rho b a) = () in
  let trans (a b c:expr)
    : Lemma (requires related s bc eq other scope rho a b /\ related s bc eq other scope rho b c)
            (ensures related s bc eq other scope rho a c) = () in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 sym);
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 trans)

let lemma_relational_judgment (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (r:U.relation) (j:U.judgment) (a b:expr)
  : Lemma (requires judgment_holds s bc eq other scope rho j /\ U.relational j == Some (r, a, b))
          (ensures related s bc eq other scope rho a b) =
  match j with
  | U.Observational x y -> T.lemma_observations_values_at s bc eq other scope rho x y
  | _ -> ()

let lemma_checked_step (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (kind:U.rule) (r:U.relation) (a b:expr) (js:list U.judgment)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\
                    judgments_hold s bc eq other scope rho js /\ Rule.step kind r a b js)
          (ensures T.evaluate_at s bc eq other scope rho a ==
                   T.evaluate_at s bc eq other scope rho b) =
  lemma_relation_laws s bc eq other scope rho;
  (match kind with
   | U.Reflexivity -> ()
   | U.Symmetry ->
     (match js with
      | [j] -> lemma_relational_judgment s bc eq other scope rho r j b a
      | _ -> ())
   | U.Transitivity ->
     (match js with
      | [p; q] ->
        (match U.edge r p, U.edge r q with
         | Some (x, y), Some (z, w) ->
           lemma_edge s bc eq other scope rho r p x y;
           lemma_edge s bc eq other scope rho r q z w
         | _, _ -> ())
      | _ -> ())
   | U.TransitivityPath ->
     lemma_edges s bc eq other scope rho r js;
     Reach.lemma_reachable (related s bc eq other scope rho) r a js [a] (L.length js);
     FStar.List.Tot.Properties.mem_memP b (U.reachable (L.length js) r js [a])
   | U.Congruence -> lemma_checked_congruence s bc eq other scope rho r a b js
   | U.IffObservational -> ()
   | _ -> ())

let lemma_checked_judgment (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (kind:U.rule) (concl:U.judgment) (js:list U.judgment)
  : Lemma (requires U.well_formed concl /\ judgments_hold s bc eq other scope rho js /\
                    (match U.relational concl with
                     | Some (r, a, b) ->
                       D.scoped scope a /\ D.scoped scope b /\ Rule.step kind r a b js
                     | None -> False))
          (ensures judgment_holds s bc eq other scope rho concl) =
  match concl with
  | U.Equal a b -> lemma_checked_step s bc eq other scope rho kind U.Equality a b js
  | U.Observational a b ->
    lemma_checked_step s bc eq other scope rho kind U.Observation a b js;
    T.lemma_values_observations_at s bc eq other scope rho a b
  | U.Holds _ -> ()

let lemma_checked_node (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (check_step:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                       (check_theory:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                       (check_binder:list SK.definition -> list U.judgment -> U.binder_certificate ->
                                     U.judgment -> Tot bool)
                       (skolems:list SK.definition) (strict:bool)
                       (assertions:list U.judgment) (contains:U.judgment -> bool) (node:U.proof_node)
  : Lemma (requires Rule.core_rule node.U.kind /\
                    judgments_hold s bc eq other scope rho (U.premise_judgments node.U.premises) /\
                    (match U.relational node.U.conclusion with
                     | Some (r, a, b) ->
                       D.scoped scope a /\ D.scoped scope b /\
                       (check_step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises) ==>
                        Rule.step node.U.kind r a b (U.premise_judgments node.U.premises))
                     | None -> False) /\
                    Some? (Node.check_node_with_membership check_step check_theory check_binder
                             skolems strict assertions contains node))
          (ensures judgment_holds s bc eq other scope rho node.U.conclusion) =
  (match node.U.kind with
   | U.Reflexivity | U.Symmetry | U.Transitivity | U.TransitivityPath
   | U.Congruence | U.IffObservational -> ()
   | _ -> ());
  lemma_checked_judgment s bc eq other scope rho node.U.kind node.U.conclusion
    (U.premise_judgments node.U.premises)

let lemma_checked_fact_node (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (scope:list sort) (rho:V.environment base (S.signature s) scope)
                            (check_step:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                            (check_theory:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                            (check_binder:list SK.definition -> list U.judgment -> U.binder_certificate ->
                                          U.judgment -> Tot bool)
                            (skolems:list SK.definition) (strict:bool)
                            (assertions:list U.judgment) (contains:U.judgment -> bool)
                            (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires Rule.core_rule node.U.kind /\
                    facts_hold s bc eq other scope rho node.U.premises /\
                    (match U.relational node.U.conclusion with
                     | Some (r, a, b) ->
                       D.scoped scope a /\ D.scoped scope b /\
                       (check_step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises) ==>
                        Rule.step node.U.kind r a b (U.premise_judgments node.U.premises))
                     | None -> False) /\
                    Node.check_node_with_membership check_step check_theory check_binder
                      skolems strict assertions contains node == Some (fact, 0))
          (ensures fact.U.conclusion == node.U.conclusion /\
                   fact.U.hypotheses == U.premise_hypotheses node.U.premises /\
                   fact_holds s bc eq other scope rho fact) =
  (match node.U.kind with
   | U.Reflexivity | U.Symmetry | U.Transitivity | U.TransitivityPath
   | U.Congruence | U.IffObservational -> ()
   | _ -> ());
  if CS.conj_holds (T.truth_at s bc eq other scope rho) fact.U.hypotheses then (
    H.lemma_premises (T.truth_at s bc eq other scope rho)
      (judgment_holds s bc eq other scope rho) node.U.premises;
    lemma_checked_node s bc eq other scope rho check_step check_theory check_binder
      skolems strict assertions contains node)
