module Z3ResolutionProofCheckerTests

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3UnifiedProof
open Z3Commutativity
open Z3BooleanRewrite
open Z3ResolutionProofJson
module Json = Z3ProofJson

let atom (name:string) : expr =
  App { decl_name = name; domain = []; range = bool_sort;
        interp = None; int_params = [] } []

let or_decl : func_decl =
  { decl_name = "or"; domain = [bool_sort; bool_sort];
    range = bool_sort; interp = Some op_or; int_params = [] }

let p = atom "p"
let q = atom "q"
let r = atom "r"
let disj = App or_decl [p; q]
let np = mk_not_expr p

let lemma_shared_legacy_proofs_use_cached_results ()
  : Lemma (
      let leaf = Json.cached_refl p in
      let shared = Json.cached_trans leaf leaf in
      let valid = Json.cached_trans shared shared in
      let bad = Json.cached_trans leaf (Json.cached_refl q) in
      let invalid = Json.cached_trans bad bad in
      valid.result == Some (p, p) /\ invalid.result == None)
  = assert_norm (
      let leaf = Json.cached_refl p in
      let shared = Json.cached_trans leaf leaf in
      let valid = Json.cached_trans shared shared in
      let bad = Json.cached_trans leaf (Json.cached_refl q) in
      let invalid = Json.cached_trans bad bad in
      valid.result == Some (p, p) /\ invalid.result == None)

let lemma_unit_literal_consequence ()
  : Lemma (rfact (RUnitRes q (Trusted "clause" disj)
                  [(np, Trusted "unit" np)]) == Some q)
  = assert_norm (rfact (RUnitRes q (Trusted "clause" disj)
                         [(np, Trusted "unit" np)]) == Some q)

let lemma_unit_nested_or_consequence ()
  : Lemma (let c = App or_decl [q; r] in
           checked_consequence "unit-resolution" c [App or_decl [p; c]; np])
  = assert_norm (let c = App or_decl [q; r] in
                 checked_consequence "unit-resolution" c [App or_decl [p; c]; np])

let lemma_unit_empty_consequence ()
  : Lemma (checked_consequence "unit-resolution" false_expr [p; np])
  = assert_norm (checked_consequence "unit-resolution" false_expr [p; np])

let lemma_unit_cannot_drop_survivor ()
  : Lemma (not (checked_consequence "unit-resolution" r [disj; np]) /\
           not (checked_consequence "unit-resolution" false_expr [disj; np]))
  = assert_norm (not (checked_consequence "unit-resolution" r [disj; np]) /\
                 not (checked_consequence "unit-resolution" false_expr [disj; np]))

let lemma_not_or_elimination_preserves_literal_polarity ()
  : Lemma (checked_consequence "not-or-elim" p [mk_not_expr (App or_decl [np; q])] /\
           checked_consequence "not-or-elim" np [mk_not_expr disj] /\
           not (checked_consequence "not-or-elim" r [mk_not_expr disj]))
  = assert_norm (
      checked_consequence "not-or-elim" p [mk_not_expr (App or_decl [np; q])] /\
      checked_consequence "not-or-elim" np [mk_not_expr disj] /\
      not (checked_consequence "not-or-elim" r [mk_not_expr disj]))

let lemma_mp_checks_both_facts ()
  : Lemma (checked_consequence "mp" q [p; mk_iff_expr p q] /\
           not (checked_consequence "mp" q [r; mk_iff_expr p q]) /\
           not (checked_consequence "mp" r [p; mk_iff_expr p q]))
  = assert_norm (checked_consequence "mp" q [p; mk_iff_expr p q] /\
                 not (checked_consequence "mp" q [r; mk_iff_expr p q]) /\
                 not (checked_consequence "mp" r [p; mk_iff_expr p q]))

let lemma_oeq_rules_keep_relations_separate ()
  : Lemma (checked_consequence "mp~" q [p; mk_oeq_expr p q] /\
           not (checked_consequence "mp~" q [p; mk_iff_expr p q]) /\
           not (checked_consequence "mp" q [p; mk_oeq_expr p q]) /\
           checked_consequence "iff~" (mk_oeq_expr p q) [mk_iff_expr p q] /\
           not (checked_consequence "iff~" (mk_iff_expr p q) [mk_oeq_expr p q]) /\
           not (checked_consequence "iff~" (mk_oeq_expr p q) [mk_oeq_expr p q]))
  = assert_norm (
      checked_consequence "mp~" q [p; mk_oeq_expr p q] /\
      not (checked_consequence "mp~" q [p; mk_iff_expr p q]) /\
      not (checked_consequence "mp" q [p; mk_oeq_expr p q]) /\
      checked_consequence "iff~" (mk_oeq_expr p q) [mk_iff_expr p q] /\
      not (checked_consequence "iff~" (mk_iff_expr p q) [mk_oeq_expr p q]) /\
      not (checked_consequence "iff~" (mk_oeq_expr p q) [mk_oeq_expr p q]))

let lemma_oeq_composition_does_not_prove_equality ()
  : Lemma (
      checked_consequence "trans" (mk_oeq_expr p r) [mk_oeq_expr p q; mk_oeq_expr q r] /\
      checked_consequence "trans" (mk_oeq_expr p r) [mk_iff_expr p q; mk_oeq_expr q r] /\
      not (checked_consequence "trans" (mk_iff_expr p r) [mk_oeq_expr p q; mk_oeq_expr q r]))
  = assert_norm (
      checked_consequence "trans" (mk_oeq_expr p r) [mk_oeq_expr p q; mk_oeq_expr q r] /\
      checked_consequence "trans" (mk_oeq_expr p r) [mk_iff_expr p q; mk_oeq_expr q r] /\
      not (checked_consequence "trans" (mk_iff_expr p r) [mk_oeq_expr p q; mk_oeq_expr q r]))

let lemma_refl_checks_endpoints ()
  : Lemma (checked_consequence "refl" (mk_iff_expr p p) [] /\
           not (checked_consequence "refl" (mk_iff_expr p q) []))
  = assert_norm (checked_consequence "refl" (mk_iff_expr p p) [] /\
                 not (checked_consequence "refl" (mk_iff_expr p q) []))

let lemma_unified_classification_keeps_judgments_distinct ()
  : Lemma (classify_fact p == Some (Holds p) /\
           classify_fact (mk_eq_expr p q) == Some (Equal p q) /\
           classify_fact (mk_oeq_expr p q) == Some (Observational p q))
  = assert_norm (classify_fact p == Some (Holds p) /\
                 classify_fact (mk_eq_expr p q) == Some (Equal p q) /\
                 classify_fact (mk_oeq_expr p q) == Some (Observational p q))

let lemma_unified_resolution_produces_an_equality_judgment ()
  : Lemma (
      let c : checked_fact =
        { conclusion = Holds (App or_decl [r; mk_eq_expr p q]); hypotheses = [] } in
      let n : checked_fact = { conclusion = Holds (mk_not_expr r); hypotheses = [] } in
      check_node [] { kind = UnitResolution; conclusion = Equal p q; premises = [c; n] } ==
        Some ({ conclusion = Equal p q; hypotheses = [] }, 0))
  = assert_norm (
      let c : checked_fact =
        { conclusion = Holds (App or_decl [r; mk_eq_expr p q]); hypotheses = [] } in
      let n : checked_fact = { conclusion = Holds (mk_not_expr r); hypotheses = [] } in
      check_node [] { kind = UnitResolution; conclusion = Equal p q; premises = [c; n] } ==
        Some ({ conclusion = Equal p q; hypotheses = [] }, 0))

let lemma_unified_discharge_keeps_the_equality_tag ()
  : Lemma (
      let contradiction : checked_fact =
        { conclusion = Holds false_expr; hypotheses = [mk_not_expr (mk_eq_expr p q)] } in
      check_node [] { kind = LemmaRule; conclusion = Equal p q; premises = [contradiction] } ==
        Some ({ conclusion = Equal p q; hypotheses = [] }, 0))
  = assert_norm (
      let contradiction : checked_fact =
        { conclusion = Holds false_expr; hypotheses = [mk_not_expr (mk_eq_expr p q)] } in
      check_node [] { kind = LemmaRule; conclusion = Equal p q; premises = [contradiction] } ==
        Some ({ conclusion = Equal p q; hypotheses = [] }, 0))

let lemma_commutativity_is_a_checked_binary_rule ()
  : Lemma (
      checked_consequence "commutativity" (mk_eq_expr (App or_decl [p; q]) (App or_decl [q; p])) [] /\
      checked_consequence "commutativity" (mk_eq_expr (mk_eq_expr p q) (mk_eq_expr q p)) [] /\
      not (checked_consequence "commutativity" (mk_eq_expr (App or_decl [p; q]) (App or_decl [p; p])) []))
  = assert_norm (
      checked_consequence "commutativity" (mk_eq_expr (App or_decl [p; q]) (App or_decl [q; p])) [] /\
      checked_consequence "commutativity" (mk_eq_expr (mk_eq_expr p q) (mk_eq_expr q p)) [] /\
      not (checked_consequence "commutativity" (mk_eq_expr (App or_decl [p; q]) (App or_decl [p; p])) []))

let lemma_def_axiom_trust_is_separate_from_strict_inputs ()
  : Lemma (
      let node = { kind = DefAxiom; conclusion = Holds p; premises = [] } in
      Some? (check_node_with_inputs false [] node) /\
      check_node_with_inputs true [] node == None /\
      Some? (check_node_with_inputs true [Holds p] node))
  = assert_norm (
      let node = { kind = DefAxiom; conclusion = Holds p; premises = [] } in
      Some? (check_node_with_inputs false [] node) /\
      check_node_with_inputs true [] node == None /\
      Some? (check_node_with_inputs true [Holds p] node))

let lemma_identity_rewrite_discharges_only_identical_endpoints ()
  : Lemma (
      check_node [] { kind = RewriteRule; conclusion = Equal p p; premises = [] } ==
        Some ({ conclusion = Equal p p; hypotheses = [] }, 0) /\
      check_node [] { kind = RewriteRule; conclusion = Equal p q; premises = [] } ==
        Some ({ conclusion = Equal p q; hypotheses = [] }, 1) /\
      checked_consequence "rewrite" (mk_oeq_expr p p) [] /\
      not (checked_consequence "rewrite" (mk_oeq_expr p q) []))
  = assert_norm (
      check_node [] { kind = RewriteRule; conclusion = Equal p p; premises = [] } ==
        Some ({ conclusion = Equal p p; hypotheses = [] }, 0) /\
      check_node [] { kind = RewriteRule; conclusion = Equal p q; premises = [] } ==
        Some ({ conclusion = Equal p q; hypotheses = [] }, 1) /\
      checked_consequence "rewrite" (mk_oeq_expr p p) [] /\
      not (checked_consequence "rewrite" (mk_oeq_expr p q) []))

let lemma_nary_boolean_flattening_preserves_operands ()
  : Lemma (
      let nested = App or_decl [App or_decl [p; q]; r] in
      let flat = App (connective_decl Disjunction [p; q; r]) [p; q; r] in
      let reordered = App (connective_decl Disjunction [r; q; p]) [r; q; p] in
      flatten_rewrite nested == Some flat /\
      flatten_rewrite nested <> Some reordered /\
      checked_consequence "rewrite" (mk_eq_expr nested flat) [] /\
      checked_consequence "rewrite" (mk_eq_expr nested reordered) [])
  = assert_norm (
      let nested = App or_decl [App or_decl [p; q]; r] in
      let flat = App (connective_decl Disjunction [p; q; r]) [p; q; r] in
      let reordered = App (connective_decl Disjunction [r; q; p]) [r; q; p] in
      flatten_rewrite nested == Some flat /\
      flatten_rewrite nested <> Some reordered /\
      checked_consequence "rewrite" (mk_eq_expr nested flat) [] /\
      checked_consequence "rewrite" (mk_eq_expr nested reordered) [])

let bool_app (op:connective) (args:list expr) : expr =
  App (connective_decl op args) args

let lemma_contextual_boolean_reductions ()
  : Lemma (
      boolean_equiv 8 10
        (bool_app Conjunction [bool_app Disjunction [p; p]; q; true_expr])
        (bool_app Conjunction [q; p]) /\
      boolean_equiv 8 10 (bool_app Conjunction [p; bool_app Disjunction [p; q]]) p /\
      boolean_equiv 8 10
        (bool_app Disjunction [bool_app Conjunction [p; np; r]; q]) q /\
      boolean_equiv 8 10 (mk_not_expr (bool_app Conjunction [p; q; r]))
        (bool_app Disjunction [np; mk_not_expr q; mk_not_expr r]))
  = assert_norm (
      boolean_equiv 8 10
        (bool_app Conjunction [bool_app Disjunction [p; p]; q; true_expr])
        (bool_app Conjunction [q; p]) /\
      boolean_equiv 8 10 (bool_app Conjunction [p; bool_app Disjunction [p; q]]) p /\
      boolean_equiv 8 10
        (bool_app Disjunction [bool_app Conjunction [p; np; r]; q]) q /\
      boolean_equiv 8 10 (mk_not_expr (bool_app Conjunction [p; q; r]))
        (bool_app Disjunction [np; mk_not_expr q; mk_not_expr r]))

let lemma_boolean_truth_table_checks_distribution_not_atom_identities ()
  : Lemma (
      boolean_equiv 8 10 (bool_app Conjunction [p; bool_app Disjunction [q; r]])
        (bool_app Disjunction [bool_app Conjunction [p; q]; bool_app Conjunction [p; r]]) /\
      boolean_equiv 8 10 (mk_eq_expr p p) true_expr /\
      not (boolean_equiv 8 10 p q) /\
      not (boolean_equiv 8 10 (bool_app Conjunction [p; q]) (bool_app Disjunction [p; q])))
  = assert_norm (
      boolean_equiv 8 10 (bool_app Conjunction [p; bool_app Disjunction [q; r]])
        (bool_app Disjunction [bool_app Conjunction [p; q]; bool_app Conjunction [p; r]]) /\
      boolean_equiv 8 10 (mk_eq_expr p p) true_expr /\
      not (boolean_equiv 8 10 p q) /\
      not (boolean_equiv 8 10 (bool_app Conjunction [p; q]) (bool_app Disjunction [p; q])))
