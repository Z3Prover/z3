module Z3ResolutionProofCheckerTests

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3UnifiedProof
open Z3Commutativity
open Z3BooleanRewrite
open Z3ProofIndex
module P = Z3ProofDocument

let checked_consequence (kind:string) (concl:expr) (facts:list expr) : bool =
  match P.rule_of_name kind, classify_fact concl, opt_map classify_fact facts with
  | Some r, Some j, Some js -> check_step r j js
  | _, _, _ -> false

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

let lemma_def_axiom_obligations_are_independent_of_input_membership ()
  : Lemma (
      let node = { kind = DefAxiom; conclusion = Holds p; premises = [] } in
      check_node_with_inputs false [] node ==
        Some ({ conclusion = Holds p; hypotheses = [] }, 1) /\
      check_node_with_inputs true [Holds p] node ==
        Some ({ conclusion = Holds p; hypotheses = [] }, 1) /\
      check_node_with_inputs true [] { node with conclusion = Holds true_expr } ==
        Some ({ conclusion = Holds true_expr; hypotheses = [] }, 0) /\
      check_node_with_inputs true [] { node with kind = Asserted } == None)
  = assert_norm (
      let node = { kind = DefAxiom; conclusion = Holds p; premises = [] } in
      check_node_with_inputs false [] node ==
        Some ({ conclusion = Holds p; hypotheses = [] }, 1) /\
      check_node_with_inputs true [Holds p] node ==
        Some ({ conclusion = Holds p; hypotheses = [] }, 1) /\
      check_node_with_inputs true [] { node with conclusion = Holds true_expr } ==
        Some ({ conclusion = Holds true_expr; hypotheses = [] }, 0) /\
      check_node_with_inputs true [] { node with kind = Asserted } == None)

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

let lemma_nary_distinct_def_axioms_are_checked ()
  : Lemma (
      let d = Z3DistinctAst.mk_distinct_expr bool_sort [p; q; r] in
      let expanded = Z3DistinctAst.expanded [p; q; r] in
      let forward = Holds (bool_app Disjunction [mk_not_expr d; expanded]) in
      let backward = Holds (bool_app Disjunction [d; mk_not_expr expanded]) in
      check_node [] { kind = DefAxiom; conclusion = forward; premises = [] } ==
        Some ({ conclusion = forward; hypotheses = [] }, 0) /\
      check_node [] { kind = DefAxiom; conclusion = backward; premises = [] } ==
        Some ({ conclusion = backward; hypotheses = [] }, 0))
  = assert_norm (
      let d = Z3DistinctAst.mk_distinct_expr bool_sort [p; q; r] in
      let expanded = Z3DistinctAst.expanded [p; q; r] in
      let forward = Holds (bool_app Disjunction [mk_not_expr d; expanded]) in
      let backward = Holds (bool_app Disjunction [d; mk_not_expr expanded]) in
      check_node [] { kind = DefAxiom; conclusion = forward; premises = [] } ==
        Some ({ conclusion = forward; hypotheses = [] }, 0) /\
      check_node [] { kind = DefAxiom; conclusion = backward; premises = [] } ==
        Some ({ conclusion = backward; hypotheses = [] }, 0))

let lemma_boolean_ite_rewrites_require_boolean_branches_and_builtin_decl ()
  : Lemma (
      boolean_equiv 8 10 (App boolean_ite_decl [p; q; r])
        (bool_app Disjunction [bool_app Conjunction [p; q]; bool_app Conjunction [np; r]]) /\
      not (boolean_equiv 8 10 (App boolean_ite_decl [p; q; r])
        (App boolean_ite_decl [p; r; q])) /\
      native_bool_op { boolean_ite_decl with interp = None } [p; q; r] ==
        Z3BoundedBoolEquiv.Opaque /\
      native_bool_op boolean_ite_decl [p; q; Var 0 (BaseSort "Int")] ==
        Z3BoundedBoolEquiv.Opaque)
  = assert_norm (
      boolean_equiv 8 10 (App boolean_ite_decl [p; q; r])
        (bool_app Disjunction [bool_app Conjunction [p; q]; bool_app Conjunction [np; r]]) /\
      not (boolean_equiv 8 10 (App boolean_ite_decl [p; q; r])
        (App boolean_ite_decl [p; r; q])) /\
      native_bool_op { boolean_ite_decl with interp = None } [p; q; r] ==
        Z3BoundedBoolEquiv.Opaque /\
      native_bool_op boolean_ite_decl [p; q; Var 0 (BaseSort "Int")] ==
        Z3BoundedBoolEquiv.Opaque)

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

module A = Z3ArrayRewrite

let array_sort = ArraySort [BaseSort "I"] (BaseSort "E")
let array_a = Var 0 array_sort
let array_i = Var 1 (BaseSort "I")
let array_j = Var 2 (BaseSort "I")
let array_v = Var 3 (BaseSort "E")
let array_w = Var 4 (BaseSort "E")
let store_decl : func_decl =
  { decl_name = "store"; domain = [array_sort; BaseSort "I"; BaseSort "E"];
    range = array_sort; interp = Some op_store; int_params = [] }
let select_decl : func_decl =
  { decl_name = "select"; domain = [array_sort; BaseSort "I"];
    range = BaseSort "E"; interp = Some op_select; int_params = [] }
let stored = App store_decl [array_a; array_i; array_v]
let overwritten = App store_decl [stored; array_i; array_w]
let reduced_store = App store_decl [array_a; array_i; array_w]
let read_ite = App (A.term_ite_decl (BaseSort "E"))
  [mk_eq_expr array_i array_j; array_v; App select_decl [array_a; array_j]]

let lemma_contextual_array_rewrites ()
  : Lemma (
      A.equivalent 64 overwritten reduced_store /\
      A.equivalent 64 (App store_decl
        [array_a; array_i; App select_decl [array_a; array_i]]) array_a /\
      A.equivalent 64 (App select_decl [stored; array_j]) read_ite /\
      checked_consequence "rewrite"
        (mk_eq_expr (mk_not_expr (mk_eq_expr overwritten array_a))
                    (mk_not_expr (mk_eq_expr reduced_store array_a))) [])
  = assert_norm (
      A.equivalent 64 overwritten reduced_store /\
      A.equivalent 64 (App store_decl
        [array_a; array_i; App select_decl [array_a; array_i]]) array_a /\
      A.equivalent 64 (App select_decl [stored; array_j]) read_ite /\
      checked_consequence "rewrite"
        (mk_eq_expr (mk_not_expr (mk_eq_expr overwritten array_a))
                    (mk_not_expr (mk_eq_expr reduced_store array_a))) [])

let lemma_contextual_array_rewrites_reject_invalid_instances ()
  : Lemma (
      not (A.equivalent 64 (App select_decl [stored; array_j]) array_v) /\
      not (A.equivalent 64 (App { store_decl with interp = None }
        [stored; array_i; array_w]) reduced_store) /\
      A.ite_parts (App (A.term_ite_decl (BaseSort "E"))
        [p; array_v; array_i]) == None /\
      not (A.equivalent 0 overwritten reduced_store))
  = assert_norm (
      not (A.equivalent 64 (App select_decl [stored; array_j]) array_v) /\
      not (A.equivalent 64 (App { store_decl with interp = None }
        [stored; array_i; array_w]) reduced_store) /\
      A.ite_parts (App (A.term_ite_decl (BaseSort "E"))
        [p; array_v; array_i]) == None /\
      not (A.equivalent 0 overwritten reduced_store))

module Defs = Z3Definitions

let defined_f : func_decl =
  { decl_name = "defined-f"; domain = [bool_sort]; range = bool_sort;
    interp = None; int_params = [] }
let defined_g : func_decl = { defined_f with decl_name = "defined-g" }
let predicate : func_decl =
  { decl_name = "predicate"; domain = [bool_sort; bool_sort]; range = bool_sort;
    interp = None; int_params = [] }
let capture_body =
  Quantifier Forall_k [bool_sort] bool_sort
    (App predicate [Var 1 bool_sort; Var 0 bool_sort])
let capture_definition : Defs.definition =
  { symbol = defined_f; variables = [0]; body = capture_body }
let capture_application =
  Quantifier Forall_k [bool_sort] bool_sort (App defined_f [Var 0 bool_sort])
let capture_expected =
  Quantifier Forall_k [bool_sort] bool_sort capture_body

let lemma_definition_expansion_avoids_variable_capture ()
  : Lemma (Defs.scoped [] capture_application /\
           Defs.expand 1 [capture_definition] capture_application == Some capture_expected)
  = assert_norm (Defs.scoped [] capture_application /\
                 Defs.expand 1 [capture_definition] capture_application == Some capture_expected)

let lemma_definition_freshness_checks_quantified_original_inputs ()
  : Lemma (
      Defs.check_fresh_inputs [capture_definition] [mk_eq_expr p q] /\
      not (Defs.check_fresh_inputs [capture_definition] [capture_application]) /\
      Defs.expand_args 1 [capture_definition] [mk_eq_expr p q] == Some [mk_eq_expr p q])
  = assert_norm (
      Defs.check_fresh_inputs [capture_definition] [mk_eq_expr p q] /\
      not (Defs.check_fresh_inputs [capture_definition] [capture_application]) /\
      Defs.expand_args 1 [capture_definition] [mk_eq_expr p q] == Some [mk_eq_expr p q])

let lemma_recursive_definitions_are_rejected ()
  : Lemma (
      let f : Defs.definition =
        { symbol = defined_f; variables = [0]; body = App defined_g [Var 0 bool_sort] } in
      let g : Defs.definition =
        { symbol = defined_g; variables = [0]; body = App defined_f [Var 0 bool_sort] } in
      not (Defs.acyclic 2 [f; g] [f; g]))
  = assert_norm (
      let f : Defs.definition =
        { symbol = defined_f; variables = [0]; body = App defined_g [Var 0 bool_sort] } in
      let g : Defs.definition =
        { symbol = defined_g; variables = [0]; body = App defined_f [Var 0 bool_sort] } in
      not (Defs.acyclic 2 [f; g] [f; g]))
