module Z3ResolutionProofCheckerTests

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3UnifiedProof
open Z3ResolutionProofJson

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
