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
module ID = Z3IntegerDivision

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

let lemma_unit_boolean_constants ()
  : Lemma (
      checked_consequence "unit-resolution" p [App or_decl [false_expr; p]; true_expr] /\
      checked_consequence "unit-resolution" p [App or_decl [true_expr; p]; false_expr] /\
      checked_consequence "unit-resolution" false_expr [true_expr; false_expr] /\
      checked_consequence "unit-resolution" false_expr [false_expr; true_expr] /\
      not (checked_consequence "unit-resolution" q [App or_decl [false_expr; p]; true_expr]) /\
      not (checked_consequence "unit-resolution" false_expr [App or_decl [false_expr; p]; true_expr]) /\
      not (checked_consequence "unit-resolution" p [App or_decl [true_expr; p]; true_expr]))
  = assert_norm (
      checked_consequence "unit-resolution" p [App or_decl [false_expr; p]; true_expr] /\
      checked_consequence "unit-resolution" p [App or_decl [true_expr; p]; false_expr] /\
      checked_consequence "unit-resolution" false_expr [true_expr; false_expr] /\
      checked_consequence "unit-resolution" false_expr [false_expr; true_expr] /\
      not (checked_consequence "unit-resolution" q [App or_decl [false_expr; p]; true_expr]) /\
      not (checked_consequence "unit-resolution" false_expr [App or_decl [false_expr; p]; true_expr]) /\
      not (checked_consequence "unit-resolution" p [App or_decl [true_expr; p]; true_expr]))

let lemma_true_axiom_checked ()
  : Lemma (
      P.rule_of_name "true-axiom" == Some DefAxiom /\
      checked_consequence "true-axiom" true_expr [] /\
      not (checked_consequence "true-axiom" false_expr []) /\
      not (checked_consequence "true-axiom" p []) /\
      not (checked_consequence "true-axiom" true_expr [p]))
  = assert_norm (
      P.rule_of_name "true-axiom" == Some DefAxiom /\
      checked_consequence "true-axiom" true_expr [] /\
      not (checked_consequence "true-axiom" false_expr []) /\
      not (checked_consequence "true-axiom" p []) /\
      not (checked_consequence "true-axiom" true_expr [p]))

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

let typed_atom (name:string) (s:sort) : expr =
  App { decl_name = name; domain = []; range = s;
        interp = None; int_params = [] } []

let lemma_typed_observations_preserve_the_relation ()
  : Lemma (
      let x = typed_atom "x" (BaseSort "Int") in
      let y = typed_atom "y" (BaseSort "Int") in
      let z = typed_atom "z" (BaseSort "Int") in
      checked_consequence "refl" (mk_oeq_expr x x) [] /\
      checked_consequence "symm" (mk_oeq_expr y x) [mk_oeq_expr x y] /\
      checked_consequence "trans" (mk_oeq_expr x z) [mk_eq_expr x y; mk_oeq_expr y z] /\
      not (checked_consequence "trans" (mk_eq_expr x z) [mk_oeq_expr x y; mk_oeq_expr y z]) /\
      not (checked_consequence "iff~" (mk_oeq_expr x y) [mk_eq_expr x y]) /\
      not (checked_consequence "refl" (mk_oeq_expr x p) []))
  = assert_norm (
      let x = typed_atom "x" (BaseSort "Int") in
      let y = typed_atom "y" (BaseSort "Int") in
      let z = typed_atom "z" (BaseSort "Int") in
      checked_consequence "refl" (mk_oeq_expr x x) [] /\
      checked_consequence "symm" (mk_oeq_expr y x) [mk_oeq_expr x y] /\
      checked_consequence "trans" (mk_oeq_expr x z) [mk_eq_expr x y; mk_oeq_expr y z] /\
      not (checked_consequence "trans" (mk_eq_expr x z) [mk_oeq_expr x y; mk_oeq_expr y z]) /\
      not (checked_consequence "iff~" (mk_oeq_expr x y) [mk_eq_expr x y]) /\
      not (checked_consequence "refl" (mk_oeq_expr x p) []))

let lemma_typed_observation_congruence ()
  : Lemma (
      let s = ArraySort [BaseSort "Int"] (BaseSort "Real") in
      let x = typed_atom "a" s in
      let y = typed_atom "b" s in
      let f = { decl_name = "observe"; domain = [s]; range = bool_sort;
                interp = None; int_params = [] } in
      checked_consequence "monotonicity" (mk_oeq_expr (App f [x]) (App f [y]))
        [mk_oeq_expr x y] /\
      checked_consequence "monotonicity" (mk_eq_expr (App f [x]) (App f [x]))
        [mk_oeq_expr x x] /\
      not (checked_consequence "monotonicity" (mk_eq_expr (App f [x]) (App f [y]))
        [mk_oeq_expr x y]) /\
      not (checked_consequence "rewrite" (mk_oeq_expr x y) []))
  = assert_norm (
      let s = ArraySort [BaseSort "Int"] (BaseSort "Real") in
      let x = typed_atom "a" s in
      let y = typed_atom "b" s in
      let f = { decl_name = "observe"; domain = [s]; range = bool_sort;
                interp = None; int_params = [] } in
      checked_consequence "monotonicity" (mk_oeq_expr (App f [x]) (App f [y]))
        [mk_oeq_expr x y] /\
      checked_consequence "monotonicity" (mk_eq_expr (App f [x]) (App f [x]))
        [mk_oeq_expr x x] /\
      not (checked_consequence "monotonicity" (mk_eq_expr (App f [x]) (App f [y]))
        [mk_oeq_expr x y]) /\
      not (checked_consequence "rewrite" (mk_oeq_expr x y) []))

let arithmetic_app (name:string) (tag:decl_kind) (s:sort) (args:list expr) : expr =
  App { decl_name = name; domain = FStar.List.Tot.map get_sort args; range = s;
        interp = Some tag; int_params = [] } args

let division_axiom_checks () : bool =
  let s = BaseSort "Int" in
  let x = typed_atom "x" s in
  let b = typed_atom "b" s in
  let n = Z3LpGomory.integer in
  let div a b = arithmetic_app "div" ID.op_idiv s [a; b] in
  let rem a b = arithmetic_app "mod" ID.op_mod s [a; b] in
  let add a b = arithmetic_app "+" op_plus s [a; b] in
  let mul a b = arithmetic_app "*" op_mul s [a; b] in
  let ge a b = arithmetic_app ">=" op_arith_ge bool_sort [a; b] in
  let le a b = arithmetic_app "<=" op_arith_le bool_sort [a; b] in
  let clause guard body = App or_decl [guard; body] in
  let decomposition a b = mk_eq_expr a (add (mul b (div a b)) (rem a b)) in
  ID.check (clause (mk_eq_expr b (n 0)) (decomposition x b)) &&
  ID.check (clause false_expr (decomposition x (n 2))) &&
  ID.check (clause false_expr (decomposition x (n (-2)))) &&
  ID.check (clause false_expr (ge (rem x (n 2)) (n 0))) &&
  ID.check (clause false_expr (le (rem x (n 2)) (n 1))) &&
  ID.check (clause (le b (n 0)) (le (add (rem x b) (mul (n (-1)) b)) (n (-1)))) &&
  ID.check (clause (mk_eq_expr b (n 0))
    (ge (add x (arithmetic_app "*" op_arith_mul s [n (-1); b; div x b])) (n 0))) &&
  ID.check (clause (mk_eq_expr b (n 0))
    (ge (add x (mul (n (-1)) (mul b (div x b)))) (n 0))) &&
  not (ID.check (clause false_expr
    (ge (add x (mul (n (-1)) (mul b (div x b)))) (n 0)))) &&
  not (ID.check (clause (mk_eq_expr b (n 0))
    (ge (add x (mul (n (-1)) (mul b (div x b)))) (n 1)))) &&
  not (ID.check (clause false_expr (decomposition x (n 0)))) &&
  not (ID.check (clause false_expr (decomposition x b))) &&
  not (ID.check (clause false_expr (le (rem x (n 2)) (n 0)))) &&
  not (ID.check (clause false_expr (ge (rem x (n 2)) (n 1)))) &&
  not (ID.check (clause (mk_eq_expr x (n 0)) (decomposition x b))) &&
  ID.equivalent (div (mul (n 10) x) (n 4)) (div (mul x (n 5)) (n 2)) &&
  ID.equivalent (div (mul (n 10) x) (n 4))
    (App (Z3ArrayRewrite.term_ite_decl s)
      [mk_eq_expr (n 0) (n 4); div (mul (n 10) x) (n 0); div (mul x (n 5)) (n 2)]) &&
  not (ID.equivalent (div (mul (n 10) x) (n 4)) (div (mul x (n 4)) (n 2))) &&
  not (ID.equivalent (div (mul (n 10) x) (n 0)) (div (mul x (n 5)) (n 2)))

let lemma_division_axiom_checks () : Lemma (division_axiom_checks ()) =
  assert_norm (division_axiom_checks ())

let lemma_arithmetic_comparison_rewrites ()
  : Lemma (
      let x = typed_atom "x" (BaseSort "Int") in
      let y = typed_atom "y" (BaseSort "Int") in
      let le = arithmetic_app "<=" op_arith_le bool_sort in
      let ge = arithmetic_app ">=" op_arith_ge bool_sort in
      let lt = arithmetic_app "<" op_arith_lt bool_sort in
      checked_consequence "rewrite" (mk_eq_expr (le [x; x]) true_expr) [] /\
      checked_consequence "rewrite" (mk_eq_expr (le [x; y]) (ge [y; x])) [] /\
      checked_consequence "rewrite" (mk_eq_expr (lt [x; y]) (mk_not_expr (le [y; x]))) [] /\
      not (checked_consequence "rewrite" (mk_eq_expr (lt [x; y]) (le [x; y])) []))
  = assert_norm (
      let x = typed_atom "x" (BaseSort "Int") in
      let y = typed_atom "y" (BaseSort "Int") in
      let le = arithmetic_app "<=" op_arith_le bool_sort in
      let ge = arithmetic_app ">=" op_arith_ge bool_sort in
      let lt = arithmetic_app "<" op_arith_lt bool_sort in
      checked_consequence "rewrite" (mk_eq_expr (le [x; x]) true_expr) [] /\
      checked_consequence "rewrite" (mk_eq_expr (le [x; y]) (ge [y; x])) [] /\
      checked_consequence "rewrite" (mk_eq_expr (lt [x; y]) (mk_not_expr (le [y; x]))) [] /\
      not (checked_consequence "rewrite" (mk_eq_expr (lt [x; y]) (le [x; y])) []))

let lemma_numeric_normalization_checks_both_sorts ()
  : Lemma (
      let x = typed_atom "x" (BaseSort "Int") in
      let y = typed_atom "y" (BaseSort "Int") in
      let add = arithmetic_app "+" op_arith_add (BaseSort "Int") in
      let rx = typed_atom "rx" (BaseSort "Real") in
      let ry = typed_atom "ry" (BaseSort "Real") in
      let radd = arithmetic_app "+" op_arith_add (BaseSort "Real") in
      checked_consequence "rewrite" (mk_eq_expr (add [x; y]) (add [y; x])) [] /\
      not (checked_consequence "rewrite" (mk_eq_expr (add [x; y]) (add [x; x])) []) /\
      checked_consequence "rewrite" (mk_eq_expr (radd [rx; ry]) (radd [ry; rx])) [] /\
      not (checked_consequence "rewrite" (mk_eq_expr (radd [rx; ry]) (radd [rx; rx])) []))
  = assert_norm (
      let x = typed_atom "x" (BaseSort "Int") in
      let y = typed_atom "y" (BaseSort "Int") in
      let add = arithmetic_app "+" op_arith_add (BaseSort "Int") in
      let rx = typed_atom "rx" (BaseSort "Real") in
      let ry = typed_atom "ry" (BaseSort "Real") in
      let radd = arithmetic_app "+" op_arith_add (BaseSort "Real") in
      checked_consequence "rewrite" (mk_eq_expr (add [x; y]) (add [y; x])) [] /\
      not (checked_consequence "rewrite" (mk_eq_expr (add [x; y]) (add [x; x])) []) /\
      checked_consequence "rewrite" (mk_eq_expr (radd [rx; ry]) (radd [ry; rx])) [] /\
      not (checked_consequence "rewrite" (mk_eq_expr (radd [rx; ry]) (radd [rx; rx])) []))

let numeric_equality_checks () : bool =
  let x = typed_atom "x" (BaseSort "Real") in
  let y = typed_atom "y" (BaseSort "Real") in
  let le = arithmetic_app "<=" op_arith_le bool_sort in
  let ge = arithmetic_app ">=" op_arith_ge bool_sort in
  let lt = arithmetic_app "<" op_arith_lt bool_sort in
  let bounds = [le [x; y]; ge [x; y]] in
  let bad_bounds = [lt [x; y]; ge [x; y]] in
  let conjunction xs =
    App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Conjunction xs) xs in
  let triangle xs =
    let clause = mk_eq_expr x y :: FStar.List.Tot.map mk_not_expr xs in
    Holds (App (Z3BooleanRewrite.connective_decl Z3BooleanRewrite.Disjunction clause) clause) in
  checked_consequence "rewrite" (mk_eq_expr (mk_eq_expr x y) (conjunction bounds)) [] &&
  not (checked_consequence "rewrite" (mk_eq_expr (mk_eq_expr x y) (conjunction bad_bounds)) []) &&
  checked_theory_lemma (Unverified "th-lemma") (triangle bounds) [] &&
  not (checked_theory_lemma (Unverified "th-lemma") (triangle bad_bounds) []) &&
  not (checked_theory_lemma (Unverified "assumed:nlsat") (triangle bounds) [])

let lemma_numeric_equality_checks () : Lemma (numeric_equality_checks ()) =
  assert_norm (numeric_equality_checks ())

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
