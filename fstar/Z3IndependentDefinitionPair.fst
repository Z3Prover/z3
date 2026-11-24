module Z3IndependentDefinitionPair

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module Recognition = Z3DefinitionRecognition
module Scope = Z3ExprScope
module A = Z3ArraySyntax
module SA = Z3SortedArray
module Dependent = Z3SortedDependentSkolem
module R = Z3ClauseSyntax
module L = FStar.List.Tot
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module B = Z3BoundedBoolEquiv

let disjunction (a b:expr) : expr =
  let args = [a; b] in App (R.or_decl args) args

let pair (t:sort) (d:D.definition) : expr =
  let name = App d.D.symbol [Var 0 t] in
  let positive = Quantifier Forall_k [t] bool_sort (disjunction (R.mk_not_expr name) d.D.body) in
  let negative = Quantifier Forall_k [t] bool_sort (disjunction name (R.mk_not_expr d.D.body)) in
  let args = [positive; negative] in
  App (R.and_decl args) args

let scalar_pair (condition name then_value else_value:expr) : expr =
  let positive = disjunction (R.mk_not_expr condition) (R.mk_eq_expr name then_value) in
  let negative = disjunction condition (R.mk_eq_expr name else_value) in
  App (R.and_decl [positive; negative]) [positive; negative]

let scalar_valid (s:S.checked_schema) (inputs:list expr) (formula:expr) (d:D.definition) : bool =
  d.D.symbol.domain = [] && d.D.variables = [] &&
  Dependent.function_safe s d.D.symbol &&
  get_sort d.D.body = d.D.symbol.range &&
  D.fresh [d] d.D.body && D.fresh_args [d] inputs &&
  Scope.scoped [] (App d.D.symbol []) &&
  Scope.scoped [] d.D.body && Scope.scoped [] formula &&
  (match A.ite_parts d.D.body with
   | Some (condition, then_value, else_value) ->
     formula = scalar_pair condition (App d.D.symbol []) then_value else_value
   | None ->
     formula = R.mk_eq_expr (App d.D.symbol []) d.D.body ||
     formula = R.mk_eq_expr d.D.body (App d.D.symbol []))

let valid (s:S.checked_schema) (inputs:list expr) (formula:expr) (d:D.definition) : bool =
  match d.D.symbol.domain with
  | [t] ->
    Dependent.function_safe s d.D.symbol &&
    d.D.symbol.range = bool_sort &&
    D.make_definition [t] (App d.D.symbol [Var 0 t]) d.D.body = Some d &&
    D.fresh [d] d.D.body && D.fresh_args [d] inputs &&
    Scope.scoped [] formula && formula = pair t d
  | [] -> scalar_valid s inputs formula d
  | _ -> false

let recognize (s:S.checked_schema) (inputs:list expr) (formula:expr)
  : result:option D.definition{
      match result with
      | Some d -> valid s inputs formula d
      | None -> True} =
  if not (Some? (expression_budget 16384 formula) &&
          L.for_all (fun e -> Some? (expression_budget 16384 e)) inputs)
  then None
  else match Recognition.definition_of formula with
  | Some d -> if valid s inputs formula d then Some d else None
  | None -> None

let lemma_disjunction (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (a b:expr)
  : Lemma (requires Scope.scoped scope a /\ Scope.scoped scope b /\
                    get_sort a == bool_sort /\ get_sort b == bool_sort)
          (ensures T.truth_at s bc eq other scope rho (disjunction a b) ==
                   (T.truth_at s bc eq other scope rho a || T.truth_at s bc eq other scope rho b)) =
  T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 (disjunction a b);
  assert_norm (T.cut 1 (disjunction a b) == B.Nary B.Or [B.Atom a; B.Atom b])

let lemma_negation (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (a:expr)
  : Lemma (requires Scope.scoped scope a /\ get_sort a == bool_sort)
          (ensures T.truth_at s bc eq other scope rho (R.mk_not_expr a) ==
                   not (T.truth_at s bc eq other scope rho a)) =
  T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 (R.mk_not_expr a);
  assert_norm (T.cut 1 (R.mk_not_expr a) == B.Not (B.Atom a))

let lemma_pair_truth (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:D.definition) (t:sort)
  : Lemma (requires valid s inputs formula d /\ d.D.symbol.domain == [t] /\
      Q.forall_model s bc other /\
      (forall (rho:V.environment base (S.signature s) [t]).
        T.truth_at s bc eq other [t] rho (App d.D.symbol [Var 0 t]) <==>
        T.truth_at s bc eq other [t] rho d.D.body))
    (ensures T.truth s bc eq other formula) =
  let name = App d.D.symbol [Var 0 t] in
  let positive = disjunction (R.mk_not_expr name) d.D.body in
  let negative = disjunction name (R.mk_not_expr d.D.body) in
  let rho = T.empty_environment (S.signature s) in
  let at (vs:V.arguments base (S.signature s) [t])
    : Lemma (
      let env = V.extend (S.signature s) [] [t] vs rho in
      T.truth_at s bc eq other [t] env positive /\
      T.truth_at s bc eq other [t] env negative) =
    let env = V.extend (S.signature s) [] [t] vs rho in
    lemma_disjunction s bc eq other [t] env (R.mk_not_expr name) d.D.body;
    lemma_disjunction s bc eq other [t] env name (R.mk_not_expr d.D.body);
    lemma_negation s bc eq other [t] env name;
    lemma_negation s bc eq other [t] env d.D.body in
  FStar.Classical.forall_intro at;
  Q.lemma_forall_truth s bc eq other [] rho [t] positive;
  Q.lemma_forall_truth s bc eq other [] rho [t] negative;
  T.lemma_cut s bc eq other 1 formula

let lemma_pair_at_arguments (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:D.definition) (t:sort)
  (vs:V.arguments base (S.signature s) [t])
  : Lemma (requires valid s inputs formula d /\ d.D.symbol.domain == [t] /\
      Q.forall_model s bc other /\ T.truth s bc eq other formula)
    (ensures (
      let env = V.extend (S.signature s) [] [t] vs (T.empty_environment (S.signature s)) in
      T.truth_at s bc eq other [t] env (App d.D.symbol [Var 0 t]) <==>
      T.truth_at s bc eq other [t] env d.D.body)) =
  let name = App d.D.symbol [Var 0 t] in
  let positive = disjunction (R.mk_not_expr name) d.D.body in
  let negative = disjunction name (R.mk_not_expr d.D.body) in
  let empty = T.empty_environment (S.signature s) in
  let env = V.extend (S.signature s) [] [t] vs empty in
  T.lemma_cut s bc eq other 1 formula;
  assert_norm (T.cut 1 (pair t d) ==
    B.Nary B.And [B.Atom (Quantifier Forall_k [t] bool_sort positive);
                  B.Atom (Quantifier Forall_k [t] bool_sort negative)]);
  Q.lemma_forall_truth s bc eq other [] empty [t] positive;
  Q.lemma_forall_truth s bc eq other [] empty [t] negative;
  assert (T.truth_at s bc eq other [t] env positive /\
          T.truth_at s bc eq other [t] env negative);
  lemma_disjunction s bc eq other [t] env (R.mk_not_expr name) d.D.body;
  lemma_disjunction s bc eq other [t] env name (R.mk_not_expr d.D.body);
  lemma_negation s bc eq other [t] env name;
  lemma_negation s bc eq other [t] env d.D.body

let lemma_pair_pointwise (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:D.definition) (t:sort)
  (rho:V.environment base (S.signature s) [t])
  : Lemma (requires valid s inputs formula d /\ d.D.symbol.domain == [t] /\
      Q.forall_model s bc other /\ T.truth s bc eq other formula)
    (ensures T.truth_at s bc eq other [t] rho (App d.D.symbol [Var 0 t]) <==>
             T.truth_at s bc eq other [t] rho d.D.body) =
  let name = App d.D.symbol [Var 0 t] in
  let env = V.extend (S.signature s) [] [t] [rho 0] (T.empty_environment (S.signature s)) in
  lemma_pair_at_arguments s bc eq other inputs formula d t [rho 0];
  let at (n:nat{n < L.length [t]}) : Lemma (env n == rho n) =
    assert_norm (L.length [t] == 1);
    assert (n == 0) in
  FStar.Classical.forall_intro at;
  Q.lemma_free_environments (S.signature s) (T.interpretation s bc eq other) [t] env rho name;
  Q.lemma_free_environments (S.signature s) (T.interpretation s bc eq other) [t] env rho d.D.body

let lemma_scalar_pair_truth (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:D.definition)
  : Lemma (requires scalar_valid s inputs formula d /\
      T.evaluate s bc eq other (App d.D.symbol []) ==
      T.evaluate s bc eq other d.D.body)
    (ensures T.truth s bc eq other formula) =
  match A.ite_parts d.D.body with
  | Some (condition, then_value, else_value) ->
    let name = App d.D.symbol [] in
    let positive = disjunction (R.mk_not_expr condition) (R.mk_eq_expr name then_value) in
    let negative = disjunction condition (R.mk_eq_expr name else_value) in
    let rho = T.empty_environment (S.signature s) in
    assert (formula == scalar_pair condition name then_value else_value);
    SA.lemma_ite_scope [] d.D.body condition then_value else_value;
    SA.lemma_ite s bc eq other [] rho d.D.body condition then_value else_value;
    lemma_disjunction s bc eq other [] rho (R.mk_not_expr condition)
      (R.mk_eq_expr name then_value);
    lemma_disjunction s bc eq other [] rho condition
      (R.mk_eq_expr name else_value);
    lemma_negation s bc eq other [] rho condition;
    T.lemma_equality s bc eq other d.D.body then_value;
    T.lemma_equality s bc eq other d.D.body else_value;
    T.lemma_equality s bc eq other name then_value;
    T.lemma_equality s bc eq other name else_value;
    T.lemma_nary s bc eq other (R.and_decl [positive; negative])
      [positive; negative] B.And;
    assert_norm (B.geval_args (T.truth s bc eq other) B.And
      [B.Atom positive; B.Atom negative] ==
      (T.truth s bc eq other positive && T.truth s bc eq other negative));
    let condition_true = T.truth s bc eq other condition in
    if condition_true then (
      assert (T.evaluate s bc eq other d.D.body == T.evaluate s bc eq other then_value);
      assert (T.evaluate s bc eq other name == T.evaluate s bc eq other then_value);
      assert (T.truth s bc eq other (R.mk_eq_expr name then_value));
      assert (T.truth s bc eq other (R.mk_not_expr condition) == false);
      assert (T.truth s bc eq other positive);
      assert (T.truth s bc eq other negative))
    else (
      assert (T.evaluate s bc eq other d.D.body == T.evaluate s bc eq other else_value);
      assert (T.evaluate s bc eq other name == T.evaluate s bc eq other else_value);
      assert (T.truth s bc eq other (R.mk_eq_expr name else_value));
      assert (T.truth s bc eq other condition == false);
      assert (T.truth s bc eq other positive);
      assert (T.truth s bc eq other negative));
    assert (T.truth s bc eq other formula)
  | None ->
    let name = App d.D.symbol [] in
    if formula = R.mk_eq_expr name d.D.body then (
      T.lemma_equality s bc eq other name d.D.body;
      assert (T.truth s bc eq other formula))
    else if formula = R.mk_eq_expr d.D.body name then (
      T.lemma_equality s bc eq other d.D.body name;
      assert (T.truth s bc eq other formula))

let test_schema : S.checked_schema =
  let s = { S.sorts = []; cases = [] } in
  assert_norm (S.valid s);
  s

let test_sort = BaseSort "U"
let test_symbol = {
  decl_name = "fresh"; domain = [test_sort]; range = bool_sort; interp = None; int_params = [];
}
let test_definition : D.definition = {
  D.symbol = test_symbol; variables = [0]; body = R.true_expr;
}
let test_pair = pair test_sort test_definition
let test_exists_definition : D.definition = {
  D.symbol = test_symbol; variables = [0];
  body = Quantifier Exists_k [test_sort] bool_sort
    (R.mk_eq_expr (Var 1 test_sort) (Var 0 test_sort));
}
let test_mismatched_pair =
  let name = App test_symbol [Var 0 test_sort] in
  let positive = Quantifier Forall_k [test_sort] bool_sort
    (disjunction (R.mk_not_expr name) R.true_expr) in
  let negative = Quantifier Forall_k [test_sort] bool_sort
    (disjunction name (R.mk_not_expr R.false_expr)) in
  let args = [positive; negative] in
  App (R.and_decl args) args

let lemma_pair_controls ()
  : Lemma (
    recognize test_schema [] test_pair == Some test_definition /\
    recognize test_schema [] (pair test_sort test_exists_definition) == Some test_exists_definition /\
    recognize test_schema [] test_mismatched_pair == None /\
    recognize test_schema [App test_symbol [App { decl_name = "x"; domain = [];
      range = test_sort; interp = None; int_params = [] } []]] test_pair == None /\
    recognize test_schema [] (pair test_sort { test_definition with
      D.body = App test_symbol [Var 0 test_sort] }) == None /\
    recognize test_schema [] (pair test_sort { test_definition with
      D.body = Var 1 bool_sort }) == None /\
    recognize test_schema [] R.true_expr == None) =
  assert_norm (recognize test_schema [] test_pair == Some test_definition);
  assert_norm (recognize test_schema [] (pair test_sort test_exists_definition) == Some test_exists_definition);
  assert_norm (recognize test_schema [] test_mismatched_pair == None);
  assert_norm (recognize test_schema [App test_symbol [App { decl_name = "x"; domain = [];
    range = test_sort; interp = None; int_params = [] } []]] test_pair == None);
  assert_norm (recognize test_schema [] (pair test_sort { test_definition with
    D.body = App test_symbol [Var 0 test_sort] }) == None);
  assert_norm (recognize test_schema [] (pair test_sort { test_definition with
    D.body = Var 1 bool_sort }) == None);
  assert_norm (recognize test_schema [] R.true_expr == None)

let test_scalar_symbol = {
  decl_name = "fresh-scalar"; domain = []; range = test_sort; interp = None; int_params = [];
}
let test_scalar_body_symbol = {
  decl_name = "scalar-body"; domain = []; range = test_sort; interp = None; int_params = [];
}
let test_scalar_body = App test_scalar_body_symbol []
let test_scalar_definition : D.definition = {
  D.symbol = test_scalar_symbol; variables = []; body = test_scalar_body;
}
let test_scalar_formula = R.mk_eq_expr test_scalar_body (App test_scalar_symbol [])
let test_scalar_input = [App test_scalar_symbol []]

let lemma_scalar_controls ()
  : Lemma (
    recognize test_schema [] test_scalar_formula == Some test_scalar_definition /\
    recognize test_schema test_scalar_input test_scalar_formula == None) =
  assert_norm (recognize test_schema [] test_scalar_formula == Some test_scalar_definition);
  assert_norm (recognize test_schema test_scalar_input test_scalar_formula == None)

let test_scalar_ite_condition = App {
  decl_name = "fresh-scalar-ite-condition"; domain = []; range = bool_sort;
  interp = None; int_params = []
} []
let test_scalar_ite_then = App {
  decl_name = "fresh-scalar-ite-then"; domain = []; range = test_sort;
  interp = None; int_params = []
} []
let test_scalar_ite_else = App {
  decl_name = "fresh-scalar-ite-else"; domain = []; range = test_sort;
  interp = None; int_params = []
} []
let test_scalar_ite_wrong_else = App {
  decl_name = "fresh-scalar-ite-wrong-else"; domain = []; range = test_sort;
  interp = None; int_params = []
} []
let test_scalar_ite_body =
  App (A.term_ite_decl test_sort)
    [test_scalar_ite_condition; test_scalar_ite_then; test_scalar_ite_else]
let test_scalar_ite_definition : D.definition = {
  D.symbol = test_scalar_symbol; variables = []; body = test_scalar_ite_body;
}
let test_scalar_ite_formula =
  scalar_pair test_scalar_ite_condition (App test_scalar_symbol [])
    test_scalar_ite_then test_scalar_ite_else
let test_scalar_ite_wrong_branch =
  scalar_pair test_scalar_ite_condition (App test_scalar_symbol [])
    test_scalar_ite_then test_scalar_ite_wrong_else

let lemma_scalar_ite_controls ()
  : Lemma (
    recognize test_schema [] test_scalar_ite_formula == Some test_scalar_ite_definition /\
    not (scalar_valid test_schema [] test_scalar_ite_wrong_branch test_scalar_ite_definition) /\
    recognize test_schema [App test_scalar_symbol []] test_scalar_ite_formula == None) =
  assert_norm (Some? (A.ite_parts test_scalar_ite_body));
  assert_norm (Recognition.definition_of test_scalar_ite_formula ==
    Some test_scalar_ite_definition);
  assert_norm (scalar_valid test_schema [] test_scalar_ite_formula test_scalar_ite_definition);
  assert_norm (recognize test_schema [] test_scalar_ite_formula == Some test_scalar_ite_definition);
  assert_norm (not (scalar_valid test_schema [] test_scalar_ite_wrong_branch
    test_scalar_ite_definition));
  assert_norm (recognize test_schema [App test_scalar_symbol []] test_scalar_ite_formula == None)
