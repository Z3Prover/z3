module Z3LinearArithmeticAstTests

module A = Z3LinearArithmeticAst

open Z3AstTheory
open Z3OperatorTags

let test_farkas_rounding_requires_integer_comparison () : Lemma True =
  let x = Var 0 A.int_s in
  let y = Var 1 A.real_s in
  let to_real = {
    decl_name = "to_real";
    domain = [A.int_s];
    range = A.real_s;
    interp = Some op_to_real;
    int_params = [];
  } in
  let int_lt = {
    decl_name = "<";
    domain = [A.int_s; A.int_s];
    range = bool_sort;
    interp = Some op_arith_lt;
    int_params = [];
  } in
  let real_lt = {
    decl_name = "<";
    domain = [A.real_s; A.real_s];
    range = bool_sort;
    interp = Some op_arith_lt;
    int_params = [];
  } in
  let five_int = App {
    decl_name = "5i";
    domain = [];
    range = A.int_s;
    interp = Some op_num_rational;
    int_params = [5; 1];
  } [] in
  let integer_bound = App int_lt [x; five_int] in
  let mixed_bound = App real_lt [App to_real [x]; y] in
  assert_norm (
    match A.prepare_literal (1, 1) true integer_bound with
    | Some c -> not c.strict /\ c.poly.cst = -4
    | None -> false);
  assert_norm (
    match A.prepare_literal (1, 1) true mixed_bound with
    | Some c -> c.strict
    | None -> false)
