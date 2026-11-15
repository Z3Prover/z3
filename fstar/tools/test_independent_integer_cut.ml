module A = Z3AstTheory
module T = Z3OperatorTags
module U = Z3UnifiedProofSyntax
module S = Z3DatatypeSignature
module R = Z3ClauseSyntax
module C = Z3LpIntegerCutSyntax
module K = Z3SortedProof

let require value message = if not value then failwith message
let int_sort = A.SortApp (A.IntSymbol, [])
let variable name =
  A.App ({ A.decl_name = name; domain = []; range = int_sort;
           interp = None; int_params = [] }, [])
let numeral n = Z3LpGomorySyntax.integer (Z.of_int n)
let arithmetic name tag args =
  A.App ({ A.decl_name = name; domain = List.map A.get_sort args;
           range = int_sort; interp = Some tag; int_params = [] }, args)
let comparison name tag a b =
  A.App ({ A.decl_name = name; domain = [int_sort; int_sort]; range = A.bool_sort;
           interp = Some tag; int_params = [] }, [a; b])
let ge = comparison ">=" T.op_arith_ge
let le = comparison "<=" T.op_arith_le
let neg e = R.mk_not_expr e
let add args = arithmetic "+" T.op_arith_add args
let mul a b = arithmetic "*" T.op_arith_mul [a; b]

let () =
  let x, y, z = variable "x", variable "y", variable "z" in
  let zero, sixteen = numeral 0, numeral 16 in
  let a = add [x; mul (numeral (-16)) y; z] in
  let c = add [mul sixteen y; mul (numeral (-1)) z] in
  let facts = [neg (ge a sixteen); neg (ge c zero); ge z zero; le z zero; ge x zero] in
  require (K.check_integer_cut facts) "integer rounding conflict was not recovered";
  let opposite = [neg (ge x sixteen); ge a zero; neg (le c zero); ge z zero; le z zero] in
  require (K.check_integer_cut opposite) "opposite rounding conflict was not recovered";
  let weak = [le a sixteen; neg (ge c zero); ge z zero; le z zero; ge x zero] in
  require (not (K.check_integer_cut weak)) "satisfiable weakened conflict was accepted";
  let simple = [ge (mul sixteen x) (numeral 1); le (mul sixteen x) (numeral 15)] in
  let wrong : C.step = {
    bound = ge x (numeral 2);
    weights = [(Z.one, Z.one); (Z.zero, Z.one); (Z.of_int 16, Z.one)] } in
  require (K.check_integer_cut simple) "simple integer cut was not recovered";
  require (not (K.check_integer_cut_steps [wrong] simple)) "over-strong cut was accepted";
  let real_sort = A.SortApp (A.RealSymbol, []) in
  let real_x = A.App ({ A.decl_name = "r"; domain = []; range = real_sort;
                        interp = None; int_params = [] }, []) in
  let real_zero = A.App ({ A.decl_name = "0"; domain = []; range = real_sort;
                           interp = Some T.op_num_rational; int_params = [Z.zero; Z.one] }, []) in
  let real_ge = A.App ({ A.decl_name = ">="; domain = [real_sort; real_sort]; range = A.bool_sort;
                         interp = Some T.op_arith_ge; int_params = [] }, [real_x; real_zero]) in
  require (not (K.check_integer_cut [real_ge])) "real input was admitted to integer cuts";
  let schema = { S.sorts = []; cases = [] } in
  let node = { U.kind = U.Unverified "th-lemma"; conclusion = U.Holds R.false_expr;
               premises = List.map (fun e ->
                 { U.conclusion = U.Holds e; hypotheses = [List.hd facts] }) facts } in
  require (match K.check_node_cached schema [] node with
           | Some (fact, pending) -> Z.equal pending Z.zero && fact.U.hypotheses = [List.hd facts]
           | None -> false) "integer cut was not dispatched for a theory conflict";
  require (match K.check_node_cached schema [] { node with U.kind = U.LemmaRule } with
           | Some (_, pending) -> Z.equal pending Z.one
           | None -> false) "integer cut changed lemma-rule handling";
  print_endline "independent integer-cut tests passed"
