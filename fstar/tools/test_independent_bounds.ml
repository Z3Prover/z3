module A = Z3AstTheory
module T = Z3OperatorTags
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof
module IB = Z3IndependentIntBounds
module RB = Z3IndependentRealBounds

let require value message = if not value then failwith message
let schema = { S.sorts = []; cases = [] }
let variable sort name =
  A.App ({ A.decl_name = name; domain = []; range = sort;
           interp = None; int_params = [] }, [])
let comparison sort name tag a b =
  A.App ({ A.decl_name = name; domain = [sort; sort]; range = A.bool_sort;
           interp = Some tag; int_params = [] }, [a; b])
let conjunction a b =
  A.App ({ A.decl_name = "and"; domain = [A.bool_sort; A.bool_sort]; range = A.bool_sort;
           interp = Some T.op_and; int_params = [] }, [a; b])

let test sort check recognizes =
  let x, y, z = variable sort "x", variable sort "y", variable sort "z" in
  let equation = R.mk_eq_expr x y in
  let le = comparison sort "<=" T.op_arith_le x y in
  let ge = comparison sort ">=" T.op_arith_ge x y in
  let reversed = comparison sort "<=" T.op_arith_le y x in
  let lt = comparison sort "<" T.op_arith_lt x y in
  let wrong = comparison sort ">=" T.op_arith_ge x z in
  let spoof = comparison sort ">=" T.op_arith_le x y in
  let bounds = conjunction le ge in
  List.iter (fun candidate ->
    require (check equation candidate) "opposite bounds were rejected")
    [bounds; conjunction ge le; conjunction le reversed];
  List.iter (fun candidate ->
    require (not (check equation candidate)) "invalid bounds were accepted")
    [conjunction le le; conjunction lt ge; conjunction le wrong; conjunction le spoof];
  require (not (check le bounds)) "non-equation was accepted";
  let node a b = { U.kind = U.RewriteRule; conclusion = U.Equal (a, b); premises = [] } in
  List.iter (fun n ->
    require (recognizes n) "bounds rewrite was not recognized";
    require (match SP.check_node_cached schema [] n with
      | Some (_, pending) -> Z.equal pending Z.zero
      | None -> false) "bounds rewrite remained pending")
    [node equation bounds; node bounds equation;
     { (node equation bounds) with U.conclusion = U.Observational (equation, bounds) }];
  let valid = node equation bounds in
  let fact = { U.conclusion = U.Holds R.true_expr; hypotheses = [] } in
  List.iter (fun n -> require (not (recognizes n)) "invalid node was recognized")
    [{ valid with U.kind = U.Unverified "rewrite" };
     { valid with U.premises = [fact] };
     node equation (conjunction le lt);
     node (R.mk_eq_expr (A.Var (Z.zero, sort)) y) bounds]

let () =
  let int_sort = A.SortApp (A.IntSymbol, []) and real_sort = A.SortApp (A.RealSymbol, []) in
  test int_sort IB.check SP.int_bounds_rewrite;
  test real_sort RB.check (SP.real_rewrite schema);
  let i = variable int_sort "i" and r = variable real_sort "r" in
  let int_bounds = conjunction (comparison int_sort "<=" T.op_arith_le i i)
      (comparison int_sort ">=" T.op_arith_ge i i) in
  let real_bounds = conjunction (comparison real_sort "<=" T.op_arith_le r r)
      (comparison real_sort ">=" T.op_arith_ge r r) in
  require (not (IB.check (R.mk_eq_expr r r) real_bounds)) "Real equation was accepted as Int";
  require (not (RB.check (R.mk_eq_expr i i) int_bounds)) "Int equation was accepted as Real";
  print_endline "independent bounds rewrite tests passed"
