module A = Z3AstTheory
module T = Z3OperatorTags
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof
module IB = Z3IndependentIntBounds
module RB = Z3IndependentRealBounds
module RDC = Z3IndependentRealDivisionClause

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
  let unary = { A.decl_name = "opaque"; domain = [real_sort]; range = real_sort;
                interp = None; int_params = [] } in
  let rec wrap n e = if n = 0 then e else wrap (n - 1) (A.App (unary, [e])) in
  let x = wrap 140 (variable real_sort "x") and y = wrap 140 (variable real_sort "y") in
  let arithmetic name tag a b =
    A.App ({ A.decl_name = name; domain = [real_sort; real_sort]; range = real_sort;
             interp = Some tag; int_params = [] }, [a; b]) in
  let plus = arithmetic "+" T.op_arith_add and times = arithmetic "*" T.op_arith_mul in
  let num n =
    A.App ({ A.decl_name = "num"; domain = []; range = real_sort;
             interp = Some T.op_num_rational; int_params = [Z.of_int n; Z.one] }, []) in
  let equation = R.mk_eq_expr x y in
  let normalized = R.mk_eq_expr (plus y (times (num (-1)) x)) (num 0) in
  let wrong = R.mk_eq_expr (plus y (times (num 1) x)) (num 0) in
  require (RB.check_large_equations equation normalized) "large valid equation rejected";
  require (not (RB.check_large_equations equation wrong)) "large invalid equation accepted";
  require (not (RB.check_large_equations (R.mk_eq_expr r r) (R.mk_eq_expr r r)))
    "small equation reached large replay";
  let huge = wrap 2100 r in
  let huge_equation = R.mk_eq_expr huge huge in
  require (not (RB.check_large_equations huge_equation huge_equation))
    "oversized equation reached large replay";
  let node = { U.kind = U.RewriteRule; conclusion = U.Equal (equation, normalized); premises = [] } in
  require (SP.real_rewrite schema node) "large equation rewrite not recognized";
  require (match SP.check_node_cached schema [] node with
    | Some (_, pending) -> Z.equal pending Z.zero | None -> false)
    "large equation rewrite remained pending";
  require (not (SP.real_rewrite schema { node with U.conclusion = U.Equal (equation, wrong) }))
    "wrong large equation rewrite accepted";
  let fact = { U.conclusion = U.Holds R.true_expr; hypotheses = [] } in
  require (not (SP.real_rewrite schema { node with U.premises = [fact] }))
    "large equation rewrite with premise accepted";
  let x, y, z = variable real_sort "x", variable real_sort "y", variable real_sort "z" in
  let zero, one, two = num 0, num 1, num 2 in
  let ge a b = comparison real_sort ">=" T.op_arith_ge a b in
  let le a b = comparison real_sort "<=" T.op_arith_le a b in
  let gt a b = comparison real_sort ">" T.op_arith_gt a b in
  let check facts goal =
    let premises = List.map (fun e -> { U.conclusion = U.Holds e; hypotheses = [] }) facts in
    let node = { U.kind = U.Unverified "arith/lp-monomial-interval";
                 conclusion = U.Holds goal; premises } in
    match SP.check_node_cached schema [] node with
    | Some (_, pending) -> Z.equal pending Z.zero
    | None -> false in
  let xy = times one (times x y) in
  require (check [gt (times one x) zero; ge (times one y) zero] (ge xy zero))
    "positive times nonnegative was not checked";
  require (check [le x zero; le y zero] (ge xy zero))
    "two nonpositive factors were not checked";
  require (not (check [ge x zero] (ge xy zero))) "missing factor bound was accepted";
  require (not (check [ge x zero; ge y zero] (ge (times one (times x z)) zero)))
    "wrong factor was accepted";
  require (not (check [ge x zero; ge y zero] (gt xy zero)))
    "nonstrict bounds implied a strict product";
  require (check [gt x one; gt y one] (gt (times x y) one))
    "factors greater than one were not checked";
  require (not (check [gt x one] (gt (times x y) one))) "missing strict bound was accepted";
  require (not (check [gt x one; gt y one] (gt (times x z) one)))
    "wrong strict factor was accepted";
  require (not (check [ge x one; ge y one] (gt (times x y) one)))
    "nonstrict bounds implied a product greater than one";
  require (not (check [gt x one; gt y one] (gt (times x y) two)))
    "greater-than-one bounds implied a product greater than two";
  let divide a b = arithmetic "/" T.op_arith_div a b in
  let disjunction a b =
    A.App ({ A.decl_name = "or"; domain = [A.bool_sort; A.bool_sort]; range = A.bool_sort;
             interp = Some T.op_or; int_params = [] }, [a; b]) in
  let guard = R.mk_eq_expr zero y in
  let body = R.mk_eq_expr x (times y (divide x y)) in
  let clause = disjunction guard body in
  require (RDC.check clause && RDC.check (disjunction body guard))
    "guarded division rejected";
  List.iter (fun c -> require (not (RDC.check c)) "invalid guarded division accepted")
    [body;
     disjunction (R.mk_eq_expr one y) body;
     disjunction guard (R.mk_eq_expr x (times y (divide z y)));
     disjunction guard (R.mk_eq_expr x (times y (divide x z)));
     disjunction guard (R.mk_eq_expr x (times z (divide x y)));
     disjunction guard (R.mk_eq_expr x (plus y (divide x y)));
     disjunction guard (R.mk_eq_expr x (times y (arithmetic "/" T.op_arith_mul x y)))];
  let division_node = { U.kind = U.Unverified "th-lemma"; conclusion = U.Holds clause;
                        premises = [] } in
  require (match SP.check_node_cached schema [] division_node with
    | Some (_, pending) -> Z.equal pending Z.zero | None -> false)
    "guarded division remained pending";
  print_endline "independent bounds rewrite tests passed"
