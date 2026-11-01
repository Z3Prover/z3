module N = Z3Native
module B = Z3NativeProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module A = Z3AstTheory
module C = Z3LpCertificate

let require condition message = if not condition then failwith message

let context () =
  let config = Z3native.mk_config () in
  Z3native.set_param_value config "proof" "true";
  let c = Z3native.mk_context_rc config in
  Z3native.del_config config;
  Z3native.set_internal_error_handler c;
  c

let parse c text =
  let vector = Z3native.parse_smtlib2_string c text 0 [] [] 0 [] [] in
  List.init (Z3native.ast_vector_size c vector) (Z3native.ast_vector_get c vector)

let unsat text =
  match N.solve text Z.zero with
  | N.Unsat (assertions, proof) -> assertions, proof
  | _ -> failwith "expected an UNSAT proof"

let document text =
  let assertions, proof = unsat text in
  let doc = B.marshal assertions proof in
  require (P.check_document_indexed (fun value -> Z.of_int (Hashtbl.hash value)) doc =
           P.check_document doc) "indexed and linear checker results differ";
  doc

let clausal_proofs () =
  let branching =
    "(declare-const p Bool)(declare-const q Bool)\
     (assert (or p q))(assert (or p (not q)))\
     (assert (or (not p) q))(assert (or (not p) (not q)))" in
  List.iter (fun source ->
      let assertions, proof = match N.solve_with_clause_proofs source Z.zero true with
        | N.Unsat (assertions, proof) -> assertions, proof
        | _ -> failwith "clausal solver did not return UNSAT" in
      if source = branching then
        require (N.view_clause_trail proof <> None) "SMT search did not return a clause trail";
      let doc = try B.marshal assertions proof with exn ->
        failwith (source ^ ": " ^ Printexc.to_string exn) in
      require (P.check_document doc = Some Z.zero) "clausal refutation was not fully checked";
      require (P.check_document { doc with assertions = [] } = None)
        "clausal refutation accepted missing original assertions";
      let corrupted = List.mapi (fun index entry ->
          if Z.equal (Z.of_int index) doc.root then
            { entry with P.formula = Z3ResolutionProofTheory.true_expr }
          else entry) doc.entries in
      require (P.check_document { doc with entries = corrupted } = None)
        "clausal refutation accepted a non-false root")
    [branching;
     "(declare-sort U 0)(declare-const x U)(declare-const y U)\
      (declare-fun f (U) U)(assert (= x y))(assert (not (= (f x) (f y))))";
     "(declare-const x Real)(declare-const y Real)\
      (assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))";
     "(declare-const x Real)(declare-const y Real)(declare-const p Bool)\
      (assert (or p (<= x (- 6.0))))(assert (=> p (>= (+ x y) 1.5)))\
      (assert (< y (/ 1.0 3.0)))(assert (> x 0.0))(assert (<= x 1.0))";
     "(declare-const a (Array Int Int))(declare-const i Int)\
      (assert (not (= (select (store a i 1) i) 1)))";
     "(declare-sort I 0)(declare-sort E 0)(declare-const a (Array I E))\
      (declare-const i I)(declare-const j I)(declare-const v E)\
      (assert (distinct i j))\
      (assert (distinct (select (store a i v) j) (select a j)))"];
  let c = context () in
  let formula = List.hd (parse c "(declare-const p Bool)(assert p)") in
  let st = B.marshal_expressions (B.empty_state ()) [formula] in
  let db, builder = Z3ClauseProof.empty (B.clause_builder st) in
  let st = B.with_clause_builder st builder in
  let rejected =
    try
      ignore (B.add_clause_entry st db
                { N.action = N.LearnedClause; formula; literals = [formula];
                  certificate = None });
      false
    with N.Error _ -> true in
  require rejected "an unsupported learned unit passed RUP"

let shared_expressions () =
  let c = context () in
  let assertions = parse c
      "(declare-fun f (Int Int) Int)(declare-const x Int)\
       (assert (= (f x x) (f x x)))" in
  let root = List.hd assertions in
  let st = B.marshal_expressions (B.empty_state ()) [root; root] in
  let value = B.cached_expression st root in
  (match value with
   | A.App (_, [left; right]) ->
       require (left == right) "shared application was allocated twice";
       (match left with
        | A.App (_, [x; y]) -> require (x == y) "shared constant was allocated twice"
        | _ -> failwith "expected binary application")
   | _ -> failwith "expected equality");
  let again = B.marshal_expressions st assertions in
  require (value == B.cached_expression again root) "cache did not reuse the same OCaml value";
  require (List.length again.all_expressions = 3) "expression was inserted more than once";
  Gc.full_major ();
  require (value == B.cached_expression again root) "cache failed after collection"

let deep_expression () =
  let c = context () in
  let int_sort = Z3native.mk_int_sort c in
  let symbol s = Z3native.mk_string_symbol c s in
  let decl = Z3native.mk_func_decl c (symbol "f") 1 [int_sort] int_sort in
  let root = ref (Z3native.mk_const c (symbol "x") int_sort) in
  for _ = 1 to 12000 do root := Z3native.mk_app c decl 1 [!root] done;
  let st = B.marshal_expressions (B.empty_state ()) [!root; !root] in
  require (List.length st.all_expressions = 12001) "deep DAG was not traversed once"

let proof_cache () =
  let assertions, proof = unsat
      "(declare-const p Bool)(declare-const q Bool)\
       (assert (or p q))(assert (not p))(assert (not q))" in
  let st = B.marshal_expressions (B.empty_state ()) assertions in
  let st = B.marshal_proof_jobs st [B.VisitProof proof] in
  let count = st.next_proof in
  let repeated = B.marshal_proof_jobs st [B.VisitProof proof; B.VisitProof proof] in
  require (Z.equal count repeated.next_proof) "proof DAG was inserted twice";
  require (st.entries == repeated.entries) "proof cache rebuilt checked entries"

let exact_numerals () =
  let c = context () in
  let n = Z.of_string "123456789012345678901234567890123456789" in
  let source = Printf.sprintf
      "(declare-const x Real)(assert (= x (/ %s 97)))" (Z.to_string n) in
  let st = B.marshal_expressions (B.empty_state ()) (parse c source) in
  require (List.exists (function
      | A.App (d, []) when d.interp = Some Z3ValueTheory.op_num_rational ->
          d.int_params = [n; Z.one]
      | _ -> false) st.all_expressions) "large numeral was truncated";
  let q = N.rational "-123456789012345678901234567890/97" in
  require (q = (Z.of_string "-123456789012345678901234567890", Z.of_int 97))
    "foreign rational was rounded"

let pretty_expressions () =
  let c = context () in
  let declarations =
    "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)\
     (declare-const x Int)(declare-const y Int)(declare-const z Int)" in
  let check source expected arithmetic =
    let assertions = parse c
        (declarations ^ "(assert " ^ (if arithmetic then "(= " ^ source ^ " 0)" else source) ^ ")") in
    let st = B.marshal_expressions (B.empty_state ()) assertions in
    let value = B.cached_expression st (List.hd assertions) in
    let value = if arithmetic then match value with
        | A.App (_, [left; _]) -> left
        | _ -> failwith "expected equality"
      else value in
    let actual = Z3NativeMain.pretty_expr value in
    require (actual = expected) ("pretty expression: " ^ actual ^ "; expected: " ^ expected) in
  List.iter (fun (source, expected, arithmetic) -> check source expected arithmetic)
    ["(and p (or q r))", "p and (q or r)", false;
     "(or (and p q) r)", "p and q or r", false;
     "(= p (= q r))", "p = (q = r)", false;
     "(+ x (* y z))", "x + y * z", true;
     "(* (+ x y) z)", "(x + y) * z", true;
     "(- x (- y z))", "x - (y - z)", true;
     "(- (- x))", "-(-x)", true;
     "(not (<= (+ x (* y z)) 0))", "not (x + y * z <= 0)", false];
  let fake = A.App ({ A.decl_name = "and"; domain = []; range = A.BaseSort "Bool";
                     interp = None; int_params = [] }, []) in
  require (Z3NativeMain.pretty_expr fake = "|and|") "uninterpreted connective was printed as logic";
  (* Hand-built shapes shared with the Cherry driver's expression rows (cherry_runtime/tests.cpp pretty_regressions
     expects the same strings): binders, numerals, names, sorts and bounds. *)
  let module V = Z3ValueTheory in
  let bool_s = A.BaseSort "Bool" and int_s = A.BaseSort "Int" and real_s = A.BaseSort "Real" in
  let app name domain range interp args =
    A.App ({ A.decl_name = name; domain; range; interp; int_params = [] }, args) in
  let constant name range = app name [] range None [] in
  let numeral n d range =
    A.App ({ A.decl_name = "numeral"; domain = []; range; interp = Some V.op_num_rational;
             int_params = [n; d] }, []) in
  let var i s = A.Var (Z.of_int i, s) in
  let x = constant "decl!3:x" int_s and p = constant "decl!1:p" bool_s and q = constant "decl!2:q" bool_s in
  let binary kind token a b = app token [int_s; int_s] (if kind = V.op_eq then bool_s else int_s) (Some kind) [a; b] in
  let disjunction a b = app "or" [bool_s; bool_s] bool_s (Some V.op_or) [a; b] in
  let negation a = app "not" [bool_s] bool_s (Some V.op_not) [a] in
  let ten n = Z.pow (Z.of_int 10) n in
  let shared = [
    "binders", A.Quantifier (A.Forall_k, [int_s; bool_s], bool_s,
                             disjunction (binary V.op_eq "=" (var 1 int_s) x) (var 0 bool_s)),
      "forall (#b0:Int, #b1:Bool). #b0 = x or #b1";
    "negated binder", negation (A.Quantifier (A.Exists_k, [int_s], bool_s,
      app ">" [int_s; int_s] bool_s (Some V.op_arith_gt) [var 0 int_s; numeral Z.zero Z.one int_s])),
      "not (exists (#b0:Int). #b0 > 0)";
    "rational summand", app "+" [int_s; real_s] real_s (Some V.op_arith_add) [x; numeral (Z.of_int (-7)) (Z.of_int 3) real_s],
      "x + -7/3";
    "negative factor", binary V.op_arith_mul "*" x (numeral (Z.of_int (-5)) Z.one int_s), "x * -5";
    "negated negative numeral", app "-" [int_s] int_s (Some V.op_arith_sub) [numeral (Z.of_int (-5)) Z.one int_s], "-(-5)";
    "64-character numeral", numeral (ten 63) Z.one int_s, Z.to_string (ten 63);
    "65-character numeral", numeral (ten 64) Z.one int_s, "...:Int";
    "65-character negative numeral", numeral (Z.neg (ten 63)) Z.one int_s, "...:Int";
    "unbound variable", var 3 int_s, "#3";
    "quoted name", constant "decl!2:a b" int_s, "|a b|";
    "long name", constant ("decl!9:" ^ String.make 300 'a') int_s, "|" ^ String.make 256 'a' ^ "...|";
    "uninterpreted keyword", constant "decl!4:or" bool_s, "|or|";
    "non-numeric id", constant "decl!x:y" int_s, "|decl!x:y|";
    "binder sorts", A.Quantifier (A.Lambda_k, [A.ArraySort ([int_s], bool_s); A.BaseSort "sort!5:T"],
                                  A.ArraySort ([A.ArraySort ([int_s], bool_s); A.BaseSort "sort!5:T"], A.ArraySort ([int_s], bool_s)),
                                  var 1 (A.ArraySort ([int_s], bool_s))),
      "lambda (#b0:Array[Int; Bool], #b1:T). #b0";
    "uninterpreted application", app "decl!7:f" [int_s; int_s] int_s None [x; numeral Z.one Z.one int_s], "f(x, 1)";
    "argument limit", app "decl!7:f" (List.init 33 (fun _ -> int_s)) int_s None (List.init 33 (fun _ -> x)), "...:Int"] in
  List.iter (fun (label, value, expected) ->
      let actual = Z3NativeMain.pretty_expr value in
      require (actual = expected) ("pretty " ^ label ^ ": " ^ actual ^ "; expected: " ^ expected)) shared;
  let deep = ref p in
  for _ = 1 to 13 do deep := negation !deep done;
  let expected = ref "not ...:Bool" in
  for _ = 1 to 11 do expected := "not (" ^ !expected ^ ")" done;
  require (Z3NativeMain.pretty_expr !deep = !expected) "pretty depth limit";
  List.iter (fun (label, judgment, expected) ->
      let actual = Z3NativeMain.pretty_judgment judgment in
      require (actual = expected) ("pretty " ^ label ^ ": " ^ actual ^ "; expected: " ^ expected))
    ["equality judgment", U.Equal (x, binary V.op_arith_add "+" x (numeral Z.one Z.one int_s)), "x = x + 1";
     "observational judgment", U.Observational (p, disjunction p q), "p ~ (p or q)";
     "holds judgment", U.Holds (disjunction p q), "p or q"]

let native_farkas () =
  let doc = document
      "(declare-const x Real)(declare-const y Real)\
       (assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))" in
  let certs = List.filter_map (fun e -> match e.P.rule with
      | U.ArithmeticFarkas cs -> Some cs | _ -> None) doc.entries in
  require (certs <> []) "real Z3 proof did not marshal supplied Farkas parameters";
  require (List.for_all (List.for_all (fun (_, den) -> Z.sign den > 0)) certs)
    "native Farkas denominator was invalid";
  require (P.check_document doc = Some Z.zero) "native arithmetic derivation was not fully checked";
  List.iter (fun coefficients ->
      let entries = List.map (fun entry -> match entry.P.rule with
          | U.ArithmeticFarkas cs -> { entry with P.rule = U.ArithmeticFarkas (coefficients cs) }
          | _ -> entry) doc.entries in
      require (match P.check_document { doc with entries } with
          | Some pending -> Z.sign pending > 0
          | None -> false) "incorrect Farkas weights lost their obligation")
    [(fun _ -> []); List.map (fun (_, denominator) -> Z.zero, denominator)];
  let baseline = match P.check_document doc with
    | Some pending -> pending
    | None -> failwith "native arithmetic derivation was rejected" in
  (match P.diagnose_document doc with
   | P.DocumentChecked (_, obligations) ->
       require (List.for_all (fun o -> match o.P.obligation_rule with
           | U.ArithmeticFarkas _ -> false | _ -> true) obligations)
         "native arithmetic certificate retained an obligation"
   | _ -> failwith "native arithmetic diagnostic was rejected");
  let changed = ref false in
  let entries = List.map (fun e -> match e.P.rule with
      | U.ArithmeticFarkas cs when not !changed ->
          changed := true;
          { e with rule = U.ArithmeticFarkas (List.map (fun _ -> Z.zero, Z.one) cs) }
      | _ -> e) doc.entries in
  (match P.check_document { doc with entries } with
   | Some pending -> require (Z.gt pending baseline) "corrupt candidate weights were trusted"
   | None -> failwith "candidate-weight mutation malformed the proof document")

let native_integer_tightening () =
  let doc = document
      "(declare-const x Int)(declare-const y Int)(declare-const z Int)\
       (assert (= (+ x (* 2 y)) 0))(assert (= (+ x (* 2 z)) 1))" in
  require (List.exists (fun e -> e.P.rule = U.Unverified "arith/lp-integer-tighten") doc.entries)
    "integer LP inference metadata was hidden";
  require (P.check_document doc = Some Z.zero) "native integer tightening did not replay";
  let mutated = ref false in
  let entries = List.map (fun e ->
      if e.P.rule = U.Unverified "arith/lp-integer-tighten" && not !mutated then begin
        mutated := true;
        { e with P.premise_ids = [List.hd e.P.premise_ids] }
      end else e) doc.entries in
  require !mutated "native proof contained no integer tightening to mutate";
  require (match P.check_document { doc with entries } with
      | Some pending -> Z.sign pending > 0 | None -> true)
    "integer tightening without its actual premise was certified"

let distinct_reflexivity () =
  let c = context () in
  let check expected declarations left right =
    let inputs = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let formula = B.cached_expression st (List.hd inputs) in
    let conclusion = Option.get (U.classify_fact formula) in
    require (U.check_step U.RewriteRule conclusion [] = expected)
      ("incorrect distinct rewrite: " ^ left ^ " -> " ^ right)
  in
  check true "(declare-const x Int)" "(distinct x x)" "false";
  check true "(declare-const x Int)(declare-const y Int)" "(distinct x y x)" "false";
  check true "(declare-const x Real)" "(distinct x x)" "false";
  check true "(declare-sort S 0)(declare-const x S)" "(distinct x x)" "false";
  check true "(declare-const a (Array Int Int))" "(distinct a a)" "false";
  check false "(declare-const x Int)(declare-const y Int)" "(distinct x y)" "false";
  check false "(declare-const x Int)" "(distinct x x)" "true";
  check true "(declare-const x Int)(declare-const y Int)" "(distinct x y)" "(not (= x y))";
  check true "(declare-const x Real)(declare-const y Real)" "(not (= x y))" "(distinct x y)";
  check true "(declare-sort S 0)(declare-const x S)(declare-const y S)"
    "(distinct x y)" "(not (= x y))";
  check true "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
    "(distinct x y z)" "(and (not (= x y)) (not (= x z)) (not (= y z)))";
  check false "(declare-const x Int)(declare-const y Int)" "(distinct x y)" "(= x y)";
  check false "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
    "(distinct x y z)" "(and (not (= x y)) (not (= y z)))";
  let x = A.Var (Z.zero, A.BaseSort "Int") in
  let declaration = Z3DistinctAst.distinct_decl (A.BaseSort "Int") (Z.of_int 2) in
  let malformed = A.App ({ declaration with A.interp = None }, [x; x]) in
  require (not (U.check_step U.RewriteRule
      (U.Equal (malformed, Z3ResolutionProofTheory.false_expr)) []))
    "an uninterpreted distinct name was trusted";
  require (not (U.check_step U.RewriteRule
      (U.Equal (malformed, Z3DistinctAst.expanded [x; x])) []))
    "an uninterpreted distinct expansion was trusted"

let integer_tightening_candidates () =
  let c = context () in
  let check expected declarations premise conclusion =
    let sources = parse c
        (declarations ^ "(assert " ^ premise ^ ")(assert " ^ conclusion ^ ")") in
    let st = B.marshal_expressions (B.empty_state ()) sources in
    let expressions = List.map (B.cached_expression st) sources in
    match expressions with
    | [p; q] ->
        require (Z3LpReplay.check_tightening q [Z3ResolutionProofTheory.true_expr; p] = expected)
          ("incorrect integer tightening: " ^ premise ^ " => " ^ conclusion);
        require (not (Z3LpReplay.check_tightening q [Z3ResolutionProofTheory.false_expr; p]))
          "integer tightening accepted a malformed context";
        require (not (Z3LpReplay.check_tightening q []))
          "integer tightening certified a conclusion without a premise"
    | _ -> failwith "expected two arithmetic formulas"
  in
  let ints = "(declare-const x Int)" in
  check true ints "(<= (* 2 x) 1)" "(<= x 0)";
  check true ints "(>= (* 2 x) 1)" "(>= x 1)";
  check true ints "(<= (* 2 x) (- 1))" "(<= x (- 1))";
  check true ints "(< (* 2 x) 2)" "(<= x 0)";
  check true ints "(> (* 2 x) (- 2))" "(>= x 0)";
  check true ints "(<= (* 2 (to_real x)) 1.0)" "(<= x 0)";
  check false ints "(<= (* 2 x) 1)" "(<= x (- 1))";
  check false ints "(>= (* 2 x) 1)" "(>= x 2)";
  check false ints "(<= (* 2 x) 1)" "(>= x 1)";
  check false "(declare-const x Real)" "(<= (* 2 x) 1)" "(<= x 0)";
  check false "(declare-const x Real)" "(>= (* 2 x) 1)" "(>= x 1)";
  List.iter (fun (source, expected) ->
      let inputs = parse c ("(declare-const x Int)(assert " ^ source ^ ")") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let formula = B.cached_expression st (List.hd inputs) in
      require (U.checked_theory_lemma (U.ArithmeticFarkas [Z.zero, Z.one])
          (Option.get (U.classify_fact formula)) [] = expected)
        ("incorrect LP identity replay: " ^ source))
    ["(= (+ x (* (- 1) x)) 0)", true;
     "(= (+ x (* (- 1) x)) 1)", false;
     "(= (* x x) x)", false]

let checked_gomory_cuts () =
  let module G = Z3LpGomory in
  let fact relation lhs rhs = {
    C.relation; contradiction = false; rhs; epsilon = Z.zero, Z.one; lhs
  } in
  let step rule conclusion = {
    C.rule; conclusion; input = None; assumption = None; id = Z.zero;
    equation = fact C.Eq [] (Z.zero, Z.one); pivot = None; definition = None;
    source = None; divisor = Z.one, Z.one; premises = []; bounds = []
  } in
  let q n d = Z.of_int n, Z.of_int d in
  let run real lower scale pivot_scale bound cut_scale cut_rhs cut_den =
    let c = context () in
    let x = if real then "(to_real x)" else "x" in
    let column = Printf.sprintf "(* %d %s)" scale x in
    let pivot = Printf.sprintf "(* %d x)" pivot_scale in
    let source = Printf.sprintf
        "(declare-const x Int)(assert (= %s %s))(assert (= %s %s))\
         (assert (%s %s %d))(assert (>= (* %d %s) %d))"
        pivot pivot column column (if lower then ">=" else "<=") column bound
        cut_scale column cut_rhs in
    let inputs = parse c source in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match List.map (B.cached_expression st) inputs with
    | A.App (_, [pivot; _]) :: A.App (_, [column; _]) :: premise :: conclusion :: [] ->
        let variables = [
          { C.term = pivot; integer = true; definition = [] };
          { C.term = column; integer = not real; definition = [] }] in
        let input = step C.Input (fact (if lower then C.Ge else C.Le)
            [q 1 1, Z.one] (q bound 1)) in
        let cut = { (step C.Gomory (fact C.Ge
            [q cut_scale cut_den, Z.one] (q cut_rhs cut_den))) with
          C.pivot = Some Z.zero;
          equation = fact C.Eq [q 1 1, Z.zero; q (-pivot_scale) scale, Z.one] (q 0 1);
          premises = [Z.zero, q 1 1];
          bounds = [{ C.bound_column = Z.one;
                      lower = if lower then Some Z.zero else None;
                      upper = if lower then None else Some Z.zero }] } in
        let certificate = {
          C.variables; monomials = []; steps = [input; cut]; root = Z.one } in
        let candidate = match G.candidate certificate Z.one with
          | Some value -> value | None -> failwith ("no Gomory candidate: " ^ source) in
        let facts = [Z3ResolutionProofTheory.true_expr; premise] in
        require (G.check candidate conclusion facts) ("Gomory cut failed: " ^ source);
        require (not (G.check candidate Z3ResolutionProofTheory.false_expr facts))
          "Gomory accepted a false conclusion from satisfiable bounds";
        require (not (G.check candidate conclusion [Z3ResolutionProofTheory.true_expr]))
          "Gomory ignored a missing bound";
        require (not (G.check { candidate with G.split = Z3ResolutionProofTheory.true_expr }
            conclusion facts)) "Gomory allowed a non-integer split";
        require (not (G.check { candidate with G.below = [] } conclusion facts))
          "Gomory accepted an unchecked split branch";
        require (not (G.check { candidate with G.above = [] } conclusion facts))
          "Gomory accepted an unchecked opposite branch";
        require (G.candidate { certificate with C.steps = [input;
            { cut with C.equation = fact C.Eq [q 2 1, Z.zero] (q 0 1) }] } Z.one = None)
          "Gomory accepted a non-unit pivot recipe"
    | _ -> failwith "unexpected Gomory fixture expressions"
  in
  run false false 2 1 1 (-1) 0 1;
  run false true 2 1 1 1 2 1;
  run false false 2 1 (-1) (-1) 2 1;
  run false false 5 3 3 (-3) (-5) 4;
  run true false 2 1 1 (-1) 0 1;
  run true true 2 1 1 1 2 1;
  let doc = document
      "(declare-const x Int)(declare-const y Int)\
       (assert (<= 0 (- (* 28300000000000 x) (* 24500000000001 y))))\
       (assert (<= (- (* 28300000000000 x) (* 24500000000001 y)) 99999999999))\
       (assert (<= 1 (- (* 28300000000001 x) (* 24500000000000 y))))\
       (assert (<= (- (* 28300000000001 x) (* 24500000000000 y)) 100000000000))" in
  let cuts = List.filter (fun e -> match e.P.rule with
      | U.ArithmeticGomory _ -> true | _ -> false) doc.entries in
  require (cuts <> []) "native Gomory split parameters were not marshaled";
  List.iter (fun e ->
      let conclusion = Option.get (U.classify_fact e.P.formula) in
      let premises = List.map (fun j ->
          Option.get (U.classify_fact (List.nth doc.entries (Z.to_int j)).P.formula))
          e.P.premise_ids in
      require (U.checked_theory_lemma e.P.rule conclusion premises)
        "authentic native Gomory cut was not certified";
      require (not (U.checked_theory_lemma e.P.rule
          (U.Holds Z3ResolutionProofTheory.false_expr) premises))
        "native Gomory metadata bypassed actual conclusion checking") cuts

let native_lp_certificates () =
  let assertions, proof = unsat
      "(declare-const x Int)(declare-const y Int)(declare-const z Int)\
       (assert (= (+ x (* 2 y)) 0))(assert (= (+ x (* 2 z)) 1))" in
  let st = B.marshal_expressions (B.empty_state ()) assertions in
  let st = B.marshal_proof_jobs st [B.VisitProof proof] in
  let visited = Hashtbl.create 32 in
  let contexts = ref [] in
  let rec collect = function
    | [] -> ()
    | p :: rest ->
        let id = N.ast_id p in
        if Hashtbl.mem visited id then collect rest else begin
          Hashtbl.add visited id ();
          let view = N.view_proof p in
          (match view.lp_data with
           | Some ("lp-context", ps) -> contexts := (p, ps) :: !contexts
           | _ -> ());
          collect (view.premises @ rest)
        end
  in
  collect [proof];
  require (!contexts <> []) "native LP context parameters were hidden";
  List.iter (fun (p, parameters) ->
      let raw = B.marshal_parameters st parameters in
      let certificate = match C.decode raw with
        | Some value -> value | None -> failwith "authentic LP context failed to decode" in
      require (Z3ProofIndex.index_get st.lp_certificates (N.ast_id p) = Some certificate)
        "decoded certificate was not cached with its native context";
      require (certificate.variables <> [] && certificate.steps <> [])
        "native LP certificate lost its variables or steps";
      let reject raw message = require (C.decode raw = None) message in
      reject (C.Rational (Z.of_int 2, Z.one) :: List.tl raw) "unknown LP version was accepted";
      reject (C.Rational (Z.one, Z.zero) :: List.tl raw) "zero denominator was accepted";
      reject (C.Rational (Z.one, Z.minus_one) :: List.tl raw) "negative denominator was accepted";
      reject (raw @ [C.Rational (Z.zero, Z.one)]) "trailing LP parameters were accepted";
      reject (List.rev (List.tl (List.rev raw))) "truncated LP context was accepted";
      let bad_root = List.rev (C.Rational (Z.of_string "4294967295", Z.one) ::
                               List.tl (List.rev raw)) in
      reject bad_root "out-of-range LP root was accepted";
      let bad_sort = List.map (function
          | C.Expression _ -> C.Expression Z3ResolutionProofTheory.true_expr
          | p -> p) raw in
      reject bad_sort "non-arithmetic LP variable was accepted";
      let invalid_count = match raw with
        | version :: _ :: rest ->
            version :: C.Rational (Z.of_string "4294967295", Z.one) :: rest
        | _ -> failwith "missing LP header" in
      reject invalid_count "unbounded LP count was accepted";
      List.iteri (fun index step ->
          require (not (C.step_refs (Z.of_int (List.length certificate.variables))
              (Z.of_int (List.length certificate.monomials)) (Z.of_int index)
              { step with C.premises = [Z.of_int index, (Z.one, Z.one)] }))
            "forward LP premise was accepted") certificate.steps;
      let first = List.hd certificate.steps in
      let nv = Z.of_int (List.length certificate.variables) in
      let nm = Z.of_int (List.length certificate.monomials) in
      let index = Z.of_int (List.length certificate.steps) in
      let lattice = { first with C.rule = C.IntegerLattice; pivot = Some Z.zero;
                                 source = None; bounds = [] } in
      require (C.step_refs nv nm index lattice)
        "lattice step required the unused monomial source field";
      let bounds:C.column_bounds list = [{ C.bound_column = Z.zero; lower = Some Z.zero; upper = None }] in
      require (not (C.step_refs nv nm index { lattice with C.bounds = bounds; premises = [] }))
        "LP bound index was treated as a global step rather than a premise position")
    !contexts;
  require (C.read_uint [C.Rational (Z.minus_one, Z.one)] = None)
    "negative LP index was accepted";
  require (C.read_uint [C.Rational (Z.one, Z.of_int 2)] = None)
    "fractional LP index was accepted";
  require (C.read_uint [C.Rational (Z.of_string "4294967296", Z.one)] = None)
    "overflowing LP index was accepted"

let native_bound () =
  let doc = document
      "(declare-const x Real)(declare-const y Real)(declare-const p Bool)\
       (assert (or p (<= x (- 6.0))))(assert (=> p (>= (+ x y) 1.5)))\
       (assert (and (< y (/ 1.0 3.0)) (> x 0.0)))(assert (not (= x 7.0)))\
       (assert (<= x 1.0))" in
  require (P.check_document doc = Some Z.zero)
    "native bound certificate did not replay through exact Farkas checking"

let native_assign_bounds () =
  let text = Buffer.create 1024 in
  for i = 0 to 4 do
    Buffer.add_string text (Printf.sprintf "(declare-const x%d Int)" i)
  done;
  let add formula = Buffer.add_string text ("(assert " ^ formula ^ ")") in
  for i = 0 to 3 do
    add (Printf.sprintf "(>= (- x%d x4) 0)" i);
    add (Printf.sprintf "(<= (- x%d x4) 3)" i)
  done;
  for i = 0 to 3 do
    for j = i + 1 to 3 do
      List.iter (fun d ->
          let numeral = if d < 0 then Printf.sprintf "(- %d)" (-d) else string_of_int d in
          add (Printf.sprintf "(not (= (- x%d x%d) %s))" i j numeral))
        [0; j - i; i - j; 4 + i - j; j - i - 4]
    done
  done;
  let assertions, proof = unsat (Buffer.contents text) in
  let st = B.marshal_expressions (B.empty_state ()) assertions in
  let st = B.marshal_proof_jobs st [B.VisitProof proof] in
  let seen = Hashtbl.create 32 in
  let checked = ref 0 in
  let rec visit = function
    | [] -> ()
    | p :: rest ->
        let id = N.ast_id p in
        if Hashtbl.mem seen id then visit rest else begin
          Hashtbl.add seen id ();
          let view = N.view_proof p in
          let c = N.ctx p in
          let declaration = Z3native.get_app_decl c (Z3native.to_app c p) in
          let is_assign_bounds =
            Z3native.get_decl_num_parameters c declaration >= 2 &&
            Z3enums.parameter_kind_of_int
              (Z3native.get_decl_parameter_kind c declaration 1) = Z3enums.PARAMETER_SYMBOL &&
            N.symbol c (Z3native.get_decl_symbol_parameter c declaration 1) = "assign-bounds" in
          if is_assign_bounds then begin
            incr checked;
            let formula = B.cached_expression st view.conclusion in
            let conclusion = Option.get (U.classify_fact formula) in
            let facts = List.map (fun p ->
                Option.get (U.classify_fact (B.cached_expression st (N.view_proof p).conclusion)))
                view.premises in
            let rule = B.native_rule view formula in
            require (U.checked_theory_lemma rule conclusion facts)
              "authentic assign-bounds weights did not replay";
            let coefficients = match rule with
              | U.ArithmeticFarkas cs -> cs
              | _ -> failwith "assign-bounds parameters were not decoded" in
            List.iter (fun cs ->
                require (not (U.checked_theory_lemma (U.ArithmeticFarkas cs) conclusion facts))
                  "corrupt assign-bounds weights were trusted")
              [[]; List.map (fun (_, d) -> Z.zero, d) coefficients]
          end;
          visit (view.premises @ rest)
        end
  in
  visit [proof];
  require (!checked > 0) "fixture contained no authentic assign-bounds hints"

let strict_inputs_and_scopes () =
  let doc = document "(assert false)" in
  require (P.check_document doc = Some Z.zero) "asserted false was not accepted";
  require (P.check_document { doc with assertions = [] } = None)
    "asserted leaf escaped input membership";
  let hypothesis = { P.rule = U.Hypothesis; formula = Z3ResolutionProofTheory.false_expr;
                     premise_ids = [] } in
  require (P.check_document { doc with entries = [hypothesis]; root = Z.zero } = None)
    "open hypothesis certified a refutation";
  let pending = { hypothesis with rule = U.Unverified "new-theory-rule" } in
  require (P.check_document { doc with entries = [pending]; root = Z.zero } = Some Z.one)
    "unknown proof rule was not a pending obligation";
  let forward = { pending with premise_ids = [Z.one] } in
  require (P.check_document { doc with entries = [forward]; root = Z.zero } = None)
    "forward proof reference was accepted";
  let invalid = { hypothesis with rule = U.ModusPonens } in
  require (P.check_document { doc with entries = doc.entries @ [invalid] } = None)
    "unreachable malformed proof entry was ignored"

let indexed_assertion_membership () =
  let source = List.init 40 (fun i ->
    Printf.sprintf "(declare-const p%d Bool)(assert p%d)" i i) |>
    String.concat "" in
  let doc = document (source ^ "(assert false)") in
  let doc = { doc with entries = doc.entries @
    List.map (fun formula -> { P.rule = U.Asserted; formula; premise_ids = [] }) doc.assertions } in
  require (List.length doc.assertions > 16) "fixture did not exercise the assertion index";
  require (P.enough_asserted (Z.of_int 17) doc.entries)
    "fixture had too few asserted leaves to build the index";
  let false_expr = Z3ResolutionProofTheory.false_expr in
  let missing = { doc with assertions = List.filter ((<>) false_expr) doc.assertions } in
  let duplicate = { doc with assertions = List.rev (doc.assertions @ doc.assertions) } in
  let leaf = { P.rule = U.Unverified "unsupported-index-fixture";
               formula = false_expr; premise_ids = [] } in
  let pending = { doc with entries = [leaf]; root = Z.zero } in
  let forward = { pending with entries = [{ leaf with premise_ids = [Z.zero] }] } in
  List.iter (fun hash ->
    List.iter (fun fixture ->
      require (P.check_document_indexed hash fixture = P.check_document fixture)
        "indexed membership changed acceptance, rejection, or obligations";
      require (P.diagnose_document_indexed hash fixture = P.diagnose_document fixture)
        "indexed membership changed typed diagnostics")
      [doc; missing; duplicate; pending; forward; { doc with assertions = [] }];
    require (P.check_document_indexed hash missing = None)
      "colliding hash certified an unregistered assertion")
    [(fun _ -> Z.zero); (fun _ -> Z.of_string "999999999999999999999999999999999999999");
     (fun value -> Z.of_int (Hashtbl.hash value)); Z3NativeMain.assertion_hash];
  let values = [Z.zero; Z.one; Z.one; Z.of_int 65521] in
  List.iter (fun hash ->
    let index = Z3ProofSet.of_list hash values in
    List.iter (fun query ->
      require (Z3ProofSet.member hash query index = List.mem query values)
        "hash bucket did not preserve exact membership")
      [Z.zero; Z.one; Z.of_int 2; Z.of_int 65521])
    [(fun _ -> Z.zero); (fun value -> value)]

let cached_definition_expansion () =
  let module D = Z3Definitions in
  let bool_sort = A.BaseSort "Bool" in
  let declaration name = {
    A.decl_name = name; domain = []; range = bool_sort;
    interp = None; int_params = [];
  } in
  let p_decl = declaration "p" and marker = declaration "defined" in
  let p = A.App (p_decl, []) and named = A.App (marker, []) in
  let conjunction = {
    A.decl_name = "and"; domain = [bool_sort; bool_sort]; range = bool_sort;
    interp = Some Z3ValueTheory.op_and; int_params = [];
  } in
  let defs = [{ D.symbol = marker; variables = []; body = p }] in
  let hashes = List.init 128 (fun index ->
    let leaf = A.App (declaration ("leaf" ^ string_of_int index), []) in
    Z3NativeMain.assertion_hash (U.Holds (A.App (conjunction, [p; leaf])))) in
  require (List.length (List.sort_uniq Z.compare hashes) >= 64)
    "production hashing collapsed distinct children below a common connective";
  let shared depth leaf =
    let result = ref leaf in
    for _ = 1 to depth do result := A.App (conjunction, [!result; !result]) done;
    !result in
  let check_sharing depth expression =
    let current = ref expression in
    for _ = 1 to depth do
      match !current with
      | A.App (_, [left; right]) ->
          require (left == right) "definition expansion destroyed expression DAG sharing";
          current := left
      | _ -> failwith "expanded DAG lost a conjunction"
    done;
    require (!current = p) "definition expansion produced the wrong leaf" in
  List.iter (fun hash ->
    List.iter (fun fuel ->
      let source = shared 5 named in
      require (D.memoized_expand hash fuel defs source = D.expand fuel defs source)
        "cached expansion differs from its reference")
      [Z.zero; Z.one; Z.of_int 3];
    let source = shared 30 p in
    let transform = D.memoized_expander hash in
    let binder = {
      U.binder_name = "refl"; binder_formula = source;
      binder_premises = []; binder_sorts = None;
    } in
    let rule = U.QuantifierIntroduction {
      U.binder_entries = [binder]; binder_root = Z.zero;
    } in
    (match P.expand_rule_using transform defs rule with
     | Some (U.QuantifierIntroduction { U.binder_entries = [entry]; _ }) ->
         require (entry.U.binder_formula == source)
           "binder definition expansion destroyed expression DAG sharing"
     | _ -> failwith "binder definition expansion failed");
    let entry = { P.rule = rule; formula = p; premise_ids = [] } in
    require (P.collect_skolems_using transform defs [] [entry] = Some [])
      "Skolem collection bypassed shared binder expansion";
    require (Prims.([source] = [source]))
      "runtime equality failed below distinct expression wrappers";
    require (Prims.([source] <> [shared 30 named]))
      "runtime equality confused different shared expressions";
    (match D.memoized_expand hash Z.one defs source with
     | Some result -> require (result == source) "unchanged expression DAG was rebuilt"
     | None -> failwith "unchanged definition expansion failed");
    (match D.memoized_expand hash Z.one defs (shared 30 named) with
     | Some result -> check_sharing 30 result
     | None -> failwith "shared definition expansion failed");
    let (failed, _), cache = D.expand_cached hash Z.zero defs named Z3ProofIndex.Empty in
    require (failed = None) "zero-fuel definition expansion succeeded";
    let (success, _), cache = D.expand_cached hash Z.one defs named cache in
    require (success = Some p) "a cached fuel failure poisoned a later expansion";
    let (failed, _), _ = D.expand_cached hash Z.zero defs named cache in
    require (failed = None) "cached expansion reused a result with insufficient fuel";
    let cyclic = [{ D.symbol = marker; variables = []; body = named }] in
    require (D.memoized_expand hash (Z.of_int 3) cyclic named = None)
      "cached expansion accepted a cyclic definition";
    let malformed = [{ D.symbol = marker; variables = []; body = A.Var (Z.zero, bool_sort) }] in
    require (D.memoized_expand hash Z.one malformed named = None)
      "cached expansion accepted an unbound substitution";
    let function_decl = { marker with A.domain = [bool_sort] } in
    let body = A.Quantifier (A.Forall_k, [bool_sort], bool_sort, A.Var (Z.one, bool_sort)) in
    let parameterized = [{ D.symbol = function_decl; variables = [Z.zero]; body }] in
    let application = A.App (function_decl, [A.Var (Z.zero, bool_sort)]) in
    require (D.memoized_expand hash Z.one parameterized application =
             D.expand Z.one parameterized application)
      "cached expansion changed capture-avoiding substitution")
    [(fun _ -> Z.zero); (fun _ -> Z.of_int 65521);
     (fun value -> Z.of_int (Hashtbl.hash value));
     (fun (_, expression) -> Z3NativeMain.assertion_hash (U.Holds expression))]

let ordered_congruence_matching () =
  let atom name = A.App ({
    A.decl_name = name; domain = []; range = A.BaseSort "Bool";
    interp = None; int_params = [];
  }, []) in
  let x, y, z = atom "x", atom "y", atom "z" in
  List.iter (fun relation ->
    List.iter (fun (left, right, facts, expected) ->
      require (U.fast_arguments_match relation left right facts = expected)
        "congruence fast path accepted a missing or reversed argument";
      require (U.fast_arguments_match relation left right facts =
               U.arguments_match relation left right facts)
        "congruence fast path changed matching semantics")
      [([x; y; z], [y; z; z], [U.Equal (x, y); U.Equal (y, z)], true);
       ([x; y; z], [y; z; z], [U.Equal (y, z); U.Equal (x, y)], true);
       ([x; y], [y; z], [U.Equal (x, y)], false);
       ([x], [y], [U.Equal (y, x)], false);
       ([x], [], [], false);
       ([x], [x], [], true)])
    [U.Equality; U.Observation]

let typed_diagnostics () =
  let doc = document "(assert false)" in
  require (P.diagnose_document doc = P.DocumentChecked (Z.zero, []))
    "complete proof acquired an obligation";
  let source = (List.hd doc.entries).P.formula in
  let leaf = { P.rule = U.Unverified "unsupported-theory"; formula = source; premise_ids = [] } in
  let partial = { doc with entries = [leaf]; root = Z.zero } in
  (match P.diagnose_document partial with
   | P.DocumentChecked (pending, [obligation]) ->
       require (P.check_document partial = Some pending && Z.equal pending Z.one)
         "diagnostic pending count disagrees with the checker";
       require (Z.equal obligation.P.obligation_index Z.zero &&
                obligation.P.obligation_rule = leaf.rule &&
                obligation.P.obligation_conclusion = U.Holds source &&
                obligation.P.obligation_premises = [] &&
                Z.equal obligation.P.obligation_count Z.one)
         "typed obligation lost its checked context";
       require (obligation.P.obligation_source == source)
         "diagnostics rebuilt a marshaled source expression"
   | _ -> failwith "pending obligation was not reported");
  let malformed = { partial with entries = [{ leaf with premise_ids = [Z.zero] }] } in
  (match P.diagnose_document malformed with
   | P.DocumentRejected (P.ProofEntry, Some index, Some formula) ->
       require (Z.equal index Z.zero && formula == source && P.check_document malformed = None)
         "malformed premise reference has an inconsistent diagnostic"
   | _ -> failwith "malformed premise reference was not diagnosed");
  let no_input = { doc with assertions = [] } in
  (match P.diagnose_document no_input with
   | P.DocumentRejected (P.ProofEntry, Some index, _) ->
       require (Z.equal index Z.zero && P.check_document no_input = None)
         "input-membership diagnostic disagrees with the checker"
   | _ -> failwith "input membership failure was not diagnosed");
  List.iter (fun fixture ->
      List.iter (fun hash ->
          let result, diagnostic = P.check_document_diagnosed_indexed hash fixture in
          require (result = P.check_document_indexed hash fixture &&
                   diagnostic = P.diagnose_document_indexed hash fixture)
            "single-pass legacy checking changed a verdict or diagnostic")
        [(fun _ -> Z.zero); Z3NativeMain.assertion_hash])
    [doc; partial; malformed; no_input; { doc with root = Z.minus_one }];
  List.iter (fun (diagnostic, expected) ->
      let rejected =
        try Z3NativeMain.report_diagnostics diagnostic expected; false
        with N.Error _ -> true in
      require rejected "single-pass diagnostics lost a mismatch guard")
    [P.DocumentChecked (Z.one, []), Some Z.one;
     P.DocumentChecked (Z.zero, []), Some Z.one;
     P.DocumentRejected (P.ProofEntry, None, None), Some Z.zero]

(* --readable renders what the checker saw, within explicit bounds. Expressions are built by hand,
   so malformed metadata and shapes no solver produces (200,000 layers, 2^100 shared occurrences,
   million-bit numerals) are covered next to the ordinary ones. *)
let readable_conditions () =
  let module R = Z3NativeMain.Readable in
  let z = Z.of_int in
  let base name = A.BaseSort name in
  let int_sort = base "Int" and bool_sort = base "Bool" and real_sort = base "Real" in
  let bv8 = base "BV8" and bv32 = base "BV32" in
  let declaration ?interp ?(params = []) name domain range =
    { A.decl_name = name; domain; range; interp; int_params = params } in
  let constant ?interp ?params name range = A.App (declaration ?interp ?params name [] range, []) in
  let numeral ?(range = int_sort) n d =
    constant ~interp:Z3ValueTheory.op_num_rational ~params:[n; d] "numeral" range in
  let bv_numeral width value =
    constant ~interp:Z3BvLemma.op_numeral ~params:[z width; value]
      "bv" (base (Printf.sprintf "BV%d" width)) in
  let text e = fst (R.judgment_text (U.Holds e)) in
  let expect label actual expected =
    require (actual = expected) (Printf.sprintf "%s: %S, expected %S" label actual expected) in
  let contains text needle =
    let n = String.length needle in
    let rec from i = i + n <= String.length text && (String.sub text i n = needle || from (i + 1)) in
    from 0 in
  (* values and sorts *)
  expect "integer numeral" (text (numeral (z 5) Z.one)) "holds(5)";
  expect "rational numeral" (text (numeral ~range:real_sort (z (-7)) (z 3))) "holds(-7/3:Real)";
  expect "integral real numeral" (text (numeral ~range:real_sort (z 2) Z.one)) "holds(2:Real)";
  expect "bit-vector numeral" (text (bv_numeral 8 (z 255))) "holds((_ bv255 8))";
  expect "wide bit-vector numeral"
    (text (bv_numeral 64 (Z.of_string "18446744073709551615")))
    "holds((_ bv18446744073709551615 64))";
  let extract = declaration ~interp:Z3BvLemma.op_extract ~params:[z 32; z 15; z 8] "extract" [bv32] bv8 in
  expect "extraction parameters" (text (A.App (extract, [A.Var (z 0, bv32)])))
    "holds((extract[32,15,8]:BV8 #0:BV32))";
  expect "multi-index array" (text (A.Var (z 0, A.ArraySort ([int_sort; int_sort], bool_sort))))
    "holds(#0:(Array Int Int Bool))";
  expect "nested array" (text (A.Var (z 1, A.ArraySort ([int_sort], A.ArraySort ([bv8], bool_sort)))))
    "holds(#1:(Array Int (Array BV8 Bool)))";
  let inner = A.Quantifier (A.Exists_k, [bv8], bool_sort, A.Var (z 1, int_sort)) in
  expect "nested binders"
    (text (A.Quantifier (A.Forall_k, [int_sort; A.ArraySort ([int_sort], bool_sort)], bool_sort, inner)))
    "holds((forall [Int (Array Int Bool)] (exists [BV8] #1:Int)))";
  expect "lambda"
    (text (A.Quantifier (A.Lambda_k, [int_sort], A.ArraySort ([int_sort], bool_sort), A.Var (z 0, int_sort))))
    "holds((lambda [Int] #0:Int))";
  (* identity: same-named declarations stay apart, datatype operations are not connectives *)
  let f7 = declaration "decl!7:f" [int_sort] int_sort and f9 = declaration "decl!9:f" [real_sort] int_sort in
  let x = constant "decl!3:x" int_sort and y = constant "decl!4:y" real_sort in
  expect "first same-named function" (text (A.App (f7, [x]))) "holds((f#7:Int x#3:Int))";
  expect "second same-named function" (text (A.App (f9, [y]))) "holds((f#9:Int y#4:Real))";
  expect "uninterpreted symbol without a native id" (text (constant "g" bool_sort)) "holds(g#-:Bool)";
  expect "user sort" (text (constant "decl!6:t" (base "sort!5:T"))) "holds(t#6:T#5)";
  let p = constant "decl!1:p" bool_sort and q = constant "decl!2:q" bool_sort in
  let conjunction = declaration ~interp:Z3ValueTheory.op_and "and" [bool_sort; bool_sort] bool_sort in
  expect "Boolean connective" (text (A.App (conjunction, [p; q]))) "holds((and p#1:Bool q#2:Bool))";
  let owner = base "sort!5:T" in
  let accessor = declaration ~interp:Z3DatatypeLemma.op_accessor ~params:[z 5; z 12; z 0] "and" [owner] bool_sort in
  expect "accessor named like a connective"
    (text (A.App (accessor, [constant "decl!6:t" owner]))) "holds((and@accessor[5,12,0]:Bool t#6:T#5))";
  expect "constructor named like a constant"
    (text (constant ~interp:Z3DatatypeLemma.op_constructor ~params:[z 5; z 13; z 0] "true" owner))
    "holds(true@constructor[5,13,0]:T#5)";
  (* names *)
  expect "Unicode name" (text (constant "decl!3:h\xc3\xa9llo \xe2\x98\x83" int_sort)) "holds(|h\xc3\xa9llo \xe2\x98\x83|#3:Int)";
  expect "bar, backslash and control bytes" (text (constant "decl!4:a|b\\c\n" int_sort))
    "holds(|a\\x7cb\\x5cc\\x0a|#4:Int)";
  expect "invalid UTF-8" (text (constant "decl!5:\xff\xc0\x80\xed\xa0\x80" int_sort))
    "holds(|\\xff\\xc0\\x80\\xed\\xa0\\x80|#5:Int)";
  expect "C1 control" (text (constant "decl!5:\xc2\x85" int_sort)) "holds(|\\xc2\\x85|#5:Int)";
  expect "empty name" (text (constant "" int_sort)) "holds(||#-:Int)";
  expect "name starting with a digit" (text (constant "1x" int_sort)) "holds(|1x|#-:Int)";
  expect "long name" (text (constant ("decl!1:" ^ String.make 300 'a') int_sort))
    ("holds(|" ^ String.make 96 'a' ^ "...<204 more bytes>|#1:Int)");
  (* numerals are checked against 10^100 before they are converted *)
  let nines = String.make 100 '9' in
  expect "100-digit numeral" (text (numeral (Z.of_string nines) Z.one)) ("holds(" ^ nines ^ ")");
  expect "negative 100-digit numeral" (text (numeral (Z.neg (Z.of_string nines)) Z.one)) ("holds(-" ^ nines ^ ")");
  expect "101-digit numeral" (text (numeral (Z.pow (z 10) 100) Z.one))
    "holds(<+huge integer: more than 100 digits omitted>)";
  expect "negative huge numeral" (text (numeral (Z.neg (Z.pow (z 10) 400)) Z.one))
    "holds(<-huge integer: more than 100 digits omitted>)";
  let started = Sys.time () in
  expect "million-bit numeral" (text (numeral (Z.shift_left Z.one 4_000_000) (z 3)))
    "holds(<+huge integer: more than 100 digits omitted>/3)";
  require (Sys.time () -. started < 5.0) "a huge numeral was converted before the size check";
  (* malformed metadata is shown as reflected, never repaired *)
  expect "rational without a denominator"
    (text (constant ~interp:Z3ValueTheory.op_num_rational ~params:[z 5] "5" int_sort)) "holds(|5|[5]:Int)";
  expect "bit-vector numeral without a value"
    (text (constant ~interp:Z3BvLemma.op_numeral ~params:[z 8] "bv" bv8)) "holds(bv[8]:BV8)";
  expect "bit-vector numeral with an extra parameter"
    (text (constant ~interp:Z3BvLemma.op_numeral ~params:[z 8; z 255; z 1] "bv" bv8)) "holds(bv[8,255,1]:BV8)";
  expect "unknown interpretation" (text (constant ~interp:(z 999) "weird" bool_sort)) "holds(weird)";
  expect "parameter limit" (text (constant ~params:(List.init 40 z) "decl!1:p" bool_sort))
    ("holds(p#1[" ^ String.concat "," (List.init 16 string_of_int) ^ ",<24 more>]:Bool)");
  (* limits leave explicit markers and stay cheap *)
  let negation = declaration ~interp:Z3ValueTheory.op_not "not" [bool_sort] bool_sort in
  let deep = ref p in
  for _ = 1 to 200_000 do deep := A.App (negation, [!deep]) done;
  let rendered, cut = R.judgment_text (U.Holds !deep) in
  require (cut && contains rendered "<...depth>" && String.length rendered < 400) "deep expression was not cut";
  let pair = declaration "decl!8:g" [int_sort; int_sort] int_sort in
  let dag = ref x in
  for _ = 1 to 100 do dag := A.App (pair, [!dag; !dag]) done;
  let started = Sys.time () in
  let rendered, cut = R.judgment_text (U.Holds !dag) in
  require (Sys.time () -. started < 5.0) "a shared DAG was expanded";
  require (cut && String.length rendered <= R.max_chars + 16) "shared DAG output was not bounded";
  let rendered, cut =
    R.judgment_text (U.Holds (A.App (declaration "decl!8:h" [] int_sort, List.init 5000 (fun _ -> numeral (z 5) Z.one)))) in
  require (cut && contains rendered "<...nodes>") "node limit left no marker";
  let rendered, cut =
    R.judgment_text (U.Holds (A.Var (z 0, A.ArraySort (List.init 3000 (fun _ -> int_sort), bool_sort)))) in
  require (cut && contains rendered "<...chars>" && String.length rendered <= R.max_chars + 16)
    "character limit left no marker";
  let nested = ref bool_sort in
  for _ = 1 to 100 do nested := A.ArraySort ([int_sort], !nested) done;
  let rendered, cut = R.judgment_text (U.Holds (A.Var (z 0, !nested))) in
  require (cut && contains rendered "<...depth>") "sort depth limit left no marker";
  (* the report: node index, premise ids, truncation, and no unrelated premises *)
  let five = numeral (z 5) Z.one in
  let conclusion = A.App (declaration ~interp:Z3ValueTheory.op_eq "=" [int_sort; int_sort] bool_sort, [x; five]) in
  let leaf = { P.rule = U.Unverified "th-lemma"; formula = conclusion; premise_ids = [z 31; z 77] } in
  let doc = { P.declarations = []; expressions = []; assertions = []; entries = [leaf; leaf]; root = z 1 } in
  let obligation ?(rule = leaf.P.rule) ?(index = 1) ?(count = 2) conclusion =
    { P.obligation_index = z index; obligation_rule = rule; obligation_conclusion = conclusion;
      obligation_premises = [U.Holds p; U.Equal (x, x)]; obligation_source = leaf.P.formula;
      obligation_count = z count } in
  let checked ?(document = doc) obligations =
    R.report_text 3 "PARTIAL 2" document (P.DocumentChecked (z 2, obligations)) in
  expect "checked report" (checked [obligation (U.Holds conclusion)])
    ("readable\tquery=3\tverdict=PARTIAL 2\tpending=2\tfamilies=1\tshown=1\n\
      readable\tfamily=1/1\trule=th-lemma\tcount=2\tmembers=1\tnode=1\tnode-pending=2\n\
     \  node 1: premises: #31 #77\n\
     \  premise #31: holds(p#1:Bool)\n\
     \  premise #77: equal(x#3:Int, x#3:Int)\n\
     \  conclusion: holds((= x#3:Int 5))\n\
     \  source formula: same as conclusion\n\
      readable\tend\tquery=3\n");
  let differing = checked [obligation (U.Equal (x, five))] in
  require (contains differing "  conclusion: equal(x#3:Int, 5)\n  source formula: holds((= x#3:Int 5))\n")
    "a differing source formula was hidden";
  let unmatched = checked [obligation ~rule:(U.Unverified "other") (U.Holds conclusion)] in
  require (contains unmatched
             "  node 1: no source-node mapping (the document entry at this index has another rule or premise count): premise ids unavailable\n  premise [0]: holds(p#1:Bool)\n")
    "premises were attached to a node of another rule";
  require (not (contains unmatched "#31") && not (contains unmatched "#77")) "unrelated premise ids were shown";
  let miscounted = checked [{ (obligation (U.Holds conclusion)) with P.obligation_premises = [U.Holds p] }] in
  require (contains miscounted "no source-node mapping (the document entry at this index has another rule or premise count)" &&
           not (contains miscounted "#31"))
    "premises were attached to a node with another premise count";
  require (contains (checked [obligation ~index:9 (U.Holds conclusion)])
             "  node 9: no source-node mapping (no document entry at this index): premise ids unavailable\n")
    "an obligation without a document entry got premise ids";
  require (contains (R.report_text 7 "REJECT" doc (P.DocumentRejected (P.MissingPremise, Some (z 9), None)))
             "  node 9: no source-node mapping (no document entry at this index)\n")
    "a rejection without a document entry claimed premises";
  let numbered = List.init 25 (fun i ->
      obligation ~rule:(U.Unverified (Printf.sprintf "rule-%02d" i)) ~index:0 ~count:(i + 1) (U.Holds conclusion)) in
  let limited = checked numbered in
  require (contains limited "pending=2\tfamilies=25\tshown=20\n" &&
           contains limited "readable\tomitted\tfamilies=5\treason=family-limit\n" &&
           contains limited "readable\tfamily=20/25\trule=rule-05\tcount=6\t" &&
           not (contains limited "rule=rule-04\t"))
    "family limit";
  let heavy = A.App (declaration "decl!8:h" [] int_sort, List.init 600 (fun _ -> x)) in
  let big_premises = List.init 8 (fun _ -> U.Holds heavy) in
  let big = List.init 6 (fun i ->
      { (obligation ~rule:(U.Unverified (Printf.sprintf "big-%d" i)) (U.Holds heavy)) with
        P.obligation_premises = big_premises; obligation_source = heavy }) in
  let sized = checked big in
  require (String.length sized < R.max_report_chars + 200 &&
           contains sized "readable\tomitted\treason=report-size\nreadable\tend\tquery=3\n")
    "report size limit";
  expect "rejected report"
    (R.report_text 4 "REJECT" doc (P.DocumentRejected (P.ProofEntry, Some (z 1), Some conclusion)))
    ("readable\tquery=4\tverdict=REJECT\tstage=proof-entry\tindex=1\n\
     \  node 1: rule=th-lemma premises: #31 #77\n\
     \  source formula: holds((= x#3:Int 5))\n\
      readable\tend\tquery=4\n");
  expect "rejected report without a node"
    (R.report_text 5 "REJECT" doc (P.DocumentRejected (P.MissingRoot, None, None)))
    ("readable\tquery=5\tverdict=REJECT\tstage=missing-root\tindex=-\n\
     \  source formula: none reported\n\
      readable\tend\tquery=5\n");
  require (not (contains (R.report_text 6 "REJECT" doc (P.DocumentRejected (P.OpenRoot, Some (z 1), None))) "  node "))
    "a root-stage rejection claimed a proof node"

(* The printer reads a finished diagnostic. On one fixed proof document: the check and diagnose results and the machine rows are the same
   before and after readable output is rendered, neither the document nor the diagnostic is modified, and rendering performs no
   checking (the hash the checker calls per judgment is not called). The CLI driver gives the same verdict, summary and machine rows
   with and without --readable on the same native proof, and the readable records only extend them. *)
let readable_same_proof () =
  let module R = Z3NativeMain.Readable in
  let capture_stderr f =
    let path = Filename.temp_file "readable" ".stderr" in
    let fd = Unix.openfile path [Unix.O_WRONLY; Unix.O_TRUNC] 0o600 in
    let saved = Unix.dup Unix.stderr in
    flush stderr;
    Unix.dup2 fd Unix.stderr;
    Fun.protect ~finally:(fun () -> flush stderr; Unix.dup2 saved Unix.stderr; Unix.close saved; Unix.close fd) f;
    let text = In_channel.with_open_bin path In_channel.input_all in
    Sys.remove path;
    text in
  let contains text needle =
    let n = String.length needle in
    let rec from i = i + n <= String.length text && (String.sub text i n = needle || from (i + 1)) in
    from 0 in
  (* A chain of 20 asserted equalities (the checker indexes its inputs by hashing them from 17 asserted entries on, which is what the
     call counter below observes) under a nonlinear conflict that leaves a pending theory lemma. *)
  let declarations = String.concat "" (List.init 21 (fun i -> Printf.sprintf "(declare-const x%d Real)" i)) in
  let chain = String.concat "" (List.init 20 (fun i -> Printf.sprintf "(assert (= x%d x%d))" i (i + 1))) in
  let assertions, proof = unsat (declarations ^ chain ^ "(assert (= (* x20 x20) 2))(assert (= (* x0 x0 x0) 3))") in
  let doc, schema = B.marshal_with_datatypes assertions proof in
  require (schema.Z3DatatypeSignature.cases = []) "expected the legacy checker";
  let calls = ref 0 in
  let hash value = incr calls; Z3NativeMain.assertion_hash value in
  let document_bytes () = Marshal.to_string doc [] in
  let before = document_bytes () in
  let result, diagnostic = P.check_document_diagnosed_indexed hash doc in
  let checks = !calls in
  require (checks > 0) "the diagnosed check did not hash anything";
  let pending = match diagnostic with
    | P.DocumentChecked (n, _ :: _) -> n
    | _ -> failwith "expected pending obligations" in
  require (result = Some pending) "the diagnosed result disagrees with the diagnostic";
  let rows_before = capture_stderr (fun () -> Z3NativeMain.report_diagnostics diagnostic result) in
  require (contains rows_before "obligation\tth-lemma\t") "no machine row for the pending theory lemma";
  let diagnostic_bytes = Marshal.to_string diagnostic [] in
  let text = R.report_text 1 (Z3NativeMain.result_text result) doc diagnostic in
  require (contains text "readable\tquery=1\tverdict=PARTIAL ") "no readable block for the pending proof";
  require (!calls = checks) "rendering invoked the checker";
  require (document_bytes () = before) "rendering changed the proof document";
  require (Marshal.to_string diagnostic [] = diagnostic_bytes) "rendering changed the diagnostic";
  require (R.report_text 1 (Z3NativeMain.result_text result) doc diagnostic = text)
    "the readable block is not a function of the diagnostic";
  require (capture_stderr (fun () -> Z3NativeMain.report_diagnostics diagnostic result) = rows_before)
    "the machine rows changed after rendering";
  let result', diagnostic' = P.check_document_diagnosed_indexed hash doc in
  require (result' = result && diagnostic' = diagnostic) "the check result changed after rendering";
  require (!calls = 2 * checks) "a diagnosed check is not a fixed amount of work";
  require (P.check_document_indexed Z3NativeMain.assertion_hash doc = result) "diagnosed and plain verdicts differ";
  (* the driver on the same native proof, with and without readable output *)
  let run readable =
    let outcome = ref (None, "") in
    let stderr_text = capture_stderr (fun () ->
        outcome := Z3NativeMain.check_proof false true readable 1 false 0.0 0.0 assertions proof) in
    !outcome, stderr_text in
  let (plain_result, plain_summary), plain_stderr = run false in
  let (readable_result, readable_summary), readable_stderr = run true in
  let untimed summary = String.concat " " (List.filteri (fun i _ -> i >= 3) (String.split_on_char ' ' summary)) in
  require (plain_result = result && readable_result = result) "the driver verdict differs from the document check";
  require (untimed plain_summary = untimed readable_summary) "--readable changed the driver summary";
  require (plain_stderr = rows_before) "the driver's machine rows differ from the diagnostic rows";
  require (String.starts_with ~prefix:plain_stderr readable_stderr &&
           String.starts_with ~prefix:"readable\tquery=1\t"
             (String.sub readable_stderr (String.length plain_stderr) (String.length readable_stderr - String.length plain_stderr)))
    "the readable records do not simply extend the machine rows";
  require (Marshal.to_string (fst (B.marshal_with_datatypes assertions proof)) [] = before)
    "the proof document changed after the driver rendered it"

(* Cases the golden renders of readable_conditions do not reach: bit-vector values as the checker reflected them (encoded signed,
   malformed, wider than a machine word), wide extractions, malformed decl!/sort! identities, and the report branches that bound
   premises or name a stage. Expectations come from the printer's contract, not from observed output: what the checker saw is shown
   verbatim (never re-encoded, repaired or reduced), an unmatched native identity is a plain quoted name, and every limit leaves a
   marker. tests.cpp repeats each expectation for the Cherry printer. *)
let readable_edge_cases () =
  let module R = Z3NativeMain.Readable in
  let z = Z.of_int in
  let base name = A.BaseSort name in
  let int_sort = base "Int" and bool_sort = base "Bool" in
  let declaration ?interp ?(params = []) name domain range =
    { A.decl_name = name; domain; range; interp; int_params = params } in
  let constant ?interp ?params name range = A.App (declaration ?interp ?params name [] range, []) in
  let bv_numeral width value =
    constant ~interp:Z3BvLemma.op_numeral ~params:[z width; value] "bv" (base (Printf.sprintf "BV%d" width)) in
  let text e = fst (R.judgment_text (U.Holds e)) in
  let expect label actual expected =
    require (actual = expected) (Printf.sprintf "%s: %S, expected %S" label actual expected) in
  let lines rows = String.concat "\n" rows ^ "\n" in
  let huge sign = Printf.sprintf "<%shuge integer: more than 100 digits omitted>" sign in
  let contains text needle =
    let n = String.length needle in
    let rec from i = i + n <= String.length text && (String.sub text i n = needle || from (i + 1)) in
    from 0 in
  (* bit-vector values: encoded two's complement, negative or out of range as reflected, wide, beyond the digit limit *)
  expect "minimum signed value, as encoded" (text (bv_numeral 8 (z 128))) "holds((_ bv128 8))";
  expect "negative value is not re-encoded" (text (bv_numeral 8 (z (-1)))) "holds((_ bv-1 8))";
  expect "value beyond the width is not reduced" (text (bv_numeral 8 (z 256))) "holds((_ bv256 8))";
  expect "zero width" (text (bv_numeral 0 Z.zero)) "holds((_ bv0 0))";
  let ones_256 = Z.pred (Z.shift_left Z.one 256) in
  expect "256-bit all ones" (text (bv_numeral 256 ones_256)) ("holds((_ bv" ^ Z.to_string ones_256 ^ " 256))");
  expect "value of 100 digits" (text (bv_numeral 333 (Z.pow (z 10) 99)))
    ("holds((_ bv1" ^ String.make 99 '0' ^ " 333))");
  expect "value of 101 digits" (text (bv_numeral 333 (Z.pow (z 10) 100))) ("holds((_ bv" ^ huge "+" ^ " 333))");
  expect "512-bit value beyond the digit limit" (text (bv_numeral 512 (Z.shift_left Z.one 511)))
    ("holds((_ bv" ^ huge "+" ^ " 512))");
  expect "negative 512-bit value beyond the digit limit"
    (text (bv_numeral 512 (Z.neg (Z.shift_left Z.one 511)))) ("holds((_ bv" ^ huge "-" ^ " 512))");
  expect "width beyond the digit limit"
    (text (constant ~interp:Z3BvLemma.op_numeral ~params:[Z.pow (z 10) 150; z 5] "bv" (base "BV0")))
    ("holds((_ bv5 " ^ huge "+" ^ "))");
  (* wide extractions: widths and bounds are shown as reflected, even beyond a machine word, with the range they give *)
  let bv256 = base "BV256" and bv128 = base "BV128" and bv101 = base "BV101" in
  let extract params domain range = declaration ~interp:Z3BvLemma.op_extract ~params "extract" [domain] range in
  expect "wide extraction" (text (A.App (extract [z 256; z 200; z 100] bv256 bv101, [A.Var (z 0, bv256)])))
    "holds((extract[256,200,100]:BV101 #0:BV256))";
  expect "extraction of a wide numeral"
    (text (A.App (extract [z 256; z 255; z 128] bv256 bv128, [bv_numeral 256 ones_256])))
    ("holds((extract[256,255,128]:BV128 (_ bv" ^ Z.to_string ones_256 ^ " 256)))");
  expect "extraction bound beyond a machine word"
    (text (A.App (extract [z 256; Z.of_string "18446744073709551621"; z 100] bv256 bv101, [A.Var (z 0, bv256)])))
    "holds((extract[256,18446744073709551621,100]:BV101 #0:BV256))";
  (* declaration identities: only "decl!DIGITS:NAME" (at most 20 digits) is a native identity; any other name is kept quoted, with no id *)
  List.iter (fun (name, shown) ->
      expect ("declaration " ^ String.escaped name) (text (constant name int_sort)) ("holds(" ^ shown ^ ":Int)"))
    ["decl!", "decl!#-"; "decl!:x", "|decl!:x|#-"; "decl!abc:x", "|decl!abc:x|#-"; "decl!12", "decl!12#-";
     "decl!12:", "||#12"; "decl!7:f:g", "|f:g|#7"; "decl!7:decl!8:x", "|decl!8:x|#7"; "decl!007:x", "x#007";
     "Decl!3:x", "|Decl!3:x|#-"; "sort!3:x", "|sort!3:x|#-"; "decl!\xd9\xa3:x", "|decl!\xd9\xa3:x|#-";
     "decl!12345678901234567890:x", "x#12345678901234567890";
     "decl!123456789012345678901:x", "|decl!123456789012345678901:x|#-"];
  expect "interpreted head whose name looks like a native identity"
    (text (constant ~interp:(z 999) "decl!3:x" bool_sort)) "holds(|decl!3:x|)";
  let p = constant "decl!1:p" bool_sort and q = constant "decl!2:q" bool_sort in
  expect "uninterpreted function named like a connective, without a native id"
    (text (A.App (declaration "and" [bool_sort; bool_sort] bool_sort, [p; q])))
    "holds((and#-:Bool p#1:Bool q#2:Bool))";
  expect "uninterpreted function named like a connective, with a native id"
    (text (A.App (declaration "decl!5:and" [bool_sort; bool_sort] bool_sort, [p; q])))
    "holds((and#5:Bool p#1:Bool q#2:Bool))";
  (* sort identities follow the same rule with "sort!DIGITS:NAME" *)
  List.iter (fun (name, shown) ->
      expect ("sort " ^ String.escaped name) (text (A.Var (z 0, base name))) ("holds(#0:" ^ shown ^ ")"))
    ["sort!", "sort!"; "sort!:T", "|sort!:T|"; "sort!x:T", "|sort!x:T|"; "sort!5", "sort!5"; "sort!5:", "||#5";
     "sort!5:two words", "|two words|#5"; "sort!4:Int", "Int#4"; "sort!8:Bool", "Bool#8";
     "Sort!5:T", "|Sort!5:T|"; "decl!5:T", "|decl!5:T|"];
  expect "array sort over malformed and native sorts"
    (text (A.Var (z 0, A.ArraySort ([base "sort!x:T"; int_sort], base "sort!6:U"))))
    "holds(#0:(Array |sort!x:T| Int U#6))";
  (* The range of an interpreted head is printed after ':' unless it is Bool (connectives and predicates: an interpreted head without a
     range is Bool) or the sort of its first argument, which that argument prints: so the sort of an expression is always printed or
     follows from what is printed. A constant array needs it most: its domain sorts occur nowhere in its arguments, so without the
     range arrays over different domains read the same. *)
  let real_sort = base "Real" in
  let zero = constant ~interp:Z3ValueTheory.op_num_rational ~params:[Z.zero; Z.one] "numeral" int_sort in
  let truth = constant ~interp:Z3ValueTheory.op_true "true" bool_sort in
  let const_array domains element value =
    A.App (declaration ~interp:Z3ValueTheory.op_const_array "const" [element] (A.ArraySort (domains, element)), [value]) in
  let over_int = text (const_array [int_sort] int_sort zero) and over_real = text (const_array [real_sort] int_sort zero) in
  expect "constant array over Int" over_int "holds((const:(Array Int Int) 0))";
  expect "constant array over Real" over_real "holds((const:(Array Real Int) 0))";
  require (over_int <> over_real) "constant arrays over different domains read the same";
  expect "constant array over two domains" (text (const_array [int_sort; real_sort] bool_sort truth))
    "holds((const:(Array Int Real Bool) true))";
  expect "constant array of constant arrays"
    (text (const_array [int_sort] (A.ArraySort ([real_sort], bool_sort)) (const_array [real_sort] bool_sort truth)))
    "holds((const:(Array Int (Array Real Bool)) (const:(Array Real Bool) true)))";
  let arrays = A.ArraySort ([int_sort], int_sort) in
  let store_of array_argument =
    A.App (declaration ~interp:Z3ValueTheory.op_store "store" [arrays; int_sort; int_sort] arrays, [array_argument; zero; zero]) in
  expect "store takes the sort of its array argument" (text (store_of (A.Var (z 0, arrays)))) "holds((store #0:(Array Int Int) 0 0))";
  expect "store of a constant array" (text (store_of (const_array [int_sort] int_sort zero)))
    "holds((store (const:(Array Int Int) 0) 0 0))";
  expect "select shows its element sort"
    (text (A.App (declaration ~interp:Z3ValueTheory.op_select "select" [arrays; int_sort] int_sort, [A.Var (z 0, arrays); zero])))
    "holds((select:Int #0:(Array Int Int) 0))";
  (* operators that keep the sort of their first argument, predicates, and operators that change the sort *)
  let x_real = A.Var (z 1, real_sort) and y_int = A.Var (z 2, int_sort) and c_bool = A.Var (z 3, bool_sort) in
  let five_real = constant ~interp:Z3ValueTheory.op_num_rational ~params:[z 5; Z.one] "numeral" real_sort in
  let operator ?(params = []) name op domain range args = A.App (declaration ~interp:op ~params name domain range, args) in
  expect "sum keeps the sort of its first argument"
    (text (operator "+" Z3ValueTheory.op_arith_add [real_sort; real_sort] real_sort [x_real; five_real])) "holds((+ #1:Real 5:Real))";
  expect "sum of integers"
    (text (operator "+" Z3ValueTheory.op_arith_add [int_sort; int_sort] int_sort [zero; y_int])) "holds((+ 0 #2:Int))";
  expect "conversion to Real shows its range"
    (text (operator "to_real" Z3ValueTheory.op_to_real [int_sort] real_sort [y_int])) "holds((to_real:Real #2:Int))";
  expect "comparison is Bool"
    (text (operator "<=" Z3ValueTheory.op_arith_le [real_sort; real_sort] bool_sort [x_real; five_real])) "holds((<= #1:Real 5:Real))";
  expect "conditional over integers"
    (text (operator "ite" Z3ValueTheory.op_ite [bool_sort; int_sort; int_sort] int_sort [c_bool; zero; y_int]))
    "holds((ite:Int #3:Bool 0 #2:Int))";
  expect "conditional over Bool"
    (text (operator "ite" Z3ValueTheory.op_ite [bool_sort; bool_sort; bool_sort] bool_sort [c_bool; p; q]))
    "holds((ite #3:Bool p#1:Bool q#2:Bool))";
  let bv8 = base "BV8" and bv24 = base "BV24" and bv32 = base "BV32" in
  expect "bit-vector sum keeps the sort of its first argument"
    (text (operator ~params:[z 32] "bvadd" Z3BvLemma.op_add [bv32; bv32] bv32 [A.Var (z 0, bv32); A.Var (z 1, bv32)]))
    "holds((bvadd[32] #0:BV32 #1:BV32))";
  expect "concatenation shows its width"
    (text (operator ~params:[z 24; z 8] "concat" Z3BvLemma.op_concat [bv24; bv8] bv32 [A.Var (z 0, bv24); A.Var (z 1, bv8)]))
    "holds((concat[24,8]:BV32 #0:BV24 #1:BV8))";
  expect "zero extension shows its width"
    (text (operator ~params:[z 8; z 24] "zero_extend" Z3BvLemma.op_zero_extend [bv8] bv32 [A.Var (z 0, bv8)]))
    "holds((zero_extend[8,24]:BV32 #0:BV8))";
  let t5 = base "sort!5:T" and t6 = base "sort!6:T" in
  expect "unknown interpreted head over one user sort"
    (text (operator "weird" (z 999) [t5] t5 [constant "decl!6:t" t5])) "holds((weird t#6:T#5))";
  expect "unknown interpreted head between two user sorts of one name"
    (text (operator "weird" (z 999) [t6] t5 [constant "decl!6:t" t6])) "holds((weird:T#5 t#6:T#6))";
  expect "unknown interpreted constant" (text (constant ~interp:(z 999) "weird" int_sort)) "holds(weird:Int)";
  expect "unknown interpreted array constant" (text (constant ~interp:(z 999) "weird" arrays)) "holds(weird:(Array Int Int))";
  expect "a user sort named Bool is not Bool" (text (constant ~interp:(z 999) "weird" (base "sort!8:Bool"))) "holds(weird:Bool#8)";
  (* where the argument is cut by the depth limit the sort is printed; so are sorts too deep or too wide to be compared *)
  let sum = ref x_real in
  for _ = 1 to 100 do sum := operator "+" Z3ValueTheory.op_arith_add [real_sort; real_sort] real_sort [!sum; x_real] done;
  let rendered, cut = R.judgment_text (U.Holds !sum) in
  require (cut && String.starts_with ~prefix:"holds((+ (+ (+ " rendered && contains rendered "(+:Real <...depth> <...depth>)")
    "a cut argument left the sum without its sort";
  let nested_sort n = let s = ref bool_sort in for _ = 1 to n do s := A.ArraySort ([int_sort], !s) done; !s in
  let store_over sort_value =
    A.App (declaration ~interp:Z3ValueTheory.op_store "store" [sort_value] sort_value, [A.Var (z 0, sort_value)]) in
  expect "store over a moderately nested sort" (let s = nested_sort 3 in text (store_over s))
    "holds((store #0:(Array Int (Array Int (Array Int Bool)))))";
  let rendered, cut = R.judgment_text (U.Holds (store_over (nested_sort 100))) in
  require (cut && String.starts_with ~prefix:"holds((store:(Array Int (Array Int " rendered && contains rendered "<...depth>")
    "sorts nested beyond the limit were compared";
  let rec shared n = if n = 0 then int_sort else (let s = shared (n - 1) in A.ArraySort ([s; s], bool_sort)) in
  let started = Sys.time () in
  let rendered, cut = R.judgment_text (U.Holds (store_over (shared 40))) in
  require (Sys.time () -. started < 5.0) "sorts sharing their parts were compared without a budget";
  require (cut && String.starts_with ~prefix:"holds((store:(Array " rendered) "sorts sharing their parts were compared";
  let nested = ref bool_sort in
  for _ = 1 to 100 do nested := A.ArraySort ([int_sort], !nested) done;
  let rendered, cut =
    R.judgment_text (U.Holds (A.App (declaration ~interp:Z3ValueTheory.op_const_array "const" [bool_sort] !nested, [truth]))) in
  require (cut && String.length rendered < 700 && String.starts_with ~prefix:"holds((const:(Array Int (Array Int " rendered)
    "a deeply nested array range was not cut with a marker";
  (* chains of heads: an omitted range follows from what is printed; what is cut, not compared or does not print its own sort keeps it *)
  let over_bv = text (const_array [bv8] int_sort zero) in
  expect "constant array over a bit-vector domain" over_bv "holds((const:(Array BV8 Int) 0))";
  require (over_bv <> over_int && over_bv <> over_real) "constant arrays over Int, Real and bit-vector domains read alike";
  let numeral_of range n = constant ~interp:Z3ValueTheory.op_num_rational ~params:[z n; Z.one] "numeral" range in
  expect "integral Real numeral under a sum"
    (text (operator "+" Z3ValueTheory.op_arith_add [real_sort; real_sort] real_sort [numeral_of real_sort 2; x_real]))
    "holds((+ 2:Real #1:Real))";
  expect "integer literal under a sum"
    (text (operator "+" Z3ValueTheory.op_arith_add [int_sort; int_sort] int_sort [numeral_of int_sort 2; y_int]))
    "holds((+ 2 #2:Int))";
  expect "select of a store of a constant array"
    (text (A.App (declaration ~interp:Z3ValueTheory.op_select "select" [arrays; int_sort] int_sort,
                  [store_of (const_array [int_sort] int_sort zero); zero])))
    "holds((select:Int (store (const:(Array Int Int) 0) 0 0) 0))";
  let ite_int a b = operator "ite" Z3ValueTheory.op_ite [bool_sort; int_sort; int_sort] int_sort [c_bool; a; b] in
  expect "nested conditionals" (text (ite_int (ite_int zero y_int) y_int))
    "holds((ite:Int #3:Bool (ite:Int #3:Bool 0 #2:Int) #2:Int))";
  expect "a lambda argument does not print its sort"
    (text (store_of (A.Quantifier (A.Lambda_k, [int_sort], arrays, A.Var (z 0, int_sort)))))
    "holds((store:(Array Int Int) (lambda [Int] #0:Int) 0 0))";
  let int_sum = ref y_int in
  for _ = 1 to 100 do int_sum := operator "+" Z3ValueTheory.op_arith_add [int_sort; int_sort] int_sort [!int_sum; y_int] done;
  let rendered, cut = R.judgment_text (U.Holds (operator "to_real" Z3ValueTheory.op_to_real [int_sort] real_sort [!int_sum])) in
  require (cut && String.starts_with ~prefix:"holds((to_real:Real (+ (+ " rendered && contains rendered "(+:Int <...depth> <...depth>)")
    "a conversion of a cut sum lost a sort";
  let real_sum = operator "+" Z3ValueTheory.op_arith_add [real_sort; real_sort] real_sort [x_real; x_real] in
  let node_limited fillers =
    R.judgment_text (U.Holds (A.App (declaration "decl!8:h" [] int_sort, List.init fillers (fun _ -> zero) @ [real_sum]))) in
  let rendered, cut = node_limited 998 in
  require (cut && contains rendered "(+:Real <...nodes>") "a head whose argument is cut at the node limit lost its sort";
  let rendered, cut = node_limited 997 in
  require (cut && contains rendered "(+ #1:Real <...nodes>") "a head whose first argument is printed printed a range";
  let long_sort n = base (String.make n 'S') in
  let rendered = text (store_over (long_sort 5000)) in
  require (String.starts_with ~prefix:"holds((store:|S" rendered && contains rendered "<4904 more bytes>")
    "sort names beyond the comparison limit were compared";
  require (String.starts_with ~prefix:"holds((store #0:|S" (text (store_over (long_sort 100))))
    "equal sort names of 100 bytes were not recognized";
  let rendered, cut =
    R.judgment_text (U.Holds (operator "+" Z3ValueTheory.op_arith_add [real_sort; real_sort] real_sort (x_real :: List.init 3000 (fun _ -> x_real)))) in
  require (cut && String.starts_with ~prefix:"holds((+ #1:Real #1:Real" rendered && String.ends_with ~suffix:"<...chars>" rendered)
    "output clipping hid where the text ends";
  (* the report: premise limit, other stages, accepted proofs and huge counts *)
  let five = constant ~interp:Z3ValueTheory.op_num_rational ~params:[z 5; Z.one] "numeral" int_sort in
  let x = constant "decl!3:x" int_sort in
  let conclusion = A.App (declaration ~interp:Z3ValueTheory.op_eq "=" [int_sort; int_sort] bool_sort, [x; five]) in
  let ids = List.init 10 (fun i -> z (100 + i)) in
  let leaf = { P.rule = U.Unverified "th-lemma"; formula = conclusion; premise_ids = ids } in
  let doc = { P.declarations = []; expressions = []; assertions = []; entries = [leaf]; root = Z.zero } in
  let obligation ?(premises = []) count =
    { P.obligation_index = Z.zero; obligation_rule = leaf.P.rule; obligation_conclusion = U.Holds conclusion;
      obligation_premises = premises; obligation_source = conclusion; obligation_count = count } in
  let premises = List.init 10 (fun i -> if i mod 2 = 0 then U.Holds p else U.Equal (x, x)) in
  expect "premise limit"
    (R.report_text 1 "PARTIAL 1" doc (P.DocumentChecked (Z.one, [obligation ~premises Z.one])))
    (lines ["readable\tquery=1\tverdict=PARTIAL 1\tpending=1\tfamilies=1\tshown=1";
            "readable\tfamily=1/1\trule=th-lemma\tcount=1\tmembers=1\tnode=0\tnode-pending=1";
            "  node 0: premises: #100 #101 #102 #103 #104 #105 #106 #107 ...<2 more>";
            "  premise #100: holds(p#1:Bool)"; "  premise #101: equal(x#3:Int, x#3:Int)";
            "  premise #102: holds(p#1:Bool)"; "  premise #103: equal(x#3:Int, x#3:Int)";
            "  premise #104: holds(p#1:Bool)"; "  premise #105: equal(x#3:Int, x#3:Int)";
            "  premise #106: holds(p#1:Bool)"; "  premise #107: equal(x#3:Int, x#3:Int)";
            "  ...<2 more premises omitted>";
            "  conclusion: holds((= x#3:Int 5))"; "  source formula: same as conclusion";
            "readable\tend\tquery=1"]);
  expect "missing-premise rejection names the node and its premise ids"
    (R.report_text 8 "REJECT" doc (P.DocumentRejected (P.MissingPremise, Some Z.zero, None)))
    (lines ["readable\tquery=8\tverdict=REJECT\tstage=missing-premise\tindex=0";
            "  node 0: rule=th-lemma premises: #100 #101 #102 #103 #104 #105 #106 #107 ...<2 more>";
            "  source formula: none reported"; "readable\tend\tquery=8"]);
  expect "entry rejection without an index"
    (R.report_text 9 "REJECT" doc (P.DocumentRejected (P.ProofEntry, None, None)))
    (lines ["readable\tquery=9\tverdict=REJECT\tstage=proof-entry\tindex=-"; "  source formula: none reported";
            "readable\tend\tquery=9"]);
  expect "accepted proof" (R.report_text 2 "ACCEPT" doc (P.DocumentChecked (Z.zero, [])))
    (lines ["readable\tquery=2\tverdict=ACCEPT\tpending=0\tfamilies=0\tshown=0"; "readable\tend\tquery=2"]);
  let bare = { doc with P.entries = [{ leaf with P.premise_ids = [] }] } in
  let big = Z.pow (z 10) 200 in
  expect "huge counts"
    (R.report_text 1 "PARTIAL" bare (P.DocumentChecked (big, [obligation big])))
    (lines ["readable\tquery=1\tverdict=PARTIAL\tpending=" ^ huge "+" ^ "\tfamilies=1\tshown=1";
            "readable\tfamily=1/1\trule=th-lemma\tcount=" ^ huge "+" ^ "\tmembers=1\tnode=0\tnode-pending=" ^ huge "+";
            "  node 0: premises: none"; "  conclusion: holds((= x#3:Int 5))"; "  source formula: same as conclusion";
            "readable\tend\tquery=1"])

let identity_and_binders () =
  let c = context () in
  let inputs = parse c
      "(declare-sort U 0)(declare-fun f (U) U)\
       (assert (forall ((x U)) (= (f x) x)))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.Quantifier (A.Forall_k, [_], s, _) ->
       require (s = A.bool_sort) "quantifier result sort changed"
   | _ -> failwith "quantifier was not marshaled");
  let st = B.marshal_expressions (B.empty_state ())
      (parse c "(assert (= ((_ extract 3 0) #x12) ((_ extract 7 4) #x12)))") in
  let extracts = List.filter (fun d -> d.A.interp = Some Z3BvLemma.op_extract)
      st.all_declarations in
  require (List.sort compare (List.map (fun d -> d.A.int_params) extracts) =
      List.map (List.map Z.of_int) [[8; 3; 0]; [8; 7; 4]])
    "native extraction widths or indices were lost";
  let st = B.marshal_expressions (B.empty_state ())
      (parse c "(assert (= ((_ rotate_left 1) #x12) ((_ rotate_left 2) #x12)))") in
  let opaque = List.filter (fun d -> d.A.interp = None && d.domain <> [])
      st.all_declarations in
  require (List.length opaque = 2) "parameterized declarations were merged";
  require ((List.nth opaque 0).decl_name <> (List.nth opaque 1).decl_name)
    "opaque declaration identity was lost"

let checked_binder_proofs () =
  let sources = [
    "(assert (not (forall ((x Int)) (= (+ x 0) x))))";
    "(declare-fun p (Int) Bool)\
     (assert (not (forall ((x Int)) (or (p (+ x 0)) (not (p x))))))";
    "(assert (exists ((x Int)) (not (= (+ x 0) x))))";
    "(assert (not (forall ((x Int)) (forall ((y Real))\
       (and (= (+ x 0) x) (= (+ y 0.0) y))))))"
  ] in
  List.iter (fun source ->
      let doc = document source in
      require (List.exists (fun e -> match e.P.rule with
          | U.QuantifierIntroduction _ -> true | _ -> false) doc.entries)
        "native quantified regression did not exercise a binder";
      require (P.check_document doc = Some Z.zero)
        ("quantified rewriting was not certified: " ^ source)) sources;
  let doc = document (List.hd sources) in
  let entry = List.find (fun e -> match e.P.rule with
      | U.QuantifierIntroduction _ -> true | _ -> false) doc.entries in
  let certificate = match entry.P.rule with
    | U.QuantifierIntroduction certificate -> certificate
    | _ -> assert false in
  let conclusion = Option.get (U.classify_fact entry.P.formula) in
  require (U.check_binder certificate conclusion) "valid hidden proof DAG was rejected";
  let fail certificate message =
    require (not (U.check_binder certificate conclusion)) message in
  fail { certificate with U.binder_root = Z.minus_one } "negative binder root was trusted";
  fail { certificate with U.binder_root = Z.of_int 1000000 } "missing binder root was trusted";
  fail { certificate with U.binder_entries = List.rev certificate.U.binder_entries }
    "forward binder premises were trusted";
  List.iter (fun name ->
      fail { certificate with U.binder_entries =
          List.map (fun e -> if e.U.binder_premises = [] then
              { e with U.binder_name = name } else e) certificate.U.binder_entries }
        ("binder generalized an unsupported leaf: " ^ name))
    ["asserted"; "hypothesis"; "unknown"; "assumed:nlsat"];
  fail { certificate with U.binder_entries =
      List.map (fun e -> if e.U.binder_name = "quant-intro" then
          { e with U.binder_sorts = Some [A.BaseSort "Real"] } else e)
        certificate.U.binder_entries }
    "binder generalized across mismatched bound sorts";
  fail { certificate with U.binder_entries =
      List.map (fun e -> if e.U.binder_premises <> [] then
          { e with U.binder_premises = [Z.minus_one] } else e)
        certificate.U.binder_entries }
    "binder ignored an invalid premise";
  let entries = List.map (fun e -> match e.P.rule with
      | U.QuantifierIntroduction _ ->
          { e with P.rule = U.QuantifierIntroduction
              { certificate with U.binder_entries = [] } }
      | _ -> e) doc.entries in
  require (match P.check_document { doc with entries } with
      | Some pending -> Z.sign pending > 0 | None -> false)
    "unsupported binder proof was certified instead of retaining an obligation";
  let lambda_doc = document
      "(assert (not (= (lambda ((x Int)) (+ x 0)) (lambda ((y Int)) y))))" in
  require (List.exists (fun e ->
      match e.P.rule, U.classify_fact e.P.formula with
      | U.QuantifierIntroduction cert,
        Some (U.Equal (A.Quantifier (A.Lambda_k, _, _, _), _) as conclusion) ->
          U.check_binder cert conclusion
      | _ -> false) lambda_doc.entries)
    "term-valued lambda congruence was not checked";
  let c = context () in
  let inputs = parse c
      "(declare-const a Int)(declare-const b Int)(declare-fun p (Int) Bool)\
       (assert (= a b))(assert (= (p a) (p b)))\
       (assert (= (forall ((x Int)) (p a)) (forall ((x Int)) (p b))))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  let forms = List.map (B.cached_expression st) inputs in
  let input = Option.get (U.classify_fact (List.nth forms 0)) in
  let conclusion = Option.get (U.classify_fact (List.nth forms 2)) in
  let certificate = {
    U.binder_entries = [
      { U.binder_name = "asserted"; binder_formula = List.nth forms 0;
        binder_premises = []; binder_sorts = None };
      { U.binder_name = "monotonicity"; binder_formula = List.nth forms 1;
        binder_premises = [Z.zero]; binder_sorts = None };
      { U.binder_name = "quant-intro"; binder_formula = List.nth forms 2;
        binder_premises = [Z.one]; binder_sorts = Some [A.BaseSort "Int"] }
    ]; binder_root = Z.of_int 2 } in
  require (U.check_binder_with_inputs [input] certificate conclusion)
    "closed original input was not available inside a binder proof";
  require (not (U.check_binder certificate conclusion) &&
           not (U.check_binder_with_inputs [] certificate conclusion))
    "binder input dependency disappeared";
  require (not (U.check_binder_with_inputs [conclusion] certificate conclusion))
    "unrelated input authorized a hidden assertion";
  let open_formula = Z3ResolutionProofTheory.mk_eq_expr
      (A.Var (Z.zero, A.BaseSort "Int")) (A.Var (Z.one, A.BaseSort "Int")) in
  let open_fact = Option.get (U.classify_fact open_formula) in
  let leaf = { U.binder_name = "asserted"; binder_formula = open_formula;
               binder_premises = []; binder_sorts = None } in
  require (not (U.binder_step_with_inputs [open_fact] leaf open_fact []))
    "open assertion was generalized across binder environments";
  let node = { U.kind = U.QuantifierIntroduction certificate;
               conclusion = conclusion; premises = [] } in
  require (match U.check_node_with_inputs true [input] node with
      | Some (_, pending) -> Z.equal pending Z.zero | None -> false)
    "input-aware binder certificate was not integrated in the node checker";
  (* Scope guard: binder entries are checked at the scopes the root uses them. *)
  let int_s = A.BaseSort "Int" and bool_s = A.bool_sort in
  let all bs b = A.Quantifier (A.Forall_k, bs, bool_s, b) in
  let eqe = Z3ResolutionProofTheory.mk_eq_expr in
  let tt = Z3ResolutionProofTheory.true_expr in
  let entry name formula premises sorts =
    { U.binder_name = name; binder_formula = formula;
      binder_premises = List.map Z.of_int premises; binder_sorts = sorts } in
  let pending entries root concl =
    match U.check_node_with_inputs true []
            { U.kind = U.QuantifierIntroduction
                { U.binder_entries = entries; binder_root = Z.of_int root };
              conclusion = concl; premises = [] } with
    | Some (_, p) -> Z.to_int p | None -> -1 in
  let refl_true = entry "refl" (eqe tt tt) [] None in
  let p0 = A.Var (Z.zero, bool_s) and x0 = A.Var (Z.zero, int_s) in
  let taut a = A.App (Z3CanonicalOps.or_decl (Z.of_int 2), [a; Z3ResolutionProofTheory.mk_not_expr a]) in
  (* forall x:Int. (or p (not p)) = forall x:Int. true with p = Var 0 : Bool is false
     in the standard model; the Boolean wrapper used to certify it. *)
  let ill = all [int_s] (taut p0) and top = all [int_s] tt in
  require (pending [refl_true; entry "quant-intro" (eqe ill top) [0] (Some [int_s])] 1
             (U.Equal (ill, top)) = 1)
    "ill-scoped binder certificate was certified";
  (* A closed, well-scoped root over an ill-scoped inner rewrite. *)
  let ok = all [int_s] (taut (eqe x0 x0)) in
  require (pending [entry "rewrite" (eqe (taut p0) tt) [] None;
                    entry "quant-intro" (eqe ok top) [0] (Some [int_s])] 1 (U.Equal (ok, top)) = 1)
    "ill-scoped inner binder entry was certified";
  (* The same open body, well scoped, stays certified. *)
  require (pending [entry "refl" (eqe (taut (eqe x0 x0)) (taut (eqe x0 x0))) [] None;
                    entry "quant-intro" (eqe ok ok) [0] (Some [int_s])] 1 (U.Equal (ok, ok)) = 0)
    "well-scoped open binder body was rejected";
  (* Bounds: 1024 binders pass, 1025 fail; a shared diamond needing 2^40 scopes fails fast. *)
  let wide n = let bs = List.init n (fun _ -> int_s) in all bs tt in
  let wide_cert n = [refl_true; entry "quant-intro" (eqe (wide n) (wide n)) [0]
                                  (Some (List.init n (fun _ -> int_s)))] in
  require (pending (wide_cert 1024) 1 (U.Equal (wide 1024, wide 1024)) = 0)
    "binder scope at the length limit was rejected";
  require (pending (wide_cert 1025) 1 (U.Equal (wide 1025, wide 1025)) = 1)
    "binder scope over the length limit was accepted";
  let diamond levels =
    let q s p = entry "quant-intro" (eqe (all [s] tt) (all [s] tt)) [p] (Some [s]) in
    let join l r = entry "monotonicity" (eqe tt tt) [l; r] None in
    let rec go i acc = if i > levels then List.rev acc
      else let a = 3 * (i - 1) in go (i + 1) (join (a + 1) (a + 2) :: q bool_s a :: q int_s a :: acc) in
    go 1 [refl_true] in
  require (pending (diamond 6) 18 (U.Equal (tt, tt)) = 0)
    "shared binder proof at the per-entry scope limit was rejected";
  let t0 = Unix.gettimeofday () in
  require (pending (diamond 40) 120 (U.Equal (tt, tt)) = 1)
    "exponential shared binder proof was accepted";
  require (Unix.gettimeofday () -. t0 < 5.0) "exponential shared binder proof was not cut off";
  (* Sort names are charged by U.name_length, which equals FStar.String.strlen,
     before they are compared. It counts FStar.String.list_of_string, which the
     runtime decodes like the Cherry runtime: code points on valid UTF-8, and at
     least a quarter of the bytes on any byte string. *)
  List.iter (fun (s, n) ->
      require (Z.equal (FStar_String.strlen s) (Z.of_int n))
        ("runtime strlen disagrees with the Cherry runtime: " ^ String.escaped s);
      require (Z.equal (U.name_length s) (Z.of_int n))
        ("guard name length disagrees with strlen: " ^ String.escaped s))
    ["", 0; "Int", 3; "\xC3\xA9", 1; "\xE2\x82\xAC", 1; "\xF0\x9F\x98\x80", 1; "e\xCC\x81", 2;
     "\x80\x80\x80\x80\x80\x80\x80\x80", 4; "\xC3", 1; "a\xE2\x82", 2; "\xFF\xFE", 1;
     "\xC0\x80", 1; "\xED\xA0\x80", 1];
  (* Decoded characters: scalar boundaries and malformed sequences (U+FFFD). *)
  List.iter (fun (s, cs) ->
      require (FStar_String.list_of_string s = cs)
        ("runtime list_of_string decodes unexpectedly: " ^ String.escaped s))
    ["a\xC3\xA9\xE2\x82\xAC\xF0\x9F\x98\x80", [0x61; 0xE9; 0x20AC; 0x1F600];
     "\xED\x9F\xBE\xED\x9F\xBF\xEE\x80\x80\xF4\x8F\xBF\xBF", [0xD7FE; 0xD7FF; 0xE000; 0x10FFFF];
     "\xED\xA0\x80\xED\xBF\xBF\xF4\x90\x80\x80", [0xFFFD; 0xFFFD; 0xFFFD];
     "\x80\x80\xC0\x80\xF5\x80\x80\x80", [0xFFFD; 0xFFFD; 0xFFFD];
     "\xE0\x80\x80", [0]; "a\xF0\x9F\x98", [0x61; 0xFFFD]];
  let named len c =
    let s = A.BaseSort (String.make len c) in
    let x = A.Var (Z.zero, s) in
    let q = all [s] (eqe x x) in
    pending [entry "refl" (eqe (eqe x x) (eqe x x)) [] None;
             entry "quant-intro" (eqe q q) [0] (Some [s])] 1 (U.Equal (q, q)) in
  require (named 1000 'S' = 0) "a binder sort with a 1000-character name was rejected";
  require (named 1_000_000 '\x80' = 1)
    "a long malformed sort name was compared without its length being charged";
  require (named 1_000_000 'S' = 1)
    "a long sort name was compared without its length being charged"

let checked_binder_definitions () =
  let c = context () in
  let parsed = parse c
      "(declare-fun f (Int) Bool)(declare-fun p (Int) Bool)\
       (assert (forall ((x Int)) (= (f x) (not (p x)))))\
       (assert (forall ((x Int)) (= (not (f x)) (not (f x)))))\
       (assert (= (not (forall ((x Int)) (f x)))\
                  (exists ((x Int)) (not (f x)))))\
       (assert (= (f 0) (p 0)))" in
  let st = B.marshal_expressions (B.empty_state ()) parsed in
  match List.map (B.cached_expression st) parsed with
  | A.Quantifier (_, _, _, A.App (_, [A.App (symbol, _); body])) ::
    A.Quantifier (_, _, _, leaf) :: formula :: input :: [] ->
      let defs = [{ Z3Definitions.symbol; variables = [Z.zero]; body }] in
      let certificate = { U.binder_entries = [
          { U.binder_name = "refl"; binder_formula = leaf;
            binder_premises = []; binder_sorts = None };
          { U.binder_name = "nnf-neg"; binder_formula = formula;
            binder_premises = [Z.zero]; binder_sorts = Some [A.BaseSort "Int"] }
        ]; binder_root = Z.one } in
      let entry = { P.rule = U.QuantifierIntroduction certificate;
                    formula; premise_ids = [] } in
      let checks entry inputs =
        match P.check_entry true true defs inputs Z3ProofIndex.Empty entry with
        | Some (_, pending) -> Z.equal pending Z.zero
        | None -> false in
      require (checks entry [])
        "NNF certificate did not expand definitions with its parent conclusion";
      let bad_leaf = { (List.hd certificate.U.binder_entries) with
        U.binder_formula = Z3ResolutionProofTheory.mk_eq_expr
          (A.Var (Z.zero, A.bool_sort)) Z3ResolutionProofTheory.true_expr } in
      let bad = { certificate with U.binder_entries =
        bad_leaf :: List.tl certificate.U.binder_entries } in
      require (not (checks { entry with P.rule = U.QuantifierIntroduction bad } []))
        "definition expansion bypassed an invalid hidden proof";
      let asserted = { U.binder_entries = [
          { U.binder_name = "asserted"; binder_formula = input;
            binder_premises = []; binder_sorts = None }
        ]; binder_root = Z.zero } in
      let entry = { P.rule = U.QuantifierIntroduction asserted;
                    formula = input; premise_ids = [] } in
      let expanded = Option.get (Z3Definitions.expand Z.one defs input) in
      let fact = Option.get (U.classify_fact expanded) in
      require (checks entry [fact])
        "expanded hidden assertion did not match its expanded original input";
      require (not (checks entry []))
        "definition expansion authorized a missing hidden assertion";
      let recursive = [{ Z3Definitions.symbol; variables = [Z.zero];
                         body = A.App (symbol, [A.Var (Z.zero, A.BaseSort "Int")]) }] in
      require (P.expand_rule recursive entry.P.rule = None)
        "failed hidden definition expansion was silently ignored"
  | _ -> failwith "unexpected binder-definition regression formulas"

let checked_quantifier_instances () =
  let sources = [
    "(declare-fun p (Int) Bool)(assert (forall ((x Int)) (p (+ x 0))))\
     (assert (not (p 3)))";
    "(declare-fun p (Int Real) Bool)\
     (assert (forall ((x Int) (y Real)) (! (p x y) :pattern ((p x y)))))\
     (assert (not (p 3 4.5)))";
    "(declare-fun p (Int) Bool)\
     (assert (forall ((x Int)) (or (p x) (not (p (+ x 1))))))\
     (assert (not (p 0)))(assert (p 1))"
  ] in
  List.iter (fun source ->
      let doc = document source in
      let instances = List.filter_map (fun e -> match e.P.rule with
          | U.QuantifierInstantiation args -> Some (args, e.P.formula) | _ -> None)
          doc.entries in
      require (instances <> []) "native proof omitted instantiation parameters";
      require (P.check_document doc = Some Z.zero)
        ("quantifier instance was not certified: " ^ source);
      List.iter (fun (args, formula) ->
          require (Z3QuantifierInstantiation.check args formula)
            "native quantifier substitution was not checked";
          require (not (Z3QuantifierInstantiation.check [] formula))
            "missing quantifier bindings were trusted";
          require (not (Z3QuantifierInstantiation.check (args @ args) formula))
            "extra quantifier bindings were trusted";
          require (not (Z3QuantifierInstantiation.check
              (List.map (fun a -> A.Var (Z.zero, A.get_sort a)) args) formula))
            "escaping substitution variables were trusted";
          (match formula with
           | A.App (f, [negative; _]) ->
               require (not (Z3QuantifierInstantiation.check args
                   (A.App (f, [negative; Z3ResolutionProofTheory.false_expr]))))
                 "an incorrect instantiated body was trusted"
           | _ -> failwith "unexpected instantiation clause");
          if List.length args > 1 then
            require (not (Z3QuantifierInstantiation.check (List.rev args) formula))
              "native binding order was ignored") instances;
      let entries = List.map (fun e -> match e.P.rule with
          | U.QuantifierInstantiation _ -> { e with P.rule = U.QuantifierInstantiation [] }
          | _ -> e) doc.entries in
      require (match P.check_document { doc with entries } with
          | Some pending -> Z.sign pending > 0 | None -> false)
        "invalid substitutions did not retain an explicit obligation") sources;
  let check_clause declarations clause arguments expected =
    let c = context () in
    let source = declarations ^ "(assert " ^ clause ^ ")" ^
      String.concat "" (List.map (fun term ->
          "(assert (= " ^ term ^ " " ^ term ^ "))") arguments) in
    let inputs = parse c source in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match List.map (B.cached_expression st) inputs with
    | formula :: bindings ->
        let args = List.map (function A.App (_, [term; _]) -> term
            | _ -> failwith "malformed test binding") bindings in
        require (Z3QuantifierInstantiation.check args formula = expected)
          ("incorrect nested quantifier substitution: " ^ source)
    | [] -> failwith "missing test instance"
  in
  let declarations = "(declare-fun p (Int Int) Bool)" in
  let quantified = "(not (forall ((x Int)) (exists ((y Int)) (p x y))))" in
  check_clause declarations
    ("(or " ^ quantified ^ " (exists ((y Int)) (p 0 y)))") ["0"] true;
  check_clause declarations
    ("(or " ^ quantified ^ " (exists ((y Int)) (p y 0)))") ["0"] false;
  check_clause declarations
    ("(or " ^ quantified ^ " (exists ((y Int)) (p 1 y)))") ["0"] false;
  check_clause declarations
    "(or (not (forall ((x Int)) (forall ((x Int)) (p x x))))\
         (forall ((x Int)) (p x x)))" ["0"] true;
  check_clause "(declare-fun q (Int Real Int Real Int) Bool)"
    "(or (not (forall ((x Int) (r Real))\
                (exists ((y Int) (s Real)) (forall ((z Int)) (q x r y s z)))))\
         (exists ((y Int) (s Real)) (forall ((z Int)) (q 3 4.5 y s z))))"
    ["3"; "4.5"] true;
  check_clause "(declare-fun q (Int Int Int) Bool)"
    "(or (not (forall ((x Int) (y Int)) (exists ((z Int)) (q x y z))))\
         (exists ((z Int)) (q 3 4 z)))" ["3"; "4"] true;
  check_clause "(declare-fun q (Int Int Int) Bool)"
    "(or (not (forall ((x Int) (y Int)) (exists ((z Int)) (q x y z))))\
         (exists ((z Int)) (q 4 3 z)))" ["3"; "4"] false;
  check_clause "(declare-fun p ((Array Int Int)) Bool)"
    "(or (not (forall ((x Int)) (p (lambda ((y Int)) (+ x y)))))\
         (p (lambda ((y Int)) (+ 3 y))))" ["3"] true;
  let c = context () in
  let inputs = parse c
      "(declare-fun p (Int Int) Bool)\
       (assert (or (not (forall ((x Int)) (exists ((y Int)) (p x y))))\
                   (exists ((y Int)) (p 0 y))))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  let formula = B.cached_expression st (List.hd inputs) in
  let zero = List.find (function
      | A.App (d, []) -> d.A.interp = Some Z3ValueTheory.op_num_rational &&
                        d.A.int_params = [Z.zero; Z.one]
      | _ -> false) st.all_expressions in
  require (Z3QuantifierInstantiation.check [zero] formula)
    "capture-avoiding substitution under an existential was rejected";
  let inputs = parse c
      "(declare-fun p (Int Int) Bool)\
       (assert (or (not (forall ((x Int)) (exists ((y Int)) (p x y))))\
                   (exists ((y Int)) (p y 0))))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  require (not (Z3QuantifierInstantiation.check [zero]
      (B.cached_expression st (List.hd inputs))))
    "nested substitution captured the inner bound variable"

let checked_negative_nnf () =
  let sources = [
    "(declare-fun p (Int) Bool)\
     (assert (not (exists ((x Int)) (p x))))(assert (p 0))";
    "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)\
     (assert (not (exists ((x Int)) (and (p x) (q x)))))\
     (assert (p 0))(assert (q 0))";
    "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)\
     (assert (not (exists ((x Int)) (or (p x) (q x)))))\
     (assert (p 0))";
    "(declare-fun p (Int Real) Bool)\
     (assert (not (exists ((x Int) (y Real)) (p x y))))\
     (assert (p 3 4.5))";
    "(declare-fun p (Int) Bool)(declare-const q Bool)\
     (assert (not (and (exists ((x Int)) (p x)) q)))\
     (assert (p 0))(assert q)";
    "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)\
     (assert (not (exists ((x Int)) (=> (p x) (q x)))))\
     (assert (not (p 0)))";
    "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)\
     (assert (not (exists ((x Int)) (xor (p x) (q x)))))\
     (assert (p 0))(assert (not (q 0)))";
    "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)(declare-fun r (Int) Bool)\
     (assert (not (exists ((x Int)) (ite (p x) (q x) (r x)))))\
     (assert (p 0))(assert (q 0))"
  ] in
  List.iter (fun source ->
      let doc = document source in
      require (P.check_document doc = Some Z.zero)
        ("negative NNF was not certified: " ^ source);
      require (List.exists (fun e -> match e.P.rule with
          | U.QuantifierIntroduction cert ->
              List.exists (fun e -> e.U.binder_name = "nnf-neg") cert.U.binder_entries
          | _ -> false) doc.entries) "native regression omitted negative NNF") sources;
  let doc = document (List.hd sources) in
  let entry = List.find (fun e -> match e.P.rule with
      | U.QuantifierIntroduction cert ->
          (List.nth cert.U.binder_entries (Z.to_int cert.U.binder_root)).U.binder_name = "nnf-neg"
      | _ -> false) doc.entries in
  let cert = match entry.P.rule with U.QuantifierIntroduction cert -> cert | _ -> assert false in
  let root = Z.to_int cert.U.binder_root in
  let original = List.nth cert.U.binder_entries root in
  let mutate changed message =
    let entries = List.mapi (fun index e -> if index = root then changed else e)
        cert.U.binder_entries in
    let mutated = { cert with U.binder_entries = entries } in
    let conclusion = Option.get (U.classify_fact changed.U.binder_formula) in
    require (not (U.check_binder mutated conclusion)) message
  in
  mutate { original with U.binder_name = "nnf-pos" } "negative NNF ignored its polarity";
  mutate { original with U.binder_sorts = Some [A.BaseSort "Real"] }
    "negative NNF ignored its binding sorts";
  mutate { original with U.binder_sorts = None } "negative NNF ignored a missing binder";
  mutate { original with U.binder_premises = [] } "negative NNF ignored its body proof";
  mutate { original with U.binder_premises = [Z.minus_one] }
    "negative NNF trusted a missing premise";
  (match original.U.binder_formula with
   | A.App (relation, [A.App (n, [A.Quantifier (kind, bs, _, body) as q]);
                       A.Quantifier (_, bs', s', target)]) ->
       let changed left right = { original with U.binder_formula = A.App (relation, [left; right]) } in
       mutate (changed (A.App (n, [q])) (A.Quantifier (kind, bs', s', target)))
         "negative NNF did not dualize its quantifier";
       mutate (changed q (A.Quantifier (Z3QuantifierNnf.dual kind, bs', s', target)))
         "negative NNF accepted a source without negation";
       mutate (changed (A.App (n, [q]))
           (A.Quantifier (Z3QuantifierNnf.dual kind, bs', s', body)))
         "negative NNF accepted an unnegated body";
       let conclusion = U.Equal (A.App (n, [q]),
           A.Quantifier (Z3QuantifierNnf.dual kind, bs', s', target)) in
       let negative_body = Z3ResolutionProofTheory.mk_not_expr body in
       require (not (U.binder_negative_quantifier_step bs conclusion
           [U.Observational (negative_body, target)]))
         "observational NNF premises silently established ordinary equality";
       require (U.binder_negative_quantifier_step bs
           (U.Observational (A.App (n, [q]),
               A.Quantifier (Z3QuantifierNnf.dual kind, bs', s', target)))
           [U.Equal (negative_body, target)])
         "negative NNF did not permit the equality-to-observation bridge"
   | _ -> failwith "unexpected native negative NNF conclusion");
  let entries = List.map (fun e ->
      if e.U.binder_premises = [] then { e with U.binder_name = "hypothesis" } else e)
      cert.U.binder_entries in
  require (not (U.check_binder { cert with U.binder_entries = entries }
      (Option.get (U.classify_fact entry.P.formula))))
    "negative NNF generalized a hypothesis";
  let c = context () in
  List.iter (fun (kind, dual) ->
      let inputs = parse c (Printf.sprintf
          "(declare-fun p_%s (Int) Bool)(declare-const q_%s Bool)\
           (assert (= (not (%s ((x Int)) (p_%s x)))\
                       (%s ((x Int)) (not (p_%s x)))))\
           (assert (= (not (and (%s ((x Int)) (p_%s x)) q_%s))\
                       (or (%s ((x Int)) (not (p_%s x))) (not q_%s))))\
           (assert (= (and (not (%s ((x Int)) (p_%s x))) q_%s)\
                       (and (%s ((x Int)) (not (p_%s x))) q_%s)))"
          kind kind kind kind dual kind kind kind kind dual kind kind
          kind kind kind dual kind kind) in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let formulas = List.map (B.cached_expression st) inputs in
      match formulas with
      | quantum :: negative :: positive :: [] ->
          let body = match quantum with
            | A.App (_, [_; A.Quantifier (_, _, _, body)]) -> body
            | _ -> failwith "unexpected synthetic quantifier duality" in
          let leaf = { U.binder_name = "refl";
                       binder_formula = Z3ResolutionProofTheory.mk_eq_expr body body;
                       binder_premises = []; binder_sorts = None } in
          let quantified = { U.binder_name = "nnf-neg"; binder_formula = quantum;
                             binder_premises = [Z.zero];
                             binder_sorts = Some [A.BaseSort "Int"] } in
          List.iter (fun (name, formula) ->
              let root = { U.binder_name = name; binder_formula = formula;
                           binder_premises = [Z.one]; binder_sorts = None } in
              let certificate = { U.binder_entries = [leaf; quantified; root];
                                  binder_root = Z.of_int 2 } in
              require (U.check_binder certificate (Option.get (U.classify_fact formula)))
                ("compositional NNF failed for " ^ kind ^ "/" ^ name);
              let bad = { leaf with U.binder_formula =
                  Z3ResolutionProofTheory.mk_eq_expr body Z3ResolutionProofTheory.true_expr } in
              require (not (U.check_binder { certificate with U.binder_entries = [bad; quantified; root] }
                  (Option.get (U.classify_fact formula))))
                "compositional NNF trusted an invalid body certificate")
            ["nnf-neg", negative; "nnf-pos", positive]
      | _ -> failwith "expected three synthetic NNF formulas")
    ["forall", "exists"; "exists", "forall"]

let checked_der_rules () =
  let declarations =
    "(declare-fun p (Int Int) Bool)(declare-fun f (Int) Int)\
     (declare-fun q (Int Real Int) Bool)(declare-fun b (Int Bool) Bool)" in
  let cases = [
    "exists", "(exists ((x Int)) (and (= x 3) (p x z)))", "(p 3 z)", true;
    "forall", "(forall ((x Int)) (or (not (= x z)) (p x z)))", "(p z z)", true;
    "reversed-equality", "(exists ((x Int)) (and (= z x) (p x z)))", "(p z z)", true;
    "mixed-sort-middle", "(exists ((x Int) (r Real) (y Int))\
       (and (= r 1.5) (q x r y)))",
       "(exists ((x Int) (y Int)) (q x 1.5 y))", true;
    "dependent-witness", "(forall ((x Int) (y Int))\
       (or (not (= x (f y))) (p x y)))",
       "(forall ((y Int)) (p (f y) y))", true;
    "alternative-witness", "(forall ((x Int) (y Int))\
       (or (not (= x (f y))) (not (= x z))))",
       "(forall ((y Int)) (not (= z (f y))))", true;
    "reordered-alternative-witness", "(forall ((x Int) (y Int))\
       (or (not (= x z)) (not (= x (f y)))))",
       "(forall ((y Int)) (not (= (f y) z)))", true;
    "wrong-alternative-witness", "(forall ((x Int) (y Int))\
       (or (not (= x (f y))) (not (= x z))))",
       "(forall ((y Int)) (not (= z (f z))))", false;
    "nested-binder", "(exists ((x Int))\
       (and (= x z) (forall ((y Int)) (p x y))))",
       "(forall ((y Int)) (p z y))", true;
    "boolean-literal", "(exists ((x Bool)) (and x (b z x)))", "(b z true)", true;
    "cyclic-witness", "(exists ((x Int)) (and (= x (f x)) (p x z)))",
       "(p (f z) z)", false;
    "missing-guard", "(exists ((x Int)) (p x z))", "(p 3 z)", false;
    "wrong-universal-polarity", "(forall ((x Int)) (and (= x 3) (p x z)))",
       "(p 3 z)", false;
    "captured-witness", "(exists ((x Int))\
       (and (= x z) (forall ((y Int)) (p x y))))",
       "(forall ((y Int)) (p y y))", false;
    "wrong-instance", "(exists ((x Int)) (and (= x 3) (p x z)))", "(p 4 z)", false
  ] in
  List.iter (fun (name, left, right, expected) ->
      let c = context () in
      let inputs = parse c (declarations ^
          "(assert (forall ((z Int)) (= " ^ left ^ " " ^ right ^ ")))" ^
          "(assert (= (forall ((z Int)) " ^ left ^ ") (forall ((z Int)) " ^ right ^ ")))") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let formula = match B.cached_expression st (List.hd inputs) with
        | A.Quantifier (_, _, _, body) -> body
        | _ -> failwith "missing DER ambient binder" in
      let conclusion = Option.get (U.classify_fact formula) in
      require (U.check_step U.DestructiveEqualityResolution conclusion [] = expected)
        ("incorrect DER decision: " ^ name);
      let certificate = { U.binder_entries = [
          { U.binder_name = "der"; binder_formula = formula;
            binder_premises = []; binder_sorts = None }];
          binder_root = Z.zero } in
      (* The open step is decided under the binder of `z`; alone, its root is not
         closed and stays an obligation. *)
      require (U.check_binder certificate conclusion = (expected && Z3Definitions.scoped [] formula))
        ("incorrect open hidden DER decision: " ^ name);
      let closed = B.cached_expression st (List.nth inputs 1) in
      let wrapped = { U.binder_entries = certificate.U.binder_entries @ [
          { U.binder_name = "quant-intro"; binder_formula = closed;
            binder_premises = [Z.zero]; binder_sorts = Some [A.BaseSort "Int"] }];
          binder_root = Z.one } in
      require (U.check_binder wrapped (Option.get (U.classify_fact closed)) = expected)
        ("incorrect hidden DER decision: " ^ name);
      if expected then
        require (not (U.check_step U.DestructiveEqualityResolution conclusion [conclusion]))
          "DER ignored an unexpected premise") cases

let checked_skolemization () =
  let module SK = Z3Skolemization in
  let check_indexed fixture =
    let reference = P.check_document fixture in
    let diagnostics = P.diagnose_document fixture in
    List.iter (fun hash ->
      require (P.check_document_indexed hash fixture = reference)
        "indexed checking changed the Skolem context";
      require (P.diagnose_document_indexed hash fixture = diagnostics)
        "indexed diagnostics changed the Skolem context")
      [(fun _ -> Z.zero); Z3NativeMain.assertion_hash] in
  let declarations =
    "(declare-fun p (Int Int) Bool)(declare-fun q (Int Real Int) Bool)\
     (declare-fun k (Int) Int)(declare-fun h (Int) Int)\
     (declare-fun kr (Int) Real)(declare-const c Int)" in
  let cases = [
    "existential", "(exists ((x Int)) (p x z))", "(p (k z) z)", true;
    "negative-universal", "(not (forall ((x Int)) (p x z)))",
      "(not (p (k z) z))", true;
    "negative-double-negation", "(not (forall ((x Int)) (not (p x z))))",
      "(p (k z) z)", true;
    "joint-mixed-sort", "(exists ((x Int) (r Real)) (q x r z))",
      "(q (k z) (kr z) z)", true;
    "joint-distinct-witnesses", "(exists ((x Int) (y Int)) (and (not (= x y)) (p x z)))",
      "(and (not (= (k z) (h z))) (p (k z) z))", true;
    "unused-bound-variable", "(exists ((x Int) (y Real)) (p x z))",
      "(p (k z) z)", true;
    "nested-binder", "(exists ((x Int)) (forall ((y Int)) (p x y)))",
      "(forall ((y Int)) (p (k z) y))", true;
    "missing-dependency", "(exists ((x Int)) (p x z))", "(p c z)", false;
    "inconsistent-occurrences", "(exists ((x Int)) (p x x))", "(p (k z) (h z))", false;
    "aliased-components", "(exists ((x Int) (y Int)) (not (= x y)))",
      "(not (= (k z) (k z)))", false;
    "captured-dependency", "(exists ((x Int)) (forall ((y Int)) (p x y)))",
      "(forall ((y Int)) (p (k y) y))", false;
    "self-reference", "(exists ((x Int)) (p x (k z)))", "(p (k z) (k z))", false;
    "positive-universal", "(forall ((x Int)) (p x z))", "(p (k z) z)", false;
    "wrong-negative-target", "(not (forall ((x Int)) (p x z)))", "(p (k z) z)", false
  ] in
  List.iter (fun (name, left, right, expected) ->
      let c = context () in
      let inputs = parse c (declarations ^
          "(assert (forall ((z Int) (unused Real)) (= " ^ left ^ " " ^ right ^ ")))") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let left, right = match B.cached_expression st (List.hd inputs) with
        | A.Quantifier (_, _, _, A.App (_, [left; right])) -> left, right
        | _ -> failwith "missing Skolem ambient binder" in
      let definition = SK.definition_of left right in
      require (Option.is_some definition = expected) ("incorrect Skolem match: " ^ name);
      if expected then (
        let definition = Option.get definition in
        let defs = [definition] in
        require (SK.ordered_context defs && SK.check defs left right)
          ("invalid Skolem choice context: " ^ name);
        let conclusion = U.Observational (left, right) in
        require (U.skolem_step defs conclusion []) ("Skolem step failed: " ^ name);
        require (not (U.skolem_step [] conclusion [])) "Skolem step ignored its choice context";
        require (not (U.skolem_step defs (U.Equal (left, right)) []))
          "Skolemization was treated as ordinary equality";
        require (not (U.skolem_step defs conclusion [conclusion]))
          "Skolemization ignored an unexpected premise";
        let leaf = { U.binder_name = "sk";
          binder_formula = Z3ObservationalEquality.mk_oeq_expr left right;
          binder_premises = []; binder_sorts = None } in
        require (U.binder_step_with_context defs [] leaf conclusion [])
          "Skolem step was not available inside a binder";
        require (SK.add_definition defs { definition with SK.negative = not definition.SK.negative } = None)
          "incompatible choice definitions shared a Skolem symbol";
        let recursive = { definition with SK.body = right } in
        require (not (SK.valid recursive)) "self-dependent choice definition was admitted"))
    cases;
  let c = context () in
  let inputs = parse c
      "(declare-fun p (Int Int) Bool)(declare-fun q (Int) Bool)(declare-fun k (Int) Int)\
       (assert (forall ((z Int)) (= (exists ((x Int)) (p x z)) (p (k z) z))))\
       (assert (forall ((z Int)) (= (not (exists ((x Int)) (p x z)))\
                                    (forall ((x Int)) (not (p x z))))))\
       (assert (forall ((z Int)) (= (= (q z) (exists ((x Int)) (p x z)))\
         (and (or (not (q z)) (p (k z) z))\
              (or (q z) (forall ((x Int)) (not (p x z))))))))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  let relations = List.map (fun native ->
      match B.cached_expression st native with
      | A.Quantifier (_, _, _, A.App (_, [left; right])) -> U.Observational (left, right)
      | _ -> failwith "expected a Skolem NNF body relation") inputs in
  (match relations with
   | [positive; negative; conclusion] ->
       require (U.binder_boolean_step false conclusion [positive; negative])
         "NNF did not compose positive Skolem and negative duality premises";
       require (not (U.binder_boolean_step false conclusion [positive]) &&
                not (U.binder_boolean_step false conclusion [negative]))
         "NNF composed Skolem witnesses without both polarity premises";
       (match conclusion with
        | U.Observational (left, right) ->
            require (not (U.binder_boolean_step false (U.Equal (left, right)) [positive; negative]))
              "NNF converted choice observations to ordinary equality"
        | _ -> assert false)
   | _ -> failwith "expected three Skolem NNF regression formulas");
  let native_sources = [
    "(declare-fun p (Int) Bool)(assert (exists ((x Int)) (p x)))\
     (assert (forall ((x Int)) (not (p x))))";
    "(declare-fun p (Int Real) Bool)(assert (exists ((x Int) (y Real)) (p x y)))\
     (assert (forall ((x Int) (y Real)) (not (p x y))))";
    "(declare-fun p (Int) Bool)(declare-fun q (Int) Bool)\
     (assert (not (forall ((x Int)) (p x))))(assert (forall ((x Int)) (q x)))\
     (assert (forall ((x Int)) (=> (q x) (p x))))";
    "(declare-fun p (Int Int) Bool)\
     (assert (forall ((x Int)) (exists ((y Int)) (p x y))))\
     (assert (forall ((x Int) (y Int)) (not (p x y))))";
    "(declare-fun p (Int Int) Bool)(declare-fun q (Int) Bool)\
     (assert (forall ((z Int)) (= (q z) (exists ((x Int)) (p x z)))))\
     (assert (q 0))(assert (forall ((x Int)) (not (p x 0))))"
  ] in
  List.iter (fun source ->
      let doc = document source in
      check_indexed doc;
      require (P.check_document doc = Some Z.zero) ("native Skolem proof was not certified: " ^ source);
      let defs = Option.get (P.collect_definitions [] (P.axiom_branches doc.P.entries) doc.P.entries) in
      let skolems = Option.get (P.collect_skolems defs [] doc.P.entries) in
      require (skolems <> []) "native Skolem regression omitted Skolemization";
      require (SK.order_context (Z.of_int (List.length skolems)) skolems <> None)
        "native Skolem dependencies could not be ordered")
    native_sources;
  let doc = document (List.hd native_sources) in
  let skolems = Option.get (P.collect_skolems [] [] doc.P.entries) in
  let f = snd (List.hd (List.hd skolems).SK.witnesses) in
  require (f.A.domain = []) "expected a ground Skolem witness for freshness mutation";
  let sk = A.App (f, []) in
  let mutation = { doc with P.assertions =
      Z3ResolutionProofTheory.mk_eq_expr sk sk :: doc.P.assertions } in
  check_indexed mutation;
  require (P.check_document mutation = None) "Skolem symbol already in original inputs was trusted";
  (match P.diagnose_document mutation with
   | P.DocumentRejected (P.SkolemFreshness, _, _) -> ()
   | _ -> failwith "Skolem freshness rejection was not diagnosed");
  let d = List.hd skolems in
  let g = { f with A.decl_name = f.A.decl_name ^ "_other" } in
  let a = A.App (f, []) and b = A.App (g, []) in
  let first = { d with SK.body = Z3ResolutionProofTheory.mk_eq_expr
      (A.Var (Z.zero, f.A.range)) b } in
  let second = { d with SK.witnesses = [Z.zero, g];
      body = Z3ResolutionProofTheory.mk_eq_expr (A.Var (Z.zero, f.A.range)) a } in
  require (SK.valid first && SK.valid second) "cyclic-choice mutation was not individually well formed";
  require (SK.order_context (Z.of_int 2) [first; second] = None)
    "cyclic Skolem definitions were admitted";
  let independent = { second with SK.body = Z3ResolutionProofTheory.mk_eq_expr
      (A.Var (Z.zero, f.A.range)) (A.Var (Z.zero, f.A.range)) } in
  require (SK.order_context (Z.of_int 2) [independent; first] <> None)
    "acyclic Skolem definitions could not be reordered"

let checked_vacuous_skolemization () =
  let module SK = Z3Skolemization in
  let declarations = "(declare-fun p (Int Int) Bool)" in
  let relation left right =
    let c = context () in
    let inputs = parse c (declarations ^
        "(assert (forall ((z Int) (w Int)) (= " ^ left ^ " " ^ right ^ ")))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match B.cached_expression st (List.hd inputs) with
    | A.Quantifier (_, _, _, A.App (_, [left; right])) -> left, right
    | _ -> failwith "missing vacuous Skolem ambient binder" in
  (* A block none of whose variables occurs in its body needs no choice context: the
     instance is the body with the block removed and the ambient indices lowered. *)
  let cases = [
    "unused-existential", "(exists ((x Int)) (p z w))", "(p z w)", true;
    "unused-multi-binder", "(exists ((x Int) (y Int)) (p z w))", "(p z w)", true;
    "unused-mixed-sorts", "(exists ((x Int) (r Real) (b Bool)) (p z w))", "(p z w)", true;
    "unused-nested-binder", "(exists ((x Int)) (forall ((y Int)) (p y z)))",
      "(forall ((y Int)) (p y z))", true;
    "unused-shadowed-binder", "(exists ((x Int)) (forall ((x Int)) (p x z)))",
      "(forall ((x Int)) (p x z))", true;
    "unused-negative-universal", "(not (forall ((x Int)) (p z w)))", "(not (p z w))", true;
    "unused-negative-double-negation", "(not (forall ((x Int)) (not (p z w))))", "(p z w)", true;
    "unused-negative-multi-binder", "(not (forall ((x Int) (r Real)) (p z w)))",
      "(not (p z w))", true;
    "body-mutation", "(exists ((x Int)) (p z w))", "(p w z)", false;
    "body-extension", "(exists ((x Int)) (p z w))", "(and (p z w) true)", false;
    "block-kept", "(exists ((x Int)) (p z w))", "(exists ((x Int)) (p z w))", false;
    "partial-removal", "(exists ((x Int) (y Int)) (p z w))", "(exists ((x Int)) (p z w))", false;
    "used-variable-dropped", "(exists ((x Int)) (p x w))", "(p z w)", false;
    "used-variable-unlowered", "(exists ((x Int)) (p x w))", "(p w w)", false;
    "partly-used-block", "(exists ((x Int) (y Int)) (p x w))", "(p z w)", false;
    "used-under-nested-binder", "(exists ((x Int)) (forall ((y Int)) (p x y)))",
      "(forall ((y Int)) (p z y))", false;
    "positive-universal", "(forall ((x Int)) (p z w))", "(p z w)", false;
    "negated-existential", "(not (exists ((x Int)) (p z w)))", "(not (p z w))", false;
    "wrong-negative-target", "(not (forall ((x Int)) (p z w)))", "(p z w)", false;
    "negative-body-mutation", "(not (forall ((x Int)) (p z w)))", "(not (p w z))", false;
    "negative-used-variable", "(not (forall ((x Int)) (p x w)))", "(not (p w w))", false;
    "no-quantifier", "(p z w)", "(p z w)", false
  ] in
  List.iter (fun (name, left, right, expected) ->
      let left, right = relation left right in
      let conclusion = U.Observational (left, right) in
      require (U.skolem_step [] conclusion [] = expected)
        ("incorrect vacuous Skolem decision: " ^ name);
      if expected then (
        require (Option.is_none (SK.definition_of left right))
          ("an unused block received a choice definition: " ^ name);
        require (SK.check [] left right) ("empty choice context rejected an unused block: " ^ name);
        require (not (U.skolem_step [] (U.Equal (left, right)) []))
          "an unused block was treated as ordinary equality";
        require (not (U.skolem_step [] conclusion [conclusion]))
          "an unused block ignored an unexpected premise";
        let leaf = { U.binder_name = "sk";
          binder_formula = Z3ObservationalEquality.mk_oeq_expr left right;
          binder_premises = []; binder_sorts = None } in
        require (U.binder_step_with_context [] [] leaf conclusion [])
          ("an unused block was not available inside a binder: " ^ name);
        let leaf = { leaf with U.binder_name = "refl" } in
        require (not (U.binder_step_with_context [] [] leaf conclusion []))
          ("an unused block was accepted under another rule name: " ^ name)))
    cases;
  (* Open and mis-lowered de Bruijn forms that SMT-LIB text cannot spell. *)
  let integer = A.BaseSort "Int" in
  let var n = A.Var (Z.of_int n, A.bool_sort) in
  let exists sorts body = A.Quantifier (A.Exists_k, sorts, A.bool_sort, body) in
  List.iter (fun (name, source, target, expected) ->
      require (U.skolem_step [] (U.Observational (source, target)) [] = expected)
        ("incorrect de Bruijn handling of an unused block: " ^ name))
    ["ambient-index-lowered", exists [integer] (var 1), var 0, true;
     "two-variable-block-lowered", exists [integer; integer] (var 2), var 0, true;
     "open-index-lowered", exists [integer] (var 5), var 4, true;
     "ambient-index-kept", exists [integer] (var 1), var 1, false;
     "open-index-kept", exists [integer] (var 5), var 5, false;
     "bound-variable-used", exists [integer] (var 0), var 0, false;
     "second-variable-used", exists [integer; integer] (var 1), var 0, false;
     "non-Boolean-body", exists [integer] (A.Var (Z.one, integer)), A.Var (Z.zero, integer), false]

let checked_quantifier_pulling () =
  let declarations =
    "(declare-fun p (Int Int) Bool)(declare-fun q (Real) Bool)\
     (declare-fun r (Int) Bool)(declare-fun s (Int) Bool)(declare-const c Bool)" in
  let cases = [
    "exists-flatten", "(exists ((x Int)) (exists ((y Int)) (p x y)))",
      "(exists ((x Int) (y Int)) (p x y))", true;
    "forall-flatten", "(forall ((x Int)) (forall ((y Int)) (p x y)))",
      "(forall ((x Int) (y Int)) (p x y))", true;
    "three-blocks", "(exists ((x Int)) (exists ((y Int)) (exists ((z Int)) (p x z))))",
      "(exists ((x Int) (y Int) (z Int)) (p x z))", true;
    "mixed-sorts", "(exists ((x Int)) (exists ((y Real)) (and (r x) (q y))))",
      "(exists ((x Int) (y Real)) (and (r x) (q y)))", true;
    "not-forall", "(not (forall ((x Int)) (r x)))",
      "(exists ((x Int)) (not (r x)))", true;
    "not-exists", "(not (exists ((x Int)) (r x)))",
      "(forall ((x Int)) (not (r x)))", true;
    "negative-boolean-context", "(not (and (forall ((x Int)) (r x)) c))",
      "(exists ((x Int)) (or (not (r x)) (not c)))", true;
    "and-forall", "(and (forall ((x Int)) (r x)) c)",
      "(forall ((x Int)) (and (r x) c))", true;
    "and-exists", "(and c (exists ((x Int)) (r x)))",
      "(exists ((x Int)) (and c (r x)))", true;
    "or-forall", "(or (forall ((x Int)) (r x)) c)",
      "(forall ((x Int)) (or (r x) c))", true;
    "or-exists", "(or c (exists ((x Int)) (r x)))",
      "(exists ((x Int)) (or c (r x)))", true;
    "multiple-blocks", "(and (forall ((x Int)) (r x)) c (forall ((y Real)) (q y)))",
      "(forall ((y Real) (x Int)) (and (r x) c (q y)))", true;
    "multiple-existentials", "(or (exists ((x Int)) (r x)) (exists ((y Real)) (q y)))",
      "(exists ((y Real) (x Int)) (or (r x) (q y)))", true;
    "multi-variable-block-order",
      "(or (forall ((a Int) (b Real)) (and (p z a) (q b)))\
           (forall ((c Int) (d Int)) (p c d)))",
      "(forall ((c Int) (d Int) (a Int) (b Real))\
         (or (and (p z a) (q b)) (p c d)))", true;
    "mixed-kinds", "(and (forall ((x Int)) (r x)) (exists ((y Real)) (q y)))",
      "(exists ((y Real)) (forall ((x Int)) (and (r x) (q y))))", true;
    "open-siblings", "(or (r z) (exists ((x Int)) (p z x)) (s z))",
      "(exists ((x Int)) (or (r z) (p z x) (s z)))", true;
    "nested-sibling-binders",
      "(and (exists ((x Int)) (p z x))\
            (= (lambda ((t Int)) (+ t z)) (lambda ((t Int)) (+ z t))))",
      "(exists ((x Int)) (and (p z x)\
            (= (lambda ((t Int)) (+ t z)) (lambda ((t Int)) (+ z t)))))", true;
    "wrong-kind", "(exists ((x Int)) (exists ((y Int)) (p x y)))",
      "(forall ((x Int) (y Int)) (p x y))", false;
    "swapped-variables", "(exists ((x Int)) (exists ((y Int)) (p x y)))",
      "(exists ((x Int) (y Int)) (p y x))", false;
    "changed-sort", "(exists ((x Int)) (exists ((y Real)) (and (r x) (q y))))",
      "(exists ((x Int) (y Int)) (and (r x) c))", false;
    "captured-dependency", "(or (r z) (exists ((x Int)) (p z x)))",
      "(exists ((x Int)) (or (r x) (p x x)))", false;
    "dropped-sibling", "(and c (exists ((x Int)) (r x)))",
      "(exists ((x Int)) (r x))", false;
    "wrong-block-order", "(and (forall ((x Int)) (r x)) (forall ((y Real)) (q y)))",
      "(forall ((x Int) (y Real)) (and (r x) (q y)))", false;
    "unsupported-implication", "(=> c (exists ((x Int)) (r x)))",
      "(exists ((x Int)) (=> c (r x)))", false
  ] in
  List.iter (fun (name, left, right, expected) ->
      let c = context () in
      let inputs = parse c (declarations ^
          "(assert (forall ((z Int)) (= " ^ left ^ " " ^ right ^ ")))" ^
          "(assert (= (forall ((z Int)) " ^ left ^ ") (forall ((z Int)) " ^ right ^ ")))") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let formula = match B.cached_expression st (List.hd inputs) with
        | A.Quantifier (_, _, _, body) -> body
        | _ -> failwith "missing ambient binder" in
      let conclusion = Option.get (U.classify_fact formula) in
      require (U.check_step U.PullQuantifier conclusion [] = expected)
        ("incorrect pull-quant decision: " ^ name);
      let certificate = { U.binder_entries = [
          { U.binder_name = "pull-quant"; binder_formula = formula;
            binder_premises = []; binder_sorts = None }];
          binder_root = Z.zero } in
      (* A binder certificate's root is used at the closed top-level scope, so the
         open step alone is now an obligation; under its binder it is decided. *)
      require (U.check_binder certificate conclusion = (expected && Z3Definitions.scoped [] formula))
        ("incorrect open binder pull-quant decision: " ^ name);
      let closed = B.cached_expression st (List.nth inputs 1) in
      let closed_conclusion = Option.get (U.classify_fact closed) in
      let wrapped = { U.binder_entries = certificate.U.binder_entries @ [
          { U.binder_name = "quant-intro"; binder_formula = closed;
            binder_premises = [Z.zero]; binder_sorts = Some [A.BaseSort "Int"] }];
          binder_root = Z.one } in
      require (U.check_binder wrapped closed_conclusion = expected)
        ("incorrect binder pull-quant decision under its binder: " ^ name);
      if expected then begin
        require (not (U.check_step U.PullQuantifier conclusion [conclusion]))
          "pull-quant ignored an unexpected premise";
        require (not (U.check_binder
            { certificate with U.binder_entries =
                List.map (fun e -> { e with U.binder_premises = [Z.one] })
                  certificate.U.binder_entries } conclusion))
          "pull-quant binder accepted a forward or missing premise";
        match conclusion with
        | U.Equal (a, b) ->
            require (not (Z3QuantifierPull.check a Z3ResolutionProofTheory.false_expr))
              "pull-quant accepted an altered body";
            require (Z3QuantifierPull.normalize Z.zero a = None)
              "pull-quant accepted exhausted normalization fuel";
            let bad = U.Equal (a, Z3ResolutionProofTheory.false_expr) in
            require (match U.check_node [] { U.kind = U.PullQuantifier;
                conclusion = bad; premises = [] } with
                | Some (_, n) -> Z.equal n Z.one | None -> false)
              "unsupported pull-quant did not retain an explicit obligation";
            require (A.get_sort a = A.get_sort b) "pull-quant changed the result sort"
        | _ -> failwith "expected an equality"
      end) cases;
  let sources = [
    "(declare-fun p (Int Int) Bool)\
     (assert (not (exists ((x Int)) (exists ((y Int)) (p x y)))))\
     (assert (p 0 1))";
    "(declare-fun p (Int Int) Bool)\
     (assert (forall ((x Int)) (forall ((y Int)) (p x y))))\
     (assert (not (p 0 1)))";
    "(declare-fun p (Int Real) Bool)\
     (assert (not (exists ((x Int)) (exists ((y Real)) (p x y)))))\
     (assert (p 0 1.5))"
  ] in
  List.iter (fun source ->
      let doc = document source in
      require (P.check_document doc = Some Z.zero)
        ("native quantifier pulling was not certified: " ^ source);
      require (List.exists (fun e -> e.P.rule = U.PullQuantifier) doc.entries)
        "native pull-quant regression omitted the rule";
      let entries = List.map (fun e -> if e.P.rule = U.PullQuantifier then
          match e.P.formula with
          | A.App (f, [a; _]) ->
              { e with P.formula = A.App (f, [a; Z3ResolutionProofTheory.false_expr]) }
          | _ -> failwith "unexpected native pull-quant shape"
        else e) doc.entries in
      require (P.check_document { doc with entries } <> Some Z.zero)
        "mutated native pull-quant certified a refutation") sources

let checked_quantifier_reductions () =
  let declarations =
    "(declare-fun p (Int Int) Bool)(declare-fun r (Int) Bool)\
     (declare-fun q (Real) Bool)(declare-const c Bool)" in
  let cases = [
    U.ElimUnused, "unused-first",
      "(forall ((x Int) (y Int)) (r y))", "(forall ((y Int)) (r y))", true;
    U.ElimUnused, "unused-middle",
      "(exists ((x Int) (y Real) (w Int)) (p x w))",
      "(exists ((x Int) (w Int)) (p x w))", true;
    U.ElimUnused, "unused-last",
      "(forall ((x Int) (y Real)) (r x))", "(forall ((x Int)) (r x))", true;
    U.ElimUnused, "unused-all", "(exists ((x Int) (y Real)) c)", "c", true;
    U.ElimUnused, "unused-ambient",
      "(forall ((x Int)) (p z z))", "(p z z)", true;
    U.ElimUnused, "unused-under-binder",
      "(forall ((x Int) (y Real)) (exists ((w Int)) (p x w)))",
      "(forall ((x Int)) (exists ((w Int)) (p x w)))", true;
    U.ElimUnused, "unused-under-lambda",
      "(forall ((x Int) (y Real)) (= (lambda ((w Int)) (+ x w z)) (lambda ((w Int)) (+ w z))))",
      "(forall ((x Int)) (= (lambda ((w Int)) (+ x w z)) (lambda ((w Int)) (+ w z))))", true;
    U.ElimUnused, "captured-ambient",
      "(forall ((x Int)) (p z x))", "(forall ((x Int)) (p x x))", false;
    U.ElimUnused, "removed-used",
      "(forall ((x Int) (y Int)) (p x y))", "(forall ((x Int)) (p x x))", false;
    U.PushQuantifier, "forall-and",
      "(forall ((x Int) (y Real)) (and (r x) (q y)))",
      "(and (forall ((x Int)) (r x)) (forall ((y Real)) (q y)))", true;
    U.PushQuantifier, "exists-or",
      "(exists ((x Int) (y Real)) (or (r x) (q y) c))",
      "(or (exists ((x Int)) (r x)) (exists ((y Real)) (q y)) c)", true;
    U.PushQuantifier, "forall-and-demorgan",
      "(forall ((x Int)) (not (or (not (r x)) (not (p x x)))))",
      "(and (forall ((x Int)) (p x x)) (forall ((x Int)) (r x)))", true;
    U.PushQuantifier, "exists-or-demorgan",
      "(exists ((x Int)) (not (and (not (r x)) (not (p x x)))))",
      "(or (exists ((x Int)) (p x x)) (exists ((x Int)) (r x)))", true;
    U.PushQuantifier, "demorgan-mixed-quantifiers",
      "(forall ((x Int)) (not (or (not (r x)) (not (p x x)))))",
      "(and (forall ((x Int)) (r x)) (exists ((x Int)) (p x x)))", false;
    U.PushQuantifier, "demorgan-changed-binders",
      "(forall ((x Int)) (not (or (not (r x)) (not (p x x)))))",
      "(and (forall ((x Int)) (r x)) (forall ((x Int) (y Int)) (p x y)))", false;
    U.PushQuantifier, "demorgan-changed-binder-sort",
      "(forall ((x Int)) (not (or (not (r x)) (not (p x x)))))",
      "(and (forall ((x Int)) (r x)) (forall ((x Real)) (q x)))", false;
    U.PushQuantifier, "demorgan-dropped-body",
      "(forall ((x Int)) (not (or (not (r x)) (not (p x x)))))",
      "(and (forall ((x Int)) (r x)) (forall ((x Int)) (r x)))", false;
    U.PushQuantifier, "demorgan-wrong-connective",
      "(forall ((x Int)) (not (or (not (r x)) (not (p x x)))))",
      "(or (forall ((x Int)) (r x)) (forall ((x Int)) (p x x)))", false;
    U.PushQuantifier, "forall-or",
      "(forall ((x Int)) (or (r x) (not (r x))))",
      "(or (forall ((x Int)) (r x)) (forall ((x Int)) (not (r x))))", false;
    U.PushQuantifier, "exists-and",
      "(exists ((x Int)) (and (r x) (not (r x))))",
      "(and (exists ((x Int)) (r x)) (exists ((x Int)) (not (r x))))", false;
    U.PushQuantifier, "push-dropped-body",
      "(forall ((x Int)) (and (r x) c))", "(forall ((x Int)) (r x))", false;
    U.DestructiveEquality, "der-forall",
      "(forall ((x Int)) (or (not (= x z)) (r x)))", "(r z)", true;
    U.DestructiveEquality, "der-reversed",
      "(forall ((x Int)) (or (not (= z x)) (r x)))", "(r z)", true;
    U.DestructiveEquality, "der-exists",
      "(exists ((x Int)) (and (= x z) (r x)))", "(r z)", true;
    U.DestructiveEquality, "der-exists-reversed",
      "(exists ((x Int)) (and (= z x) (r x)))", "(r z)", true;
    U.DestructiveEquality, "der-chain",
      "(forall ((x Int) (y Int)) (or (not (= x y)) (not (= y z)) (p x y)))",
      "(p z z)", true;
    U.DestructiveEquality, "der-nested-disjunction",
      "(forall ((x Int)) (or c (or (not (= x z)) (r x))))",
      "(or c (r z))", true;
    U.DestructiveEquality, "der-bool-literal",
      "(forall ((b Bool)) (or b (= b c)))", "(= false c)", true;
    U.DestructiveEquality, "der-bool-negative",
      "(exists ((b Bool)) (and (not b) (= b c)))", "(= false c)", true;
    U.DestructiveEquality, "der-bool-equality",
      "(forall ((b Bool)) (or (= b c) b))", "(not c)", true;
    U.DestructiveEquality, "der-forall-unit",
      "(forall ((x Int)) (not (= x z)))", "false", true;
    U.DestructiveEquality, "der-exists-unit",
      "(exists ((x Int)) (= x z))", "true", true;
    U.DestructiveEquality, "der-under-binder",
      "(exists ((x Int)) (and (= x z) (forall ((y Int)) (p x y))))",
      "(forall ((y Int)) (p z y))", true;
    U.DestructiveEquality, "der-occurs",
      "(exists ((x Int)) (and (= x (+ x 1)) (r x)))", "(r z)", false;
    U.DestructiveEquality, "der-cyclic",
      "(forall ((x Int) (y Int)) (or (not (= x (+ y 1))) (not (= y (+ x 1))) (p x y)))",
      "(p z z)", false;
    U.DestructiveEquality, "der-changed-substitution",
      "(forall ((x Int)) (or (not (= x z)) (r x)))", "(r 7)", false;
    U.RewriteRule, "lambda-extensional",
      "(= (lambda ((x Int)) (+ x z)) (lambda ((x Int)) (+ z x)))",
      "(forall ((x Int)) (= (+ x z) (+ z x)))", true;
    U.RewriteRule, "lambda-constant",
      "(= ((as const (Array Int Int)) z) (lambda ((x Int)) (+ x z)))",
      "(forall ((x Int)) (= (+ x z) z))", true;
    U.RewriteRule, "lambda-constant-reversed",
      "(= (lambda ((x Int)) (+ x z)) ((as const (Array Int Int)) z))",
      "(forall ((x Int)) (= (+ x z) z))", true;
    U.RewriteRule, "lambda-beta",
      "(= (select (lambda ((x Int)) (+ x z)) 5) 0)", "(= (+ 5 z) 0)", true;
    U.RewriteRule, "lambda-beta-direct",
      "(select (lambda ((x Int)) (+ x z)) 5)", "(+ 5 z)", true;
    U.RewriteRule, "lambda-beta-multi",
      "(select (lambda ((x Int) (b Bool)) (ite b x z)) 5 c)",
      "(ite c 5 z)", true;
    U.RewriteRule, "lambda-beta-nested",
      "(select (lambda ((x Int)) (lambda ((y Int)) (+ x y z))) 5)",
      "(lambda ((y Int)) (+ 5 y z))", true;
    U.RewriteRule, "lambda-captured-constant",
      "(= ((as const (Array Int Int)) z) (lambda ((x Int)) (+ x z)))",
      "(forall ((x Int)) (= (+ x x) x))", false;
    U.RewriteRule, "lambda-beta-wrong",
      "(select (lambda ((x Int)) (+ x z)) 5)", "(+ z z)", false;
    U.RewriteRule, "lambda-beta-wrong-order",
      "(select (lambda ((x Int) (y Int)) (- x y)) 5 7)", "(- 7 5)", false
  ] in
  List.iter (fun (rule, name, left, right, expected) ->
      let c = context () in
      let inputs = parse c (declarations ^
          "(assert (forall ((z Int)) (= " ^ left ^ " " ^ right ^ ")))") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let a, b = match B.cached_expression st (List.hd inputs) with
        | A.Quantifier (_, _, _, A.App (_, [a; b])) -> a, b
        | _ -> failwith "expected ambient equality" in
      let conclusion = U.Equal (a, b) in
      require (U.check_step rule conclusion [] = expected)
        ("incorrect quantified rewrite decision: " ^ name);
      require (not (U.check_step rule conclusion [conclusion]))
        ("quantified rewrite accepted unexpected premises: " ^ name);
      require (match U.check_node [] { U.kind = rule; conclusion = conclusion; premises = [] } with
          | Some (_, n) -> Z.equal n (if expected then Z.zero else Z.one)
          | None -> false)
        ("quantified rewrite lost its obligation: " ^ name)) cases

let checked_nested_nnf_replacement () =
  (* A Boolean NNF step rewrites its premises inside binder bodies. The binder
     scope guard reads each premise at the step's own scope, so a closed fact is
     substituted under a binder, while an open fact (the body of `forall x`,
     whose variable the step would read under a different binder) is not. *)
  List.iter (fun (name, left, right, leaf_assertion, open_leaf) ->
      let c = context () in
      let inputs = parse c
          ("(declare-fun p (Int) Bool)(declare-const c Bool)\
            (assert " ^ leaf_assertion ^ ")\
            (assert (= " ^ left ^ " " ^ right ^ "))") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let leaf_formula = match B.cached_expression st (List.hd inputs), open_leaf with
        | A.Quantifier (_, _, _, body), true -> body
        | formula, false -> formula
        | _ -> failwith "missing arithmetic body" in
      let formula = B.cached_expression st (List.nth inputs 1) in
      let leaf = { U.binder_name = "rewrite"; binder_formula = leaf_formula;
                   binder_premises = []; binder_sorts = None } in
      let root = { U.binder_name = name; binder_formula = formula;
                   binder_premises = [Z.zero]; binder_sorts = None } in
      let certificate = { U.binder_entries = [leaf; root]; binder_root = Z.one } in
      let conclusion = Option.get (U.classify_fact formula) in
      if open_leaf then
        require (not (U.check_binder certificate conclusion))
          ("NNF substituted an open fact under a binder outside its scope: " ^ name)
      else
        require (U.check_binder certificate conclusion)
          ("NNF did not substitute a closed fact under a binder: " ^ name);
      require (not (U.check_binder { certificate with U.binder_entries =
          [{ leaf with U.binder_name = "hypothesis" }; root] } conclusion))
        "NNF generalized a hypothesis while rewriting a nested binder")
    ["nnf-pos", "(and (forall ((x Int)) (p (+ x 0))) c)",
       "(and (forall ((x Int)) (p x)) c)", "(forall ((x Int)) (= (+ x 0) x))", true;
     "nnf-neg", "(not (and (forall ((x Int)) (p (+ x 0))) c))",
       "(or (exists ((x Int)) (not (p x))) (not c))", "(forall ((x Int)) (= (+ x 0) x))", true;
     "nnf-pos", "(and (forall ((x Int)) (p (+ 1 0))) c)",
       "(and (forall ((x Int)) (p 1)) c)", "(= (+ 1 0) 1)", false;
     "nnf-neg", "(not (and (forall ((x Int)) (p (+ 1 0))) c))",
       "(or (exists ((x Int)) (not (p 1))) (not c))", "(= (+ 1 0) 1)", false]

let checked_theory_extensions () =
  let declarations =
    "(declare-datatype T ((C (field Int)) (D (other Int))))\
     (declare-datatype L ((nil) (cons (head T) (tail L))))\
     (declare-const xs L)(declare-const t T)\
     (declare-const a Int)(declare-const b Int)(declare-const d Int)\
     (declare-const v (_ BitVec 8))(declare-const w (_ BitVec 8))\
     (declare-const arr (Array Int Int))" in
  let cases = [
    "datatype-injectivity", "(or (not (= (C a) (C b))) (= a b))", true;
    "datatype-disjointness", "(not (= (C a) (D b)))", true;
    "datatype-recognizer", "((_ is C) (C a))", true;
    "datatype-recognizer-mismatch", "(not ((_ is D) (C a)))", true;
    "datatype-accessor", "(= (field (C a)) a)", true;
    "datatype-invalid-injectivity", "(or (not (= (C a) (C b))) (= a d))", false;
    "datatype-wrong-accessor", "(= (field (C a)) b)", false;
    "datatype-wrong-recognizer", "((_ is C) (D b))", false;
    "datatype-nested-disjointness",
      "(not (= (cons (C a) nil) (cons (D b) nil)))", true;
    "datatype-nested-tail-disjointness",
      "(not (= (cons (C a) (cons (C b) nil)) (cons (C a) nil)))", true;
    "datatype-nested-injectivity",
      "(or (not (= (cons (C a) xs) (cons (C b) xs))) (= a b))", true;
    "datatype-invalid-nested-equality",
      "(= (cons (C a) xs) (cons (C b) xs))", false;
    "array-read", "(= (select (store arr a b) a) b)", true;
    "array-overwrite", "(= (store (store arr a b) a d) (store arr a d))", true;
    "array-invalid-read", "(= (select (store arr a b) a) d)", false;
    "arithmetic-reflexive", "(<= (+ a 1) (+ 1 a))", true;
    "arithmetic-unit-transitivity",
      "(or (not (< a b)) (not (< b d)) (< a d))", true;
    "arithmetic-invalid-bound", "(or (not (< a b)) (< b a))", false;
    "bv-and-idempotent", "(= (bvand v v) v)", true;
    "bv-or-idempotent", "(= (bvor v v) v)", true;
    "bv-xor-self", "(= (bvxor v v) #x00)", true;
    "bv-sub-self", "(= (bvsub v v) #x00)", true;
    "bv-neutral", "(= (bvadd v #x00) v)", true;
    "bv-double-not", "(= (bvnot (bvnot v)) v)", true;
    "bv-double-negation", "(= (bvneg (bvneg v)) v)", true;
    "bv-absorbing", "(= (bvmul v #x00) #x00)", true;
    "bv-wrap", "(= (bvadd #xff #x01) #x00)", true;
    "bv-literal-distinct", "(not (= #x01 #x02))", true;
    "bv-invalid-identity", "(= (bvand v w) v)", false;
    "bv-invalid-fold", "(= (bvadd #xff #x01) #x01)", false
  ] in
  List.iter (fun (name, formula, expected) ->
      let c = context () in
      let inputs = parse c (declarations ^ "(assert " ^ formula ^ ")") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let conclusion = Option.get (U.classify_fact (B.cached_expression st (List.hd inputs))) in
      require (U.checked_theory_lemma (U.Unverified "th-lemma") conclusion [] = expected)
        ("incorrect theory lemma decision: " ^ name);
      require (U.check_step U.DefAxiom conclusion [] = expected)
        ("incorrect definition axiom decision: " ^ name);
      require (match U.check_node [] {
          U.kind = U.Unverified "th-lemma"; conclusion = conclusion; premises = [] } with
          | Some (_, n) -> Z.equal n (if expected then Z.zero else Z.one)
          | None -> false)
        ("theory lemma lost its explicit obligation: " ^ name)) cases;
  let sources = [
    declarations ^ "(assert (= (C a) (C b)))(assert (not (= a b)))";
    declarations ^ "(assert (= (C a) (D b)))";
    declarations ^ "(assert (not (= (field (C a)) a)))";
    declarations ^ "(assert (not (= (bvand v v) v)))";
    declarations ^ "(assert (not (= (bvxor v v) #x00)))";
    declarations ^ "(assert (not (= (bvadd #xff #x01) #x00)))"
  ] in
  List.iter (fun source ->
      require (P.check_document (document source) = Some Z.zero)
        ("native theory proof was not certified: " ^ source)) sources;
  List.iter (fun (name, premises, target, expected) ->
      let c = context () in
      let inputs = parse c (declarations ^
          String.concat "" (List.map (fun e -> "(assert " ^ e ^ ")") (premises @ [target]))) in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let judgments = List.map (fun e -> Option.get (U.classify_fact (B.cached_expression st e))) inputs in
      let conclusion = List.hd (List.rev judgments) in
      let facts = List.rev (List.tl (List.rev judgments)) in
      require (U.checked_theory_lemma (U.Unverified "th-lemma") conclusion facts = expected)
        ("incorrect theory consequence: " ^ name))
    ["arithmetic-premises", ["(< a b)"; "(< b d)"], "(< a d)", true;
     "datatype-premise", ["(= (C a) (C b))"], "(= a b)", true;
     "datatype-constructor-recognizer", ["(= t (C a))"], "((_ is C) t)", true;
     "datatype-constructor-conflict",
       ["(not ((_ is C) t))"; "(= (C a) t)"], "false", true;
     "datatype-constructor-selector", ["(= t (C a))"], "(= (field t) a)", true;
     "datatype-constructor-chain",
       ["(= xs (cons t nil))"; "(= t (C a))"], "(= (field (head xs)) a)", true;
     "datatype-unmatched-selector", ["(= t (D a))"], "(= (field t) a)", false;
     "datatype-missing-constructor-equality", [], "((_ is C) t)", false;
     "datatype-invalid-propagated-field", ["(= t (C a))"], "(= (field t) b)", false;
     "datatype-binder-capture", ["(= t (C a))"],
       "(forall ((t T)) ((_ is C) t))", false;
     "datatype-cyclic-equality", ["(= xs (cons (C a) xs))"], "false", false;
     "bv-premise", ["(= (bvand v v) w)"], "(= v w)", true;
     "invalid-bv-consequence", ["(= (bvand v v) w)"], "(= v (bvnot w))", false];
  let c = context () in
  let inputs = parse c (declarations ^
      "(assert (forall ((t T)) (and (= t (C 0)) ((_ is C) t)\
        (forall ((t T)) ((_ is C) t)))))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.Quantifier (_, _, _, A.App (_, [equality; current; nested])) ->
       require (Z3TheoryNormalize.consequence [equality] current)
         "constructor equality was not usable in its own binder environment";
       require (not (Z3TheoryNormalize.consequence [equality] nested))
         "constructor propagation substituted an outer bound variable inside a nested binder"
   | _ -> failwith "unexpected nested datatype binder fixture");
  let c = context () in
  let inputs = parse c
      "(declare-sort Fake 0)(declare-const a Int)\
       (declare-fun C (Int) Fake)(declare-fun field (Fake) Int)\
       (assert (= (field (C a)) a))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  require (not (U.check_step U.DefAxiom
      (Option.get (U.classify_fact (B.cached_expression st (List.hd inputs)))) []))
    "datatype interpretation was inferred from a user-supplied name";
  let c = context () in
  let inputs = parse c "(declare-const v (_ BitVec 8))(assert (= (bvadd v #x00) v))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (f, args); _]) ->
       List.iter (fun width ->
           require (Z3BvLemma.rewrite (A.App ({ f with A.int_params = [Z.of_int width] }, args)) = None)
             "invalid bit-vector width escaped an erased refinement")
         [-1; 0; 9; 4097]
   | _ -> failwith "expected native bit-vector addition");
  let c = context () in
  let inputs = parse c
      "(assert (forall ((a Real) (b Real) (c Real))\
         (or (not (< a b)) (not (< b c)) (< a c))))" in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  let bound, formula = match B.cached_expression st (List.hd inputs) with
    | A.Quantifier (_, bs, _, body) -> bs, body
    | _ -> failwith "missing quantified arithmetic clause" in
  let conclusion = Option.get (U.classify_fact formula) in
  let leaf = { U.binder_name = "th-lemma"; binder_formula = formula;
               binder_premises = []; binder_sorts = None } in
  (* The open clause is the root only of an obligation; under its binders, through
     iff-true and forall introduction, it is checked. *)
  let certificate = { U.binder_entries = [leaf]; binder_root = Z.zero } in
  require (not (U.check_binder certificate conclusion))
    "an open binder root was certified at the top-level scope";
  let tt = Z3ResolutionProofTheory.true_expr in
  let iff = Z3ResolutionProofTheory.mk_iff_expr formula tt in
  let all body = A.Quantifier (A.Forall_k, bound, A.bool_sort, body) in
  let root = Z3ResolutionProofTheory.mk_eq_expr (all formula) (all tt) in
  let closed leaf = { U.binder_entries = [leaf;
      { U.binder_name = "iff-true"; binder_formula = iff; binder_premises = [Z.zero]; binder_sorts = None };
      { U.binder_name = "quant-intro"; binder_formula = root; binder_premises = [Z.one];
        binder_sorts = Some bound }]; binder_root = Z.of_int 2 } in
  let closed_conclusion = Option.get (U.classify_fact root) in
  require (U.check_binder (closed leaf) closed_conclusion)
    "an independently checked theory lemma was rejected inside a binder";
  require (not (U.check_binder (closed { leaf with U.binder_name = "assumed:nlsat" }) closed_conclusion))
    "a hidden NLSAT assumption was generalized"

let concrete_datatype_model () =
  let module V = Z3DatatypeValue in
  let module S = Z3DatatypeSignature in
  let c = context () in
  let inputs = parse c
      "(declare-datatypes ((Tree 0) (Forest 0))\
        (((leaf (number Int) (marked Bool)) (branch (children Forest))\
          (fork (left Tree) (right Tree)))\
         ((nil) (cons (first Tree) (rest Forest)))))\
       (declare-const x Tree)(assert (= (leaf 7 true) x))" in
  let root = match N.view_expression (List.hd inputs) with
    | N.Application (_, value :: _) -> Z3native.get_sort c value
    | _ -> failwith "expected a native datatype equality" in
  let schema = N.view_datatypes [root] in
  require (S.valid schema) "native mutually recursive datatype schema was rejected";
  require (List.length schema.S.sorts = 2 && List.length schema.S.cases = 5)
    "native datatype adapter omitted unreferenced or mutually recursive constructors";
  let find name = List.find (fun case -> case.S.constructor.A.decl_name = name) schema.S.cases in
  let leaf, branch, fork, nil, cons =
    find "leaf", find "branch", find "fork", find "nil", find "cons" in
  let sigma = S.signature schema in
  let witness sort = match S.shape_witness sigma sort with
    | Some value -> value | None -> failwith "productive datatype lacked a concrete witness" in
  let number, marked = witness (A.BaseSort "Int"), witness (A.BaseSort "Bool") in
  let leaf_value = S.constructor_value schema leaf [number; marked] in
  let nil_value = S.constructor_value schema nil [] in
  let cons_value = S.constructor_value schema cons [leaf_value; nil_value] in
  let fork_value = S.constructor_value schema fork [leaf_value; leaf_value] in
  let branch_value = S.constructor_value schema branch [cons_value] in
  require (V.has_sort sigma leaf.S.constructor.A.range branch_value)
    "valid mutually recursive constructor value was not well sorted";
  require (not (V.has_sort sigma leaf.S.constructor.A.range
      (V.Constructor (leaf.S.constructor, [marked; number]))))
    "datatype carrier accepted swapped heterogeneous fields";
  require (not (V.has_sort sigma leaf.S.constructor.A.range
      (V.Constructor (leaf.S.constructor, [number]))))
    "datatype carrier accepted an incorrect constructor arity";
  require (S.recognizer_value schema fork fork_value &&
           not (S.recognizer_value schema branch fork_value))
    "concrete datatype recognizers did not distinguish constructors";
  (* `S.accessor_value` is ghost since the typed-root G1a change (023988e32) and is not
     extracted. The three selector facts this test used to check at run time (the matched
     field of `branch`, and the argument-dependent wrong-constructor fallback on `leaf` and
     `fork`) are proved with their exact values, and wrong-value mutants refuted, in
     `Z3DatatypeNativeModelTests.a1_leaf`, `a1_fork`, `a1_branch` and `a1_mutants`, on this
     fixture. *)
  require (V.Constructor (fork.S.constructor, V.fields fork_value) = fork_value)
    "concrete datatype reconstruction failed";
  require (List.for_all (fun sort ->
      let value = witness sort in
      List.exists (fun case ->
          case.S.constructor.A.range = sort && S.recognizer_value schema case value)
        schema.S.cases) schema.S.sorts)
    "a well-sorted datatype value lacked a recognized constructor";
  (match V.descendant [Z.zero; Z.one] branch_value with
   | Some child -> require (child = nil_value && Z.lt (V.size child) (V.size branch_value))
       "recursive datatype subterms did not have smaller finite size"
   | None -> failwith "missing recursive datatype subterm");
  let children = List.hd branch.S.accessors in
  let opaque = { children with A.decl_name = "opaque"; interp = None; int_params = [] } in
  (* `S.interpretation`/`S.application` and `V.evaluate` are ghost since the typed-root G1a
     change (023988e32) and are not extracted. The facts this test used to check at run time
     through the supplied interpretation `other` (canonical constructor and recognizer
     dispatch, the matched `children` field, its argument-dependent fallback on `leaf` and
     `fork`, `opaque` reaching `other`, selector evaluation of `children x` at `fork`, and the
     quantifier evaluated with the supplied interpretation over the reversed typed binders
     [Bool true; Int false]) are proved with their exact values, and wrong-value mutants
     refuted, in `Z3DatatypeNativeModelTests.a2_*`, `a3_*` and `a4_*`, on this fixture and
     this `other`. The executable dispatch decisions those facts rest on are checked here on
     the native schema itself. *)
  require (List.mem fork.S.constructor sigma &&
           not (List.mem fork.S.recognizer sigma) && not (List.mem branch.S.recognizer sigma) &&
           S.find_recognizer fork.S.recognizer schema.S.cases = Some fork &&
           S.find_recognizer branch.S.recognizer schema.S.cases = Some branch)
    "native constructor or recognizer dispatch was not canonical";
  require (not (List.mem children sigma) &&
           S.find_recognizer children schema.S.cases = None &&
           S.find_accessor children schema.S.cases = Some { S.matched_case = branch; field = Z.zero } &&
           not (List.mem opaque sigma) &&
           S.find_recognizer opaque schema.S.cases = None &&
           S.find_accessor opaque schema.S.cases = None)
    "native selector dispatch lost matching fields or reached an opaque symbol";
  let scope = [leaf.S.constructor.A.range] in
  let expression = A.App (children, [A.Var (Z.zero, leaf.S.constructor.A.range)]) in
  require (Z3Definitions.scoped scope expression) "native evaluator fixture is not well sorted";
  let quantified = A.Quantifier (A.Forall_k, [A.BaseSort "Int"; A.BaseSort "Bool"],
      A.BaseSort "Bool", A.Var (Z.zero, A.BaseSort "Bool")) in
  require (Z3Definitions.scoped [] quantified) "native quantifier fixture is not well sorted";
  let forged = { children with A.int_params = [Z.zero; Z.zero; Z.of_int 99] } in
  require (S.find_accessor forged schema.S.cases = None &&
           S.find_recognizer { fork.S.recognizer with A.range = A.BaseSort "Int" }
             schema.S.cases = None)
    "native dispatch admitted invalid accessor indices or recognizer result sorts";
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (f, _); _]) ->
       require (f = leaf.S.constructor)
         "native schema constructor identity differs from proof-expression identity"
   | _ -> failwith "expected a marshaled constructor");
  let reject cases message = require (not (S.valid { schema with S.cases = cases })) message in
  reject (leaf :: schema.S.cases) "duplicate constructor IDs escaped schema checking";
  reject (List.filter (fun case -> case <> nil) schema.S.cases)
    "unproductive mutually recursive datatype sorts were admitted";
  let replace original changed = List.map (fun case -> if case = original then changed else case)
      schema.S.cases in
  reject (replace leaf { leaf with S.recognizer =
      { leaf.S.recognizer with A.int_params = [Z.zero; Z.zero] } })
    "a recognizer with incorrect constructor ownership was admitted";
  reject (replace leaf { leaf with S.accessors = List.rev leaf.S.accessors })
    "reordered datatype accessors were admitted";
  reject (replace leaf { leaf with S.accessors = [] })
    "missing datatype accessors were admitted";
  let nested = A.ArraySort ([A.BaseSort "Int"], leaf.S.constructor.A.range) in
  reject (replace branch { branch with
      S.constructor = { branch.S.constructor with A.domain = [nested] };
      accessors = List.map (fun accessor -> { accessor with A.range = nested }) branch.S.accessors })
    "nested recursive array fields were silently treated as opaque scalars";
  let native_schema source =
    let c = context () in
    let formula = List.hd (parse c source) in
    let root = match N.view_expression formula with
      | N.Application (_, value :: _) -> Z3native.get_sort c value
      | _ -> failwith "expected a native sort fixture" in
    N.view_datatypes [root] in
  List.iter (fun sort ->
      let schema = native_schema
          ("(declare-datatype T ((C) (D)))(declare-const x " ^ sort ^
           ")(assert (= x x))") in
      require (S.valid schema && List.length schema.S.sorts = 1 &&
               List.length schema.S.cases = 2)
        ("datatype signature was not collected through " ^ sort))
    ["(Seq T)"; "(Seq (Seq T))"; "(Array (Seq T) Int)"; "(Seq (Array Int T))"];
  List.iter (fun field ->
      let rejected = try
          ignore (native_schema
            ("(declare-datatype T ((C) (D)))" ^
             "(declare-datatype U ((empty) (node (items " ^ field ^ "))))" ^
             "(declare-const x U)(assert (= x x))"));
          false
        with N.Error message -> message = "Nested datatype sequence fields are not supported" in
      require rejected ("unsupported datatype sequence field was admitted: " ^ field))
    ["(Seq T)"; "(Seq U)"; "(Array Int (Seq T))"; "(Array (Seq T) Int)"]

let malformed_foreign_certificate () =
  let c = context () in
  let conclusion = List.hd (parse c "(assert false)") in
  let view = { N.proof_name = "th-lemma"; premises = []; conclusion;
               farkas = Some [Z.one, Z.zero]; assumed = None; lp_data = None;
               binding = None; instantiations = []; ff_pac = None } in
  match B.native_rule view Z3ResolutionProofTheory.false_expr with
  | _ -> failwith "malformed foreign certificate was accepted"
  | exception N.Error _ -> ()

let sorted_datatype_checker () =
  let module K = Z3SortedProof in
  let module S = Z3DatatypeSignature in
  let module DT = Z3SortedDatatype in
  let module R = Z3ResolutionProofTheory in
  let samples = [
    "exhaustiveness",
      "(declare-datatype T ((C) (D)))(declare-const x T)\
       (assert (not ((_ is C) x)))(assert (not ((_ is D) x)))";
    "exhaustiveness-three",
      "(declare-datatype T ((C) (D) (E)))(declare-const x T)\
       (assert (not ((_ is C) x)))(assert (not ((_ is D) x)))(assert (not ((_ is E) x)))";
    "reconstruction",
      "(declare-datatype T ((C (field Int)) (D)))(declare-const x T)\
       (assert ((_ is C) x))(assert (not (= x (C (field x)))))";
    "injectivity",
      "(declare-datatype T ((C (field Int)) (D)))\
       (declare-const a Int)(declare-const b Int)\
       (assert (= (C a) (C b)))(assert (not (= a b)))";
    "disjointness",
      "(declare-datatype T ((C (field Int)) (D)))(declare-const a Int)\
       (assert (= (C a) D))";
    "conditional-constructor",
      "(declare-datatype T ((C) (D)))(declare-const x T)\
       (assert (= x (ite false C D)))(assert (not (= x D)))";
    "symmetric-equality",
      "(declare-datatype T ((C) (D)))(declare-const x T)(declare-const y T)\
       (assert (= x C))(assert (= x y))(assert (not (= y x)))";
  ] in
  List.iter (fun (name, source) ->
      let assertions, proof = unsat source in
      let doc, schema = B.marshal_with_datatypes assertions proof in
      require (schema.S.cases <> [] && S.valid schema) ("invalid sorted schema: " ^ name);
      if name = "exhaustiveness" || name = "exhaustiveness-three" then (
        let last = List.hd (List.rev doc.P.assertions) in
        let premises = List.filter (fun e -> e <> last) doc.P.assertions in
        let tester, subject = match last with
          | A.App (_, [A.App (f, [a])]) -> f, a
          | _ -> failwith "expected a negated datatype recognizer" in
        let conclusion = A.App (tester, [subject]) in
        require (Z3SortedDatatype.exhaustiveness_from schema premises conclusion)
          "remaining constructor was not inferred from negative recognizers";
        require (not (Z3SortedDatatype.exhaustiveness_from schema [] conclusion))
          "constructor was inferred without exclusions";
        let other = match subject with
          | A.App (f, []) -> A.App ({ f with A.decl_name = f.A.decl_name ^ ":other" }, [])
          | _ -> failwith "expected a nullary datatype subject" in
        require (not (Z3SortedDatatype.exhaustiveness_from schema premises (A.App (tester, [other]))))
          "constructor exclusions were transferred to another subject";
        let conclusion = A.App (tester, [other]) in
        let equation = R.mk_eq_expr subject other in
        List.iter (fun facts ->
          require (DT.consequence schema facts conclusion)
            "constructor exclusions were not transported across equality")
          [equation :: premises; List.rev (R.mk_eq_expr other subject :: premises)];
        require (not (DT.consequence schema premises conclusion))
          "constructor exclusions were transported without equality";
        let fake_equation = match equation with
          | A.App (f, args) -> A.App ({ f with A.interp = None }, args)
          | _ -> failwith "expected an equality" in
        require (not (DT.consequence schema (fake_equation :: premises) conclusion))
          "an uninterpreted equality lookalike transported exclusions";
        let fake_premises = List.map (function
          | A.App (f, args) -> A.App ({ f with A.interp = None }, args)
          | e -> e) premises in
        require (not (DT.consequence schema (equation :: fake_premises) conclusion))
          "uninterpreted negation lookalikes excluded constructors";
        let unrelated = match other with
          | A.App (f, []) -> A.App ({ f with A.decl_name = f.A.decl_name ^ ":unrelated" }, [])
          | _ -> failwith "expected a nullary datatype subject" in
        require (not (DT.consequence schema
          (R.mk_eq_expr subject unrelated :: premises) conclusion))
          "an unrelated equality transported constructor exclusions";
        let case = match S.find_recognizer tester schema.S.cases with
          | Some c -> c
          | None -> failwith "missing recognizer case" in
        let negative = R.mk_not_expr (A.App (tester, [subject])) in
        let witness = A.App (case.S.constructor, []) in
        List.iter (fun facts ->
          require (DT.consequence schema facts R.false_expr)
            "constructor equality did not conflict with its negative recognizer")
          [[negative; R.mk_eq_expr witness subject];
           [R.mk_eq_expr subject witness; negative]];
        require (not (DT.consequence schema [negative] R.false_expr))
          "a negative recognizer conflicted without constructor equality";
        require (not (DT.consequence schema [R.mk_eq_expr witness subject] R.false_expr))
          "constructor equality conflicted without a negative recognizer";
        let alternative = List.find (fun c -> c.S.constructor <> case.S.constructor) schema.S.cases in
        require (not (DT.consequence schema
          [negative; R.mk_eq_expr (A.App (alternative.S.constructor, [])) subject] R.false_expr))
          "a constructor conflicted with a different negative recognizer";
        if name = "exhaustiveness-three" then
          (require (not (DT.exhaustiveness_from schema [List.hd premises]
            (A.App (tester, [subject]))))
            "constructor was inferred without excluding every alternative";
           require (not (DT.consequence schema [equation; List.hd premises] conclusion))
             "equality transport ignored an unexcluded third constructor"));
      if name = "reconstruction" then (
        match doc.P.assertions with
        | [guard; A.App (_, [A.App (_, [subject; witness])])] ->
          require (DT.consequence schema
            [R.mk_not_expr guard; R.mk_eq_expr witness subject] R.false_expr)
            "a non-nullary constructor equality did not conflict with its negative recognizer"
        | _ -> failwith "expected a recognizer and negated reconstruction equality");
      let result = K.check_document schema doc in
      require (result = Some Z.zero)
        ("sorted datatype proof remained unchecked: " ^ name ^
         (match result with None -> " (rejected)" | Some n -> " (pending " ^ Z.to_string n ^ ")"));
      require (K.diagnostic_result (K.diagnose_document schema doc) = result)
        ("sorted diagnostics disagree: " ^ name);
      List.iter (fun fixture ->
          let actual, diagnostic = K.check_document_diagnosed schema fixture in
          require (actual = K.check_document schema fixture &&
                   diagnostic = K.diagnose_document schema fixture)
            ("single-pass sorted checking changed a verdict or diagnostic: " ^ name))
        [doc;
         { doc with P.assertions = [] };
         { doc with P.root = Z.minus_one };
         { doc with P.entries = [
             { P.rule = U.Unverified "th-lemma"; formula = Z3ResolutionProofTheory.false_expr;
               premise_ids = [] }]; root = Z.zero }];
      require (K.check_document schema { doc with P.assertions = [] } <> Some Z.zero)
        ("sorted checker ignored original input binding: " ^ name);
      require (K.check_document schema { doc with P.entries = [
        { P.rule = U.Hypothesis; formula = Z3ResolutionProofTheory.false_expr; premise_ids = [] }];
        root = Z.zero } = None) "sorted checker admitted an open root hypothesis";
      require (K.check_document schema { doc with P.entries = [
        { P.rule = U.Unverified "th-lemma"; formula = Z3ResolutionProofTheory.false_expr;
          premise_ids = [] }]; root = Z.zero } = Some Z.one)
        "sorted checker treated an unsupported claim as certified";
      let omitted = { schema with S.cases = List.tl schema.S.cases } in
      require (K.check_document omitted doc <> Some Z.zero)
        ("sorted checker accepted an incomplete referenced signature: " ^ name)) samples;
  require (N.solve
      "(declare-datatype T ((C (field Int)) (D (other Int))))\
       (assert (not (= (field (D 0)) (field (D 1)))))" Z.zero = N.Sat)
    "wrong-constructor selectors were incorrectly forced to a shared default"

let sorted_integer_farkas () =
  let module K = Z3SortedProof in
  let module AR = Z3SortedArithmetic in
  let module R = Z3ResolutionProofTheory in
  let c = context () in
  let native = parse c
    "(declare-datatype T ((C (field Int))))(declare-const t T)\
     (declare-const r Real)(declare-const p Bool)\
     (assert (> (field t) 0))(assert (< (field t) 1))\
     (assert (> r 0.0))(assert (< r 0.0))(assert p)\
     (assert (<= (field t) 0))(assert (>= (field t) 0))" in
  let st = B.marshal_expressions (B.empty_state ()) native in
  let schema = N.view_datatypes st.B.retained_sorts in
  let expressions = List.map (B.cached_expression st) native in
  let x, y, real_x, real_y, p, le, ge = match expressions with
    | [x; y; real_x; real_y; p; le; ge] -> x, y, real_x, real_y, p, le, ge
    | _ -> failwith "expected integer Farkas regression formulas" in
  let one = Z.one, Z.one in
  let zero = Z.zero, Z.one in
  let check expected formulas weights =
    require (AR.check_contradiction formulas weights = expected)
      "unexpected sorted integer Farkas certificate verdict" in
  check true [true, x; true, y] [one; one];
  check true [true, x; true, y] [Z.one, Z.of_int 2; Z.one, Z.of_int 2];
  check false [true, x; true, y] [one; zero];
  check false [true, x; true, y] [one];
  check false [true, x; true, y] [one; one; one];
  check false [true, real_x; true, real_y] [one; one];
  check true [true, x; true, y; true, real_x; false, p] [one; one; zero; zero];
  check false [true, le; true, ge] [one; one];
  let fake = match x with
    | A.App (f, args) -> A.App ({ f with A.interp = None }, args)
    | _ -> failwith "expected an integer comparison" in
  check false [true, fake; true, y] [one; one];
  check false (List.init 5000 (fun _ -> true, p)) (List.init 5000 (fun _ -> zero));
  (* polarity: the negated strict lower bound (field t) <= 0 with (field t) < 1 is satisfiable *)
  check false [false, x; true, y] [one; one];
  (* cancellation: (field t) > 0 and (field t) <= 0 sum to 0 > 0 *)
  check true [true, x; true, le] [one; one];
  (* the 4096-node expression budget, at its boundary: x and y have 4 nodes each, p one *)
  let padded n = [true, x; true, y] @ List.init n (fun _ -> true, p) in
  let padded_weights n = [one; one] @ List.init n (fun _ -> zero) in
  check true (padded 4088) (padded_weights 4088);
  check false (padded 4089) (padded_weights 4089);
  let fact formula =
    { U.conclusion = Option.get (U.classify_fact formula); hypotheses = [p] } in
  let node =
    { U.kind = U.ArithmeticFarkas [one; one];
      conclusion = Option.get (U.classify_fact R.false_expr);
      premises = [fact x; fact y] } in
  require (K.arithmetic_farkas node) "typed Farkas dispatch did not replay the certificate";
  (match K.check_node schema [] node with
   | Some (result, pending) ->
       require (Z.equal pending Z.zero && result.U.hypotheses = [p])
         "typed Farkas lost inherited hypotheses or retained an obligation"
   | None -> failwith "typed Farkas rejected well-sorted premises");
  let fake_or = A.App
    ({ A.decl_name = "or"; domain = [A.bool_sort; A.bool_sort];
       range = A.bool_sort; interp = None; int_params = [] }, [le; ge]) in
  require (not (K.arithmetic_farkas
    { node with U.conclusion = Option.get (U.classify_fact fake_or); premises = [] }))
    "typed Farkas treated an uninterpreted or lookalike as a clause";
  (* signed conclusion literals: a negated literal of the conclusion is assumed positive, from one premise
     or from a canonical two-literal clause with no premise *)
  let negated e = R.mk_not_expr e in
  require (K.arithmetic_farkas
    { node with U.conclusion = Option.get (U.classify_fact (negated y)); premises = [fact x] })
    "typed Farkas ignored a negated conclusion literal";
  let clause = A.App
    ({ A.decl_name = "or"; domain = [A.bool_sort; A.bool_sort];
       range = A.bool_sort; interp = Some Z3ValueTheory.op_or; int_params = [] }, [negated x; negated y]) in
  require (K.arithmetic_farkas
    { node with U.conclusion = Option.get (U.classify_fact clause); premises = [] })
    "typed Farkas ignored the literals of a conclusion clause";
  require (not (K.arithmetic_farkas
    { node with U.conclusion = Option.get (U.classify_fact y); premises = [fact x] }))
    "typed Farkas accepted a positive conclusion literal as an assumption"

let sorted_epsilon_skolemization () =
  let module K = Z3SortedProof in
  let module E = Z3SortedSkolem in
  let module R = Z3ResolutionProofTheory in
  let declarations =
    "(declare-datatype T ((C (field Int))))\
     (declare-fun p (Int Int) Bool)(declare-fun q (T Int) Bool)\
     (declare-const c Int)(declare-const h Int)(declare-const t T)\
     (declare-fun k (Int) Int)" in
  let fixture left right =
    let c = context () in
    let native = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) native in
    let schema = N.view_datatypes st.B.retained_sorts in
    let a, b = match B.cached_expression st (List.hd native) with
      | A.App (_, [a; b]) -> a, b
      | _ -> failwith "expected a Skolem test equation" in
    let entry = { P.rule = U.Skolemization;
      formula = Z3ObservationalEquality.mk_oeq_expr a b; premise_ids = [] } in
    let doc = { P.declarations = []; expressions = [a; b]; assertions = [R.false_expr];
      entries = [entry; { P.rule = U.Asserted; formula = R.false_expr; premise_ids = [] }];
      root = Z.one } in
    schema, doc, entry, a, b in
  let cases = [
    "(exists ((x Int)) (p x x))", "(p c c)", true;
    "(not (forall ((x Int)) (p x x)))", "(not (p c c))", true;
    "(not (forall ((x Int)) (not (p x x))))", "(p c c)", true;
    "(exists ((x T) (y Int)) (q x y))", "(q t c)", true;
    "(exists ((x Int) (y Int)) (not (= x y)))", "(not (= c h))", true;
    "(exists ((x Int) (unused T)) (p x x))", "(p c c)", true;
    "(exists ((x Int)) (forall ((y Int)) (p x y)))",
      "(forall ((y Int)) (p c y))", true;
    "(exists ((x Int)) (p x x))", "(p c h)", false;
    "(exists ((x Int) (y Int)) (not (= x y)))", "(not (= c c))", false;
    "(exists ((x Int)) (p x c))", "(p c c)", false;
    "(forall ((x Int)) (p x x))", "(p c c)", false;
    "(not (forall ((x Int)) (p x x)))", "(p c c)", false;
    "(exists ((x Int)) (p x h))", "(p (k h) h)", false;
  ] in
  List.iter (fun (left, right, expected) ->
    let schema, doc, entry, a, b = fixture left right in
    let ds = K.epsilon_context schema doc in
    require (K.epsilon_entry schema ds entry = expected)
      ("incorrect typed epsilon eligibility: " ^ left ^ " -> " ^ right);
    let result, diagnostic = K.check_document_epsilon_diagnosed schema doc in
    require (result = K.check_document_epsilon schema doc &&
             diagnostic = K.diagnose_document_epsilon schema doc)
      "typed epsilon checking and diagnostics disagree";
    if expected then (
      require (K.check_document schema doc = Some Z.one && result = Some Z.zero)
        "typed epsilon did not discharge precisely the isolated Skolem obligation";
      require (K.epsilon_context schema
        { doc with P.assertions = R.mk_eq_expr b b :: doc.P.assertions } = [])
        "typed epsilon reused a witness already present in original inputs";
      require (not (K.epsilon_entry schema ds { entry with P.premise_ids = [Z.zero] }))
        "typed epsilon ignored an unexpected premise";
      require (not (K.epsilon_entry schema ds { entry with P.formula = R.mk_eq_expr a b }))
        "typed epsilon admitted an ordinary equality lookalike";
      let conflicting = List.hd ds in
      require (not (E.eligible schema
        { conflicting with Z3Skolemization.dependencies = [Z.zero, A.BaseSort "Int"] }))
        "typed epsilon admitted a dependency-bearing certificate"))
    cases;
  let schema, doc, entry, _, _ = fixture
    "(exists ((x Int)) (p x x))" "(p c c)" in
  let _, _, conflict, _, _ = fixture
    "(exists ((x Int)) (not (p x x)))" "(not (p c c))" in
  require (K.epsilon_context schema { doc with P.entries = entry :: conflict :: doc.P.entries } = [])
    "incompatible typed choice equations shared a witness";
  require (List.length (K.epsilon_context schema { doc with P.entries = entry :: doc.P.entries }) = 1)
    "duplicate identical typed choice equations were rejected";
  let schema, doc, first, _, _ = fixture "(exists ((x Int)) (= x h))" "(= c h)" in
  let _, _, second, _, _ = fixture "(exists ((x Int)) (= x c))" "(= h c)" in
  require (K.epsilon_context schema { doc with P.entries = [first; second] } = [])
    "cyclic typed choice equations were admitted";
  List.iter (fun source ->
    let assertions, proof = unsat source in
    let doc, schema = B.marshal_with_datatypes assertions proof in
    require (schema.Z3DatatypeSignature.cases <> []) "native epsilon test omitted datatypes";
    require (K.epsilon_context schema doc <> []) "native epsilon test omitted a closed choice block";
    let before, after = K.diagnose_document schema doc, K.diagnose_document_epsilon schema doc in
    match before, after with
    | P.DocumentChecked (old_pending, old_unmet), P.DocumentChecked (pending, unmet) ->
      let sk = List.fold_left (fun n obligation ->
        if obligation.P.obligation_rule = U.Skolemization
        then Z.add n obligation.P.obligation_count else n) Z.zero old_unmet in
      require (Z.sign sk > 0 && Z.equal (Z.add pending sk) old_pending &&
               List.for_all (fun obligation -> obligation.P.obligation_rule <> U.Skolemization) unmet)
        ("native typed epsilon did not discharge its Skolem steps: " ^ source)
    | _ -> failwith "native typed epsilon rejected a previously checkable proof")
    [
      "(declare-datatype T ((C (field Int))))(declare-fun p (T) Bool)\
       (assert (exists ((x T)) (p x)))(assert (forall ((x T)) (not (p x))))";
      "(declare-datatype T ((C (field Int))))(declare-fun p (T) Bool)(declare-fun q (T) Bool)\
       (assert (not (forall ((x T)) (p x))))(assert (forall ((x T)) (q x)))\
       (assert (forall ((x T)) (=> (q x) (p x))))";
    ];
  let assertions, proof = unsat
    "(declare-fun p (Int) Bool)(assert (exists ((x Int)) (p x)))\
     (assert (forall ((x Int)) (not (p x))))" in
  let doc, schema = B.marshal_with_datatypes assertions proof in
  require (K.epsilon_context schema doc <> [] &&
           K.check_document_epsilon schema doc = Some Z.zero)
    "native typed integer epsilon refutation was not fully certified"

(* Readable output on the epsilon route. The elaborated document keeps one entry per ORIGINAL entry (a used Skolem step only
   changes its rule label to Asserted, and every choice equation is appended to the assertions), so an obligation or a
   rejected entry names the same original entry and premise ids; an assertion-stage rejection carries no index at all. The
   report is rendered from the one diagnosed check, which equals the plain epsilon check. *)
let readable_epsilon_provenance () =
  let module K = Z3SortedProof in
  let module R = Z3NativeMain.Readable in
  let module RT = Z3ResolutionProofTheory in
  let contains text needle =
    let n = String.length needle in
    let rec from i = i + n <= String.length text && (String.sub text i n = needle || from (i + 1)) in
    from 0 in
  let c = context () in
  let native = parse c
    "(declare-fun p (Int Int) Bool)(declare-const c Int)\
     (assert (= (exists ((x Int)) (p x x)) (p c c)))" in
  let st = B.marshal_expressions (B.empty_state ()) native in
  let schema = N.view_datatypes st.B.retained_sorts in
  let a, b = match B.cached_expression st (List.hd native) with
    | A.App (_, [a; b]) -> a, b
    | _ -> failwith "expected a Skolem test equation" in
  let skolem = { P.rule = U.Skolemization; formula = Z3ObservationalEquality.mk_oeq_expr a b; premise_ids = [] } in
  let document entries = { P.declarations = []; expressions = [a; b]; assertions = [RT.false_expr];
                           entries; root = Z.one } in
  let diagnosed doc =
    let result, diagnostic = K.check_document_epsilon_diagnosed schema doc in
    require (result = K.check_document_epsilon schema doc && diagnostic = K.diagnose_document_epsilon schema doc)
      "epsilon check and diagnosis disagree";
    result, diagnostic, R.report_text 1 (Z3NativeMain.result_text result) doc diagnostic in
  (* an open step after the used Skolem step: its obligation names original entry 1 and its premise #0 *)
  let doc = document [skolem; { P.rule = U.Unverified "open-step"; formula = RT.false_expr; premise_ids = [Z.zero] }] in
  require (K.epsilon_context schema doc <> []) "the provenance fixture lost its choice block";
  let result, diagnostic, text = diagnosed doc in
  (match diagnostic with
   | P.DocumentChecked (pending, [obligation]) ->
       require (result = Some Z.one && Z.equal pending Z.one && Z.equal obligation.P.obligation_index Z.one &&
                obligation.P.obligation_rule = U.Unverified "open-step")
         "the epsilon obligation does not name its original entry"
   | _ -> failwith "expected exactly one open step after epsilon elaboration");
  require (contains text "\tnode=1\t" && contains text "  node 1: premises: #0\n")
    "readable epsilon output lost the original node or premise ids";
  require (not (contains text "no source-node mapping")) "readable epsilon output dropped a valid source mapping";
  (* an ill-scoped entry after the used Skolem step is rejected at its own original index *)
  let doc = document [skolem; { P.rule = U.Unverified "bad"; formula = A.Var (Z.zero, A.bool_sort); premise_ids = [] }] in
  let result, diagnostic, text = diagnosed doc in
  (match diagnostic with
   | P.DocumentRejected (P.ProofEntry, Some index, _) ->
       require (result = None && Z.equal index Z.one) "the epsilon rejection does not name its original entry"
   | _ -> failwith "expected a proof-entry rejection after epsilon elaboration");
  require (contains text "  node 1: rule=bad premises: none\n") "readable epsilon rejection lost its original entry";
  (* a rejected original assertion is reported without any index (never an appended choice equation's) *)
  let doc = { (document [skolem; { P.rule = U.Asserted; formula = RT.false_expr; premise_ids = [] }])
              with P.assertions = [A.Var (Z.zero, A.bool_sort)] } in
  let result, diagnostic, text = diagnosed doc in
  require (result = None && diagnostic = P.DocumentRejected (P.OriginalAssertions, None, None))
    "an epsilon assertion-stage rejection carried an index";
  require (contains text "\tstage=original-assertions\tindex=-\n" && not (contains text "  node "))
    "readable epsilon assertion rejection attached a node"

let sorted_quantifier_rewrites () =
  let module K = Z3SortedProof in
  let module S = Z3DatatypeSignature in
  let c = context () in
  let declarations =
    "(declare-datatype T ((C (field Int)) (D)))\
     (declare-fun P (T) Bool)(declare-fun Q (T Int) Bool)\
     (declare-fun box (Bool) T)\
     (declare-fun mix (Int Bool) T)\
     (declare-fun fakeEq (Int Int) Bool)\
     (declare-fun fakeAdd (Int Int) Int)\
     (declare-fun fakeIte (Bool T T) T)\
     (declare-fun fake (Bool Bool) Bool)" in
  let check expected left right =
    let native = List.hd (parse c
      (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))")) in
    let st = B.marshal_expressions (B.empty_state ()) [native] in
    let schema = N.view_datatypes st.B.retained_sorts in
    require (S.valid schema && schema.S.cases <> [])
      "sorted quantifier regression did not retain its datatype signature";
    let formula = B.cached_expression st native in
    let conclusion = Option.get (U.classify_fact formula) in
    List.iter (fun kind ->
      let result = K.check_node schema []
        { U.kind; conclusion = conclusion; premises = [] } in
      let checked = match result with
        | Some (_, pending) -> Z.equal pending Z.zero
        | None -> failwith "sorted quantifier checker rejected a well-sorted equality" in
      require (checked = expected)
        ("unexpected sorted quantifier rewrite: " ^ left ^ " -> " ^ right))
      [U.RewriteRule; U.QuantifierIntroduction {
        U.binder_entries = []; binder_root = Z.minus_one }];
    (match formula with
     | A.App (f, args) ->
         require (not (K.consequence schema [] (A.App ({ f with A.interp = None }, args))))
           "an uninterpreted equality lookalike justified a quantifier rewrite"
     | _ -> failwith "expected a quantified equality")
  in
  check true
    "(forall ((x T) (y Int)) (=> (P x) (Q x y)))"
    "(forall ((x T) (y Int)) (or (Q x y) (not (P x))))";
  check true
    "(exists ((x T)) (not (and (P x) (Q x 0))))"
    "(exists ((x T)) (or (not (P x)) (not (Q x 0))))";
  check true
    "(lambda ((x T)) (=> (P x) (Q x 0)))"
    "(lambda ((x T)) (or (not (P x)) (Q x 0)))";
  check true
    "(forall ((x T)) (= (box (and (P x) (Q x 0))) x))"
    "(forall ((x T)) (= (box (not (or (not (P x)) (not (Q x 0))))) x))";
  check true
    "(forall ((x T)) (exists ((y Int)) (= (box (and (P x) (Q x y))) x)))"
    "(forall ((x T)) (exists ((y Int)) (= (box (not (or (not (P x)) (not (Q x y))))) x)))";
  check true
    "(lambda ((x T)) (box (and (P x) (Q x 0))))"
    "(lambda ((x T)) (box (not (or (not (P x)) (not (Q x 0))))))";
  check true
    "(forall ((x T)) (exists ((y Int)) (= 346 (field x))))"
    "(forall ((x T)) (exists ((y Int)) (= (field x) 346)))";
  check true
    "(forall ((x T) (y Real)) (= 1.0 y))"
    "(forall ((x T) (y Real)) (= y 1.0))";
  check true
    "(forall ((x T)) (=> (P x) (forall ((y Int)) (= 7 (field x)))))"
    "(forall ((x T)) (or (forall ((y Int)) (= (field x) 7)) (not (P x))))";
  check true
    "(forall ((x T)) (not (and (P x) (exists ((y Int)) (= 7 (field x))))))"
    "(forall ((x T)) (or (not (P x)) (not (exists ((y Int)) (= (field x) 7)))))";
  check true
    "(forall ((x T)) (= (P x) (forall ((y Int)) (= 7 (field x)))))"
    "(forall ((x T)) (= (forall ((y Int)) (= (field x) 7)) (P x)))";
  check false
    "(forall ((x T)) (=> (P x) (forall ((y Int)) (=> (Q x y) (forall ((z Int)) (= 7 (field x)))))))"
    "(forall ((x T)) (or (forall ((y Int)) (or (forall ((z Int)) (= (field x) 7)) (not (Q x y)))) (not (P x))))";
  let rec duplicate depth body =
    if depth = 0 then body
    else duplicate (depth - 1) ("(let ((p " ^ body ^ ")) (and p p))")
  in
  let large_body = duplicate 8 "(forall ((y Int)) (= 7 (field x)))" in
  check false
    ("(forall ((x T)) " ^ large_body ^ ")")
    "(forall ((x T)) (forall ((y Int)) (= (field x) 7)))";
  check true
    ("(forall ((x T)) (=> (P x) " ^ large_body ^ "))")
    ("(forall ((x T)) (or (not (P x)) " ^ large_body ^ "))");
  check false
    "(forall ((x T)) (= (P x) (forall ((y Int)) (= 7 (field x)))))"
    "(forall ((x T)) (= (forall ((y Int)) (= (field x) 8)) (P x)))";
  check true
    "(lambda ((x T)) (ite (P x) x D))"
    "(lambda ((x T)) (ite (not (P x)) D x))";
  check true
    "(lambda ((x T)) (ite (and (P x) (Q x 0)) x D))"
    "(lambda ((x T)) (ite (or (not (P x)) (not (Q x 0))) D x))";
  check false
    "(forall ((x T)) (= 346 (field x)))"
    "(forall ((x T)) (= (field x) 347))";
  check false
    "(forall ((x T)) (=> (P x) (forall ((y Int)) (= 7 (field x)))))"
    "(forall ((x T)) (or (forall ((y Int)) (= (field x) 8)) (not (P x))))";
  check false
    "(lambda ((x T)) (ite (P x) x D))"
    "(lambda ((x T)) (ite (not (P x)) x D))";
  check false
    "(lambda ((x T)) (ite (P x) x D))"
    "(lambda ((x T)) (ite (not (Q x 0)) D x))";
  check false
    "(forall ((x T)) (fakeEq 346 (field x)))"
    "(forall ((x T)) (fakeEq (field x) 346))";
  check false
    "(lambda ((x T)) (fakeIte (P x) x D))"
    "(lambda ((x T)) (fakeIte (not (P x)) D x))";
  check true
    "(forall ((x T)) (= (+ (field x) 0) 7))"
    "(forall ((x T)) (= (field x) 7))";
  check true
    "(lambda ((x T)) (+ (field x) 0))"
    "(lambda ((x T)) (field x))";
  check true
    "(forall ((x T) (y Int)) (= (+ (field x) y) 7))"
    "(forall ((x T) (y Int)) (= (+ y (field x)) 7))";
  check true
    "(forall ((x T) (y Int)) (>= (field x) y))"
    "(forall ((x T) (y Int)) (>= (+ (field x) (* (- 1) y)) 0))";
  check true
    "(forall ((x T) (y Int)) (not (> (+ (field x) 3) y)))"
    "(forall ((x T) (y Int)) (<= (+ (field x) (* (- 1) y)) (- 3)))";
  check true
    "(forall ((x T) (y Int)) (= (* 2 (- (field x) y)) 0))"
    "(forall ((x T) (y Int)) (= (field x) y))";
  check false
    "(forall ((x T) (y Int)) (>= (field x) y))"
    "(forall ((x T) (y Int)) (>= (+ (field x) (* (- 1) y)) 1))";
  check false
    "(forall ((x T) (y Int)) (>= (field x) y))"
    "(forall ((x T) (y Int)) (> (field x) y))";
  check false
    "(lambda ((x T)) (fakeAdd (field x) 0))"
    "(lambda ((x T)) (field x))";
  check false
    "(forall ((x T) (y Real)) (= (+ y 0.0) 7.0))"
    "(forall ((x T) (y Real)) (= y 7.0))";
  check false
    ("(lambda ((x T)) (+ (field x) " ^
      String.concat " " (List.init 256 (fun _ -> "0")) ^ "))")
    "(lambda ((x T)) (field x))";
  let clauses = List.init 30 (fun i ->
    Printf.sprintf "(or (Q x %d) (Q x %d))" (2 * i) (2 * i + 1)) in
  let conjunction xs = "(and " ^ String.concat " " xs ^ ")" in
  check true
    ("(forall ((x T)) " ^ conjunction clauses ^ ")")
    ("(forall ((x T)) " ^ conjunction (List.rev clauses) ^ ")");
  check true
    ("(lambda ((x T)) (mix (+ (field x) 0) " ^ conjunction clauses ^ "))")
    ("(lambda ((x T)) (mix (field x) " ^ conjunction (List.rev clauses) ^ "))");
  check false
    "(forall ((x T)) (= (box (and (P x) (Q x 0))) x))"
    "(forall ((x T)) (= (box (or (P x) (Q x 0))) x))";
  check false "(forall ((x T)) (P x))" "(forall ((x T)) (not (P x)))";
  check false "(forall ((x T)) (P x))" "(exists ((x T)) (P x))";
  check false "(forall ((x T) (y T)) (P x))" "(forall ((x T) (y T)) (P y))";
  check false
    "(forall ((x T)) (fake (P x) (Q x 0)))"
    "(forall ((x T)) (or (not (P x)) (Q x 0)))"

let sorted_constant_folding () =
  let module K = Z3SortedProof in
  let c = context () in
  let declarations =
    "(declare-datatype T ((C (field Int))))\
     (declare-fun box (Bool) T)(declare-fun mix (Int Bool) T)\
     (declare-fun fakeEq (Int Int) Bool)(declare-fun fakeAdd (Int Int) Int)" in
  List.iter (fun (left, right, expected) ->
    let native = List.hd (parse c
      (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))")) in
    let st = B.marshal_expressions (B.empty_state ()) [native] in
    let schema = N.view_datatypes st.B.retained_sorts in
    require (schema.Z3DatatypeSignature.cases <> [])
      "constant folding regression did not select datatype semantics";
    let conclusion = Option.get (U.classify_fact (B.cached_expression st native)) in
    let result = K.check_node schema []
      { U.kind = U.RewriteRule; conclusion; premises = [] } in
    require (match result with Some (_, pending) ->
        Z.equal pending (if expected then Z.zero else Z.one) | None -> false)
      ("incorrect sorted constant folding: " ^ left ^ " -> " ^ right))
    ["(box (= 12 23))", "(box false)", true;
     "(box (= 12 12))", "(box true)", true;
     "(box (= (+ 12 11) 23))", "(box true)", true;
     "(box true)", "(box (= (* (- 12) 2) (- 24)))", true;
     "(box (= (* 18446744073709551616 18446744073709551616)\
       340282366920938463463374607431768211456))", "(box true)", true;
     "(mix (+ 12 11) (= 12 23))", "(mix 23 false)", true;
     "(box (< (+ 12 11) 23))", "(box false)", true;
     "(box (and (= 12 23) (>= 23 12)))", "(box false)", true;
     "(box (not (= 12 23)))", "(box true)", true;
     "(box (=> (= 12 12) (= 12 23)))", "(box false)", true;
     "(box (= (= 12 23) (< 23 12)))", "(box true)", true;
     "(box (ite (= 12 23) false true))", "(box true)", true;
     "(box (xor (= 12 23) true false))", "(box true)", true;
     "(box (= 12 23))", "(box true)", false;
     "(box (= 12 12))", "(box false)", false;
     "(box (= (+ 12 11) 24))", "(box true)", false;
     "(box (and (= 12 23) (>= 23 12)))", "(box true)", false;
     "(box (fakeEq 12 23))", "(box false)", false;
     "(mix (fakeAdd 12 11) false)", "(mix 23 false)", false]

let sorted_quantifier_flattening () =
  let module K = Z3SortedProof in
  let module Q = Z3SortedQuantifier in
  let declarations =
    "(declare-datatype T ((A) (B)))(declare-const x T)\
     (declare-fun k (Bool Bool) Bool)(declare-fun r (T Bool Int) Bool)" in
  (* An independent small reproducer, not a copy of the corpus input. *)
  let assertions, proof = unsat (declarations ^
    "(assert (forall ((p Bool)) (forall ((q Bool)) (= (k p q) p))))\
     (assert (k (= x A) true))(assert (not (= x A)))") in
  let doc, schema = B.marshal_with_datatypes assertions proof in
  let pulls = List.filter (fun e -> e.P.rule = U.PullQuantifier) doc.P.entries in
  require (schema.Z3DatatypeSignature.cases <> [] && pulls <> [])
    "flattening regression did not exercise the sorted pull-quant path";
  require (K.check_document schema doc = Some Z.zero)
    "sorted universal flattening remained an obligation";
  require (K.diagnostic_result (K.diagnose_document schema doc) = Some Z.zero)
    "sorted flattening diagnostics disagree";
  List.iter (fun e ->
      require (e.P.premise_ids = [] && Q.check_flatten e.P.formula)
        "native pull-quant did not have the expected binder certificate";
      match e.P.formula with
      | A.App (_, [A.Quantifier (A.Forall_k, outer, _,
          A.Quantifier (A.Forall_k, inner, _, body));
          A.Quantifier (A.Forall_k, combined, _, body')]) ->
          require (outer = [A.bool_sort] && inner = [A.bool_sort] &&
                   combined = outer @ inner && body = body')
            "native Boolean binder blocks or body changed"
      | _ -> failwith "unexpected native pull-quant shape") pulls;
  let c = context () in
  let check expected left right =
    let native = List.hd (parse c
      (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))")) in
    let st = B.marshal_expressions (B.empty_state ()) [native] in
    let formula = B.cached_expression st native in
    require (Q.check_flatten formula = expected)
      ("incorrect flattening certificate: " ^ left ^ " -> " ^ right);
    let node = { U.kind = U.PullQuantifier;
      conclusion = Option.get (U.classify_fact formula); premises = [] } in
    let accepted = function Some (_, pending) -> Z.equal pending Z.zero | None -> false in
    require (accepted (K.check_node schema [] node) = expected)
      "sorted node dispatch disagrees with flattening check";
    match formula with
    | A.App (f, args) ->
        require (not (Q.check_flatten (A.App ({ f with A.interp = None }, args))))
          "uninterpreted equality lookalike justified flattening"
    | _ -> failwith "expected equality in flattening fixture"
  in
  check true
    "(forall ((a T)) (forall ((b Bool) (n Int)) (r a b n)))"
    "(forall ((a T) (b Bool) (n Int)) (r a b n))";
  check true
    "(forall ((a T) (b Bool) (n Int)) (r a b n))"
    "(forall ((a T)) (forall ((b Bool) (n Int)) (r a b n)))";
  check true
    "(forall ((a T)) (forall ((b Bool) (n Int)) (exists ((z T)) (r z b n))))"
    "(forall ((a T) (b Bool) (n Int)) (exists ((z T)) (r z b n)))";
  check false
    "(forall ((a T)) (forall ((b Bool) (n Int)) (r a b n)))"
    "(forall ((b Bool) (n Int) (a T)) (r a b n))";
  check false
    "(forall ((p Bool)) (forall ((q Bool)) (= (k p q) p)))"
    "(forall ((p Bool) (q Bool)) (= (k q p) q))";
  check false
    "(forall ((a T)) (exists ((b Bool) (n Int)) (r a b n)))"
    "(forall ((a T) (b Bool) (n Int)) (r a b n))";
  let malformed = List.map (fun e ->
      if e.P.rule = U.PullQuantifier then { e with P.formula =
        Z3ResolutionProofTheory.mk_eq_expr
          (A.Quantifier (A.Forall_k, [A.bool_sort], A.bool_sort,
            A.Quantifier (A.Forall_k, [A.bool_sort], A.bool_sort,
              A.Var (Z.of_int 2, A.bool_sort))))
          (A.Quantifier (A.Forall_k, [A.bool_sort; A.bool_sort], A.bool_sort,
            A.Var (Z.of_int 2, A.bool_sort))) }
      else e) doc.P.entries in
  require (K.check_document schema { doc with P.entries = malformed } = None)
    "escaping flattening binders were accepted"

let sorted_quantifier_instances () =
  let module K = Z3SortedProof in
  let module Q = Z3SortedQuantifier in
  let declarations =
    "(declare-datatype T ((C (field Int)) (D)))\
     (declare-fun P (T) Bool)(declare-fun Q (T Int) Bool)\
     (declare-fun R (T T) Bool)" in
  let sources = [
    "(assert (forall ((x T)) (P x)))(assert (not (P D)))";
    "(assert (forall ((x T) (n Int)) (Q x n)))(assert (not (Q D 7)))";
    "(assert (forall ((x T) (y T)) (R x y)))(assert (not (R D (C 7))))";
    "(assert (forall ((x T) (n Int)) (=> (P x) (Q x n))))\
     (assert (P (C 3)))(assert (not (Q (C 3) 7)))"
  ] in
  List.iter (fun source ->
      let assertions, proof = unsat (declarations ^ source) in
      let doc, schema = B.marshal_with_datatypes assertions proof in
      require (schema.Z3DatatypeSignature.cases <> [])
        "sorted instantiation regression omitted its datatype signature";
      let instances = List.filter_map (fun e -> match e.P.rule with
          | U.QuantifierInstantiation args -> Some (args, e.P.formula)
          | _ -> None) doc.P.entries in
      require (instances <> []) "sorted proof omitted instantiation parameters";
      require (K.check_document schema doc = Some Z.zero)
        ("sorted quantifier instance remained unchecked: " ^ source);
      require (K.diagnostic_result (K.diagnose_document schema doc) = Some Z.zero)
        "sorted instantiation diagnostics disagree";
      List.iter (fun (args, formula) ->
          require (Q.check args formula) "typed quantifier substitution was not checked";
          require (not (Q.check [] formula)) "missing typed bindings were trusted";
          require (not (Q.check (args @ args) formula)) "extra typed bindings were trusted";
          require (not (Q.check
            (List.map (fun a -> A.Var (Z.zero, A.get_sort a)) args) formula))
            "escaping typed substitution variables were trusted";
          if List.length args > 1 then
            require (not (Q.check (List.rev args) formula))
              "typed de Bruijn binding order was ignored";
          match formula with
          | A.App (f, [A.App (n, [A.Quantifier (_, bs, t, body)]) as negative; inst]) ->
              require (not (Q.check args (A.App ({ f with A.interp = None },
                [negative; inst]))))
                "an uninterpreted disjunction lookalike was trusted";
              require (not (Q.check args (A.App (f,
                [A.App ({ n with A.interp = None },
                   [A.Quantifier (A.Forall_k, bs, t, body)]); inst]))))
                "an uninterpreted negation lookalike was trusted";
              require (not (Q.check args (A.App (f,
                [negative; Z3ResolutionProofTheory.false_expr]))))
                "an incorrect typed instance was trusted";
              require (not (Q.check args (A.App (f,
                [A.App (n, [A.Quantifier (A.Exists_k, bs, t, body)]);
                 inst]))))
                "an existential antecedent justified universal instantiation"
          | _ -> failwith "unexpected sorted instantiation clause") instances;
      let entries = List.map (fun e -> match e.P.rule with
          | U.QuantifierInstantiation _ -> { e with P.rule = U.QuantifierInstantiation [] }
          | _ -> e) doc.P.entries in
      require (match K.check_document schema { doc with P.entries = entries } with
        | Some pending -> Z.sign pending > 0 | None -> false)
        "invalid sorted substitutions lost their explicit obligations") sources;
  let check_clause clause arguments expected =
    let c = context () in
    let inputs = parse c (declarations ^ "(assert " ^ clause ^ ")" ^
      String.concat "" (List.map (fun term ->
        "(assert (= " ^ term ^ " " ^ term ^ "))") arguments)) in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match List.map (B.cached_expression st) inputs with
    | formula :: bindings ->
        let args = List.map (function A.App (_, [term; _]) -> term
          | _ -> failwith "malformed sorted test binding") bindings in
        require (Q.check args formula = expected)
          ("unexpected sorted quantifier instance: " ^ clause);
        let schema = N.view_datatypes st.B.retained_sorts in
        let node = { U.kind = U.QuantifierInstantiation args;
          conclusion = Option.get (U.classify_fact formula); premises = [] } in
        require ((match K.check_node schema [] node with
          | Some (_, pending) -> Z.equal pending Z.zero
          | None -> false) = expected)
          ("sorted node dispatch disagrees for nested instantiation: " ^ clause)
    | [] -> failwith "missing sorted instantiation fixture"
  in
  check_clause
    "(or (not (forall ((x T) (b Bool)) (or (P x) b)))\
         (or (P D) (forall ((y T)) (P y))))"
    ["D"; "(forall ((y T)) (P y))"] true;
  check_clause
    "(or (not (forall ((x T)) (exists ((y T)) (R x y))))\
         (exists ((y T)) (R D y)))"
    ["D"] true;
  check_clause
    "(or (not (forall ((x T)) (forall ((y T)) (R x y))))\
         (forall ((y T)) (R D y)))"
    ["D"] true;
  check_clause
    "(or (not (forall ((x T) (n Int))\
                (exists ((y T)) (and (Q x n) (R x y)))))\
         (exists ((y T)) (and (Q D 7) (R D y))))"
    ["D"; "7"] true;
  check_clause
    "(or (not (forall ((x T) (b Bool))\
                (exists ((y T)) (or b (R x y)))))\
         (exists ((y T)) (or (forall ((z T)) (P z)) (R D y))))"
    ["D"; "(forall ((z T)) (P z))"] true;
  check_clause
    "(or (not (forall ((x T)) (exists ((y T)) (R x y))))\
         (exists ((y T)) (R y D)))"
    ["D"] false;
  check_clause
    "(or (not (forall ((x T) (n Int))\
                (exists ((y T)) (and (Q x n) (R x y)))))\
         (exists ((y T)) (and (Q D 7) (R D y))))"
    ["7"; "D"] false

let assumed_nlsat () =
  let c = context () in
  let conclusion = List.hd (parse c "(assert false)") in
  let view = { N.proof_name = "th-lemma"; premises = []; conclusion;
               farkas = None; assumed = Some "nlsat"; lp_data = None;
               binding = None; instantiations = []; ff_pac = None } in
  let rule = B.native_rule view Z3ResolutionProofTheory.false_expr in
  require (rule = U.Unverified "assumed:nlsat")
    "native NLSAT assumption lost its origin";
  let doc = document "(assert false)" in
  let entry = { P.rule = rule; formula = Z3ResolutionProofTheory.false_expr; premise_ids = [] } in
  require (P.check_document { doc with assertions = []; entries = [entry]; root = Z.zero } = Some Z.one)
    "assumed NLSAT lemma was certified without an obligation"

let boolean_constant_resolution () =
  let module R = Z3ResolutionProofTheory in
  let c = context () in
  let native = parse c
      "(declare-const p Bool)(assert (or false false p false (not true)))\
       (assert (not p))(assert true)" in
  let st = B.marshal_expressions (B.empty_state ()) native in
  let formulas = List.map (B.cached_expression st) native in
  let clause, np, truth = match formulas with
    | [clause; np; truth] -> clause, np, truth
    | _ -> failwith "expected Boolean constant fixtures" in
  let p = match clause with
    | A.App (_, [_; _; p; _; _]) -> p
    | _ -> failwith "expected an unsimplified false-padded clause" in
  let view = { N.proof_name = "true-axiom"; premises = [];
               conclusion = List.nth native 2; farkas = None; assumed = None;
               lp_data = None; binding = None; instantiations = []; ff_pac = None } in
  let truth_rule = B.native_rule view truth in
  require (truth_rule = U.DefAxiom && U.check_step truth_rule (U.Holds truth) [])
    "native true-axiom retained an obligation";
  List.iter (fun (left, right) ->
      require (R.complementary left right) "Boolean constants were not complementary")
    [R.true_expr, R.false_expr; R.false_expr, R.true_expr;
     R.true_expr, R.mk_not_expr R.true_expr;
     R.false_expr, R.mk_not_expr R.false_expr];
  require (not (R.complementary R.true_expr R.true_expr) &&
           not (R.complementary R.false_expr R.false_expr))
    "equal Boolean constants were treated as complementary";
  let entry rule formula premise_ids = { P.rule; formula; premise_ids } in
  let entries =
    [entry U.Asserted clause []; entry U.Asserted np [];
     entry truth_rule truth [];
     entry U.UnitResolution p [Z.zero; Z.of_int 2];
     entry U.UnitResolution R.false_expr [Z.of_int 3; Z.one]] in
  let doc = { P.declarations = st.all_declarations; expressions = st.all_expressions;
              assertions = [clause; np]; entries; root = Z.of_int 4 } in
  require (P.check_document doc = Some Z.zero)
    "false-padded native clause did not produce a checked refutation";
  List.iter (fun formula ->
      require (not (U.check_step truth_rule (U.Holds formula) []))
        "a false true-axiom was certified") [p; R.false_expr];
  let bad = List.mapi (fun i e ->
      if i = 3 then { e with P.formula = R.false_expr } else e) entries in
  require (P.check_document { doc with entries = bad } = None)
    "constant resolution dropped a surviving literal"

let integer_division_axioms () =
  let c = context () in
  let check expected clause =
    let source = List.hd (parse c
        ("(declare-const x Int)(declare-const y Int)(assert " ^ clause ^ ")")) in
    let st = B.marshal_expressions (B.empty_state ()) [source] in
    let formula = B.cached_expression st source in
    require (U.checked_theory_lemma (U.Unverified "th-lemma") (U.Holds formula) [] = expected)
      ("incorrect integer division axiom: " ^ clause);
    require (not (U.checked_theory_lemma (U.Unverified "assumed:nlsat") (U.Holds formula) []))
      "division axioms silently trusted an NLSAT origin"
  in
  check true "(or false (= x (+ (* 2 (div x 2)) (mod x 2))))";
  check true "(or (= y 0) (= x (+ (* y (div x y)) (mod x y))))";
  check true "(or false (>= (mod x 2) 0))";
  check true "(or false (<= (mod x 2) 1))";
  check true "(or false (<= (mod x 10000000000000000000000000000000000000000)\
                           9999999999999999999999999999999999999999))";
  check false "(or false (= x (+ (* 0 (div x 0)) (mod x 0))))";
  check false "(or false (= x (+ (* y (div x y)) (mod x y))))";
  check false "(or (= x 0) (= x (+ (* y (div x y)) (mod x y))))";
  check false "(or false (<= (mod x 2) 0))";
  check false "(or false (>= (mod x 2) 1))"

let typed_observations () =
  let c = context () in
  let source = List.hd (parse c "(declare-const x Int)(assert (= x x))") in
  let st = B.marshal_expressions (B.empty_state ()) [source] in
  let x = match B.cached_expression st source with
    | A.App (_, [x; _]) -> x | _ -> failwith "expected equality" in
  let foreign = { N.id = Z.of_int 12345; name = "~"; unique_name = "native-oeq";
                  op = N.Oeq; range = Z3native.mk_bool_sort c;
                  numeral = None; native_kind = Z.zero; parameters = [] } in
  let d, _ = B.marshal_declaration st foreign [x; x] in
  require (d.domain = [A.BaseSort "Int"; A.BaseSort "Int"])
    "non-Boolean observational equality was relabeled";
  let formula = A.App (d, [x; x]) in
  require (U.classify_fact formula = Some (U.Observational (x, x)) &&
           U.check_step U.Reflexivity (U.Observational (x, x)) [])
    "typed observational reflexivity was rejected";
  require (not (U.check_step U.Symmetry (U.Equal (x, x)) [U.Observational (x, x)]))
    "observational evidence became ordinary equality";
  require (U.check_step U.Congruence (U.Equal (x, x)) [U.Observational (x, x)])
    "reflexive congruence rejected a redundant observational premise";
  let malformed = { d with domain = [A.bool_sort; A.bool_sort] } in
  require (U.classify_fact (A.App (malformed, [x; x])) = None)
    "observational declaration accepted mismatched operand sorts";
  let entry = { P.rule = U.Unverified "th-lemma"; formula; premise_ids = [] } in
  let doc = { P.declarations = [d]; expressions = [formula]; assertions = [];
              entries = [entry]; root = Z.zero } in
  require (P.check_document doc = None) "observational root certified a refutation";
  require (P.logical_decl d && not (P.logical_decl { d with interp = None }))
    "observational declaration validation lost the native tag";
  let lambda = A.Quantifier (A.Lambda_k, [A.BaseSort "Int"],
      A.ArraySort ([A.BaseSort "Int"], A.BaseSort "Int"), x) in
  require (P.check_document { doc with declarations = []; expressions = [lambda];
      entries = [{ entry with formula = lambda }] } = None)
    "non-Boolean proof conclusion was certified"

let contextual_boolean_rewrites () =
  let module F = Z3BoundedBoolEquiv in
  let module N = Z3BooleanNormalForm in
  let atom i = F.Atom (A.Var (Z.of_int i, A.bool_sort)) in
  let rec equalities n =
    if n = 0 then atom 0 else F.Eq (equalities (n - 1), atom n) in
  let deep = equalities 48 in
  require (N.forced_pair [] deep = (false, false))
    "unassigned nested equalities acquired a forced truth value";
  require (not (N.forced_polarity [] deep true) &&
           not (N.forced_polarity [] deep false))
    "single-polarity propagation changed unassigned nested equalities";
  require (N.forced_pair (List.init 49 (fun i -> F.Not (atom i))) deep = (true, false))
    "nested equality propagation lost the positive result";
  require (N.forced_pair (atom 48 :: List.init 48 (fun i -> F.Not (atom i))) deep = (false, true))
    "nested equality propagation ignored the changed final input";
  require (N.forced_pair [atom 0; F.Not (atom 0)] (F.Eq (atom 0, atom 0)) = (true, true))
    "paired propagation changed inconsistent-context behavior";
  require (N.clause_tautology (F.Nary (F.Or, [F.Not deep; deep])))
    "deep complementary clause was not certified";
  require (not (N.clause_tautology (F.Nary (F.Or, [F.Not deep; atom 49]))))
    "deep clause mutation became a tautology";
  let module D = Z3SortedDatatype in
  let wide_formula = F.Nary (F.Or, List.init 24 atom) in
  let contextual = F.Eq (
      F.Nary (F.Or, [atom 0; F.Eq (atom 0, wide_formula)]),
      F.Nary (F.Or, [atom 0; F.Not wide_formula])) in
  require (D.propositional contextual && D.bounded_propositional contextual)
    "wide contextual equivalence was incorrectly restricted by its atom count";
  require (not (D.propositional (F.Eq (
      F.Nary (F.Or, [atom 0; F.Eq (atom 0, wide_formula)]),
      F.Nary (F.Or, [atom 0; wide_formula])))))
    "wide contextual mutation was certified";
  let shared = ref (atom 0) in
  for i = 1 to 12 do
    shared := F.Eq (!shared, F.Not !shared)
  done;
  require (D.context_budget (Z.of_int 256) !shared = None)
    "context limit counted shared nodes instead of tree occurrences";
  let large_clause = F.Nary (F.Or, List.init 300 atom) in
  require (D.propositional (F.Eq (
      F.Nary (F.Or, [atom 0; F.Eq (atom 0, large_clause)]),
      F.Nary (F.Or, [atom 0; F.Not large_clause]))))
    "congruence context limit leaked into datatype certificates";
  require (D.propositional (F.Nary (F.Or, [large_clause; F.Not large_clause])))
    "context limit disabled large complementary clauses";
  let reordered = F.Nary (F.Or, List.init 300 (fun i -> atom (299 - i))) in
  require (D.propositional (F.Eq (large_clause, reordered)))
    "context limit disabled large shape equivalences";
  let c = context () in
  let declarations = List.init 24 (fun i ->
      Printf.sprintf "(declare-const p%d Bool)" i) |> String.concat "" in
  let wide = "(or " ^ (List.init 24 (Printf.sprintf "p%d") |> String.concat " ") ^ ")" in
  let check expected left right =
    let inputs = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let conclusion = Option.get (U.classify_fact (B.cached_expression st (List.hd inputs))) in
    require (U.check_step U.RewriteRule conclusion [] = expected)
      ("incorrect contextual Boolean rewrite: " ^ left ^ " -> " ^ right)
  in
  let structural expected left right =
    let inputs = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match B.cached_expression st (List.hd inputs) with
    | A.App (_, [a; b]) ->
        require (Z3BooleanRewrite.structural_boolean_equiv a b = expected)
          ("incorrect complemented equality normalization: " ^ left ^ " -> " ^ right)
    | _ -> failwith "expected Boolean equality"
  in
  structural true ("(= p0 (not " ^ wide ^ "))") ("(not (= " ^ wide ^ " p0))");
  structural true ("(= (not p0) " ^ wide ^ ")") ("(not (= p0 " ^ wide ^ "))");
  structural true ("(= (not p0) (not " ^ wide ^ "))") ("(= " ^ wide ^ " p0)");
  structural false ("(= p0 (not " ^ wide ^ "))") ("(= p0 " ^ wide ^ ")");
  check true ("(and " ^ wide ^ " (not " ^ wide ^ "))") "false";
  check true ("(or " ^ wide ^ " (not " ^ wide ^ "))") "true";
  check true ("(or (not p0) (not (= p0 " ^ wide ^ ")))")
    ("(or (not p0) (not " ^ wide ^ "))");
  check true ("(or p0 (= p0 " ^ wide ^ "))") ("(or p0 (not " ^ wide ^ "))");
  check false ("(or (not p0) (not (= p0 " ^ wide ^ ")))")
    ("(or (not p0) " ^ wide ^ ")");
  check false ("(and " ^ wide ^ " (not p0))") "false";
  check false ("(or " ^ wide ^ " (not p0))") "false";
  let prefix = List.init 23 (Printf.sprintf "p%d") |> String.concat " " in
  let negatives = List.init 23 (fun i -> Printf.sprintf "(not p%d)" i)
    |> String.concat " " in
  check true ("(not (or " ^ prefix ^ " (and " ^ negatives ^ " p23)))")
    ("(not " ^ wide ^ ")");
  check true ("(not (or (and " ^ negatives ^ " p23) " ^ prefix ^ "))")
    ("(not " ^ wide ^ ")");
  check false ("(not (or " ^ prefix ^ " (and " ^ negatives ^ " p23)))")
    ("(not (or " ^ prefix ^ " (not p23)))");
  let a = List.init 11 (fun i -> Printf.sprintf "p%d" (i + 1)) in
  let b = List.init 12 (fun i -> Printf.sprintf "p%d" (i + 12)) in
  let disj xs = "(or " ^ String.concat " " xs ^ ")" in
  let conj xs = "(and " ^ String.concat " " xs ^ ")" in
  let left = "(and (or p0 " ^ disj a ^ ") (or (not p0) " ^ conj b ^ "))" in
  check true left ("(or (and p0 " ^ conj (List.rev b) ^ ") (and (not p0) " ^
      disj (List.rev a) ^ "))");
  check false left ("(or (and p0 " ^ disj (List.rev a) ^ ") (and (not p0) " ^
      conj (List.rev b) ^ "))")

let unused_quantifier_rewrites () =
  let c = context () in
  let check expected declarations left right =
    let inputs = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let conclusion = Option.get (U.classify_fact (B.cached_expression st (List.hd inputs))) in
    require (U.check_step U.RewriteRule conclusion [] = expected)
      ("incorrect unused-binder rewrite: " ^ left ^ " -> " ^ right)
  in
  check true "" "(exists ((x Int) (y Int)) (> x 0))" "(exists ((x Int)) (> x 0))";
  check true "" "(forall ((x Int) (y Real)) (> y 0.0))" "(forall ((y Real)) (> y 0.0))";
  check true "(declare-const p Bool)" "(forall ((x Int) (y Real)) p)" "p";
  check true "(declare-const p Bool)" "p" "(exists ((x Int) (y Real)) p)";
  check true "(declare-fun P (Int Int) Bool)"
    "(forall ((x Int) (y Int)) (forall ((z Int)) (P y z)))"
    "(forall ((y Int)) (forall ((z Int)) (P y z)))";
  check true "" "(exists ((x Int)) (not (exists ((n Int)) (> n 0))))"
    "(not (exists ((n Int)) (> n 0)))";
  check true "(declare-fun P (Int) Bool)"
    "(forall ((x Int)) (exists ((y Int)) (P x)))" "(forall ((x Int)) (P x))";
  (* The unused binder is removed first; the remaining Boolean bodies are then compared. Only the
     quantifier reduction decides an elimination step, so this fixes that comparison. *)
  let eliminate expected left right =
    let declarations = "(declare-const p Bool)(declare-const q Bool)" in
    let inputs = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let conclusion = Option.get (U.classify_fact (B.cached_expression st (List.hd inputs))) in
    require (U.check_step U.ElimUnused conclusion [] = expected)
      ("incorrect unused-binder elimination: " ^ left ^ " -> " ^ right)
  in
  eliminate true "(forall ((x Int)) (or q p))" "(or p q)";
  eliminate true "(or p q)" "(exists ((x Int)) (or q p))";
  eliminate true "(forall ((x Int)) (or q p))" "(or q p)";
  eliminate false "(forall ((x Int)) (or q p))" "(and p q)";
  eliminate false "(or p q)" "(exists ((x Int)) (and q p))";
  check false "(declare-fun P (Int Int) Bool)"
    "(forall ((x Int) (y Int)) (P x y))" "(forall ((x Int)) (P x x))";
  check false "(declare-fun P (Int) Bool)"
    "(forall ((x Int) (y Int)) (P x))" "(exists ((x Int)) (P x))";
  check false "" "(forall ((x Int) (y Int)) (> x 0))" "(forall ((x Real)) (> x 0.0))";
  check false "(declare-fun P (Int Int) Bool)"
    "(forall ((x Int) (y Int)) (exists ((z Int)) (P x z)))"
    "(forall ((x Int)) (exists ((z Int)) (P z z)))";
  let source = A.Quantifier (A.Forall_k, [A.BaseSort "Int"], A.bool_sort,
      A.Var (Z.one, A.bool_sort)) in
  require (U.check_step U.RewriteRule (U.Equal (source, A.Var (Z.zero, A.bool_sort))) [])
    "an outer de Bruijn variable was not lowered";
  require (not (U.check_step U.RewriteRule (U.Equal (source, A.Var (Z.one, A.bool_sort))) []))
    "a free de Bruijn variable retained its old index"

let bv_rewrites () =
  let c = context () in
  let declarations =
    "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)(declare-const s Bool)\
     (declare-const v (_ BitVec 8))\
     (declare-const w (_ BitVec 8))(declare-const z (_ BitVec 8))\
     (declare-const bit (_ BitVec 1))(declare-const other (_ BitVec 1))\
     (declare-const half (_ BitVec 4))\
     (declare-const wide (_ BitVec 65))\
     (declare-const maxwide (_ BitVec 4096))(declare-const too_wide (_ BitVec 4097))" in
  let check expected left right =
    let inputs = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let conclusion = Option.get (U.classify_fact (B.cached_expression st (List.hd inputs))) in
    require (U.check_step U.RewriteRule conclusion [] = expected)
      ("incorrect bit-vector rewrite: " ^ left ^ " -> " ^ right)
  in
  List.iter (fun op ->
      check true ("(" ^ op ^ " v w)") ("(" ^ op ^ " w v)");
      check false ("(" ^ op ^ " v w)") ("(" ^ op ^ " v v)"))
    ["bvand"; "bvor"; "bvxor"; "bvadd"; "bvmul"];
  check false "(bvsub v w)" "(bvsub w v)";
  check true "(bvshl v #x00)" "v";
  check true "(bvlshr v #x00)" "v";
  check true "(bvlshr v (bvneg (bvmul w #x00)))" "v";
  check true "(bvshl #x81 #x01)" "#x02";
  check true "(bvlshr #x81 #x01)" "#x40";
  check true "(bvshl #x01 #x08)" "#x00";
  check true "(bvlshr #xff #xff)" "#x00";
  check true "(bvshl #b1 #b1)" "#b0";
  check true "(bvlshr #b1 #b0)" "#b1";
  check true "(bvshl (_ bv1 65) (_ bv64 65))" "(_ bv18446744073709551616 65)";
  check true "(bvlshr (_ bv18446744073709551616 65) (_ bv64 65))" "(_ bv1 65)";
  check true "(bvshl (_ bv1 65) (_ bv18446744073709551616 65))" "(_ bv0 65)";
  check true "(bvlshr (_ bv1 65) (_ bv18446744073709551616 65))" "(_ bv0 65)";
  check true "(bvshl (_ bv1 4096) (_ bv4096 4096))" "(_ bv0 4096)";
  check false "(bvshl #x81 #x01)" "#x40";
  check false "(bvlshr #x81 #x01)" "#xc0";
  check false "(bvlshr v #x01)" "v";
  check false "(bvlshr (_ bv1 4097) (_ bv0 4097))" "(_ bv1 4097)";
  check true "(concat (concat v w) z)" "(concat v (concat w z))";
  check true "(concat (concat half bit) v)" "(concat half bit v)";
  check true "(concat bit half v)" "(concat bit (concat half v))";
  check false "(concat (concat v w) z)" "(concat v (concat z w))";
  check false "(concat (concat bit half) v)" "(concat half bit v)";
  check false "(bvudiv v w)" "(bvudiv w v)";
  check true "(bvudiv #b1 #b0)" "#b1";
  check true "(bvudiv v #x00)" "#xff";
  check true "(bvurem v #x00)" "v";
  check true "(bvudiv v #x01)" "v";
  check true "(bvurem v #x01)" "#x00";
  check true "(bvudiv #x80 #x03)" "#x2a";
  check true "(bvurem #x80 #x03)" "#x02";
  check true "(bvudiv wide (_ bv0 65))" "(_ bv36893488147419103231 65)";
  check false "(bvudiv v #x00)" "#x00";
  check false "(bvurem v #x00)" "#xff";
  check true "(= (ite p #b1 #b0) #b1)" "p";
  check true "(= (ite p #b0 #b1) #b1)" "(not p)";
  check true "(= (ite p #x12 #x34) #x12)" "p";
  check true "(= #x34 (ite p #x12 #x34))" "(not p)";
  check false "(= (ite p #x12 #x34) #x12)" "(not p)";
  check false "(= (ite p #x12 #x12) #x12)" "p";
  check true "(ite (= bit #b0) #b1 #b0)" "(bvnot bit)";
  check true "(ite (= #b1 bit) #b1 #b0)" "bit";
  check true "(ite (= bit #b1) #b0 #b1)" "(bvnot bit)";
  check true "(ite (= bit #b0) #b0 #b1)" "bit";
  check false "(ite (= v #x00) #b1 #b0)" "(bvnot bit)";
  check true "(= (bvnot bit) #b1)" "(= bit #b0)";
  check true "(= #x12 (bvnot v))" "(= v #xed)";
  check false "(= (bvnot v) #x12)" "(= v #x12)";
  check true "(bvnot (ite p #b1 #b0))" "(ite p #b0 #b1)";
  check true "(bvnot (ite p #x12 #x34))" "(ite p #xed #xcb)";
  check false "(bvnot (ite p #x12 #x34))" "(ite p #x12 #xcb)";
  check true "(= (= bit #b1) p)" "(= bit (ite p #b1 #b0))";
  check true "(= (= bit #b0) p)" "(= (ite p #b0 #b1) bit)";
  check false "(= (= bit #b1) p)" "(= bit (ite p #b0 #b1))";
  check true "(= (= bit #b1) (= other #b0))" "(= bit (bvnot other))";
  check false "(= (= v #xff) (= w #xff))" "(= v w)";
  check true "(bvmul v (bvadd w z))" "(bvadd (bvmul v w) (bvmul v z))";
  check true "(bvadd (bvmul v w) (bvmul v z))" "(bvmul v (bvadd w z))";
  check false "(bvmul v (bvadd w z))" "(bvadd (bvmul v w) (bvmul w z))";
  check false "(bvmul v (bvsub w z))" "(bvadd (bvmul v w) (bvmul v z))";
  check true "(bvsub v w)" "(bvadd v (bvmul #xff w))";
  check false "(bvsub v w)" "(bvadd v (bvmul #xfe w))";
  check true "(bvadd #x00 v)" "v";
  check true "(bvmul #x01 v)" "v";
  check true "(bvmul #x00 v)" "#x00";
  check true "(bvmul #xff #xff v)" "v";
  check true "(bvmul #x02 (bvmul #x80 v))" "#x00";
  check false "(bvmul #xfe (bvmul #xff v))" "v";
  check true "(bvadd v w z)" "(bvadd v (bvadd w z))";
  check true "(= (bvadd v w) z)" "(= v (bvadd z (bvmul #xff w)))";
  check false "(= (bvadd v w) z)" "(= v (bvadd z w))";
  check true "(= (bvadd #x01 v) #x03)" "(= v #x02)";
  check true "(= (bvadd #xff v) #x00)" "(= v #x01)";
  check true "(= (bvadd #x02 v) #x00)" "(= v #xfe)";
  check true "(= (bvadd #b1 bit) #b0)" "(= bit #b1)";
  check false "(= (bvadd #x02 v) #x00)" "(= v #x02)";
  check false "(= (bvmul #x02 v) #x00)" "(= v #xfe)";
  check true "(= (bvadd v w) (bvmul #x02 v))" "(= v w)";
  check true "(= (bvadd v w) (bvmul #x02 v))"
    "(= w (bvsub #x00 (bvmul #xff v)))";
  check false "(= (bvadd v w) (bvmul #x02 v))" "(= v z)";
  check false "(= (bvadd v w) (bvmul #x03 v))" "(= v w)";
  check true "(bvult v w)" "(not (bvule w v))";
  check true "(bvuge v w)" "(bvule w v)";
  check false "(bvult v w)" "(not (bvule v w))";
  check false "(bvuge v w)" "(bvule v w)";
  check true "(bvult v v)" "false";
  check true "(bvule v v)" "true";
  check true "(bvuge v v)" "true";
  check true "(bvult bit bit)" "false";
  check true "(bvule wide wide)" "true";
  check true "(bvule maxwide maxwide)" "true";
  check false "(bvule too_wide too_wide)" "true";
  check true "(bvule (bvadd v w) (bvadd v w))" "true";
  check true "(bvult v v)" "(not (bvule v v))";
  check true "(bvuge v v)" "(bvule v v)";
  check false "(bvult v v)" "true";
  check false "(bvule v v)" "false";
  check false "(bvuge v v)" "false";
  check false "(bvult v w)" "false";
  check false "(bvule v w)" "true";
  check true "(bvule (mkbv p q) (mkbv r s))"
    "(ite (= q s) (ite (= p r) true (not p)) (not q))";
  check false "(bvule (mkbv p q) (mkbv r s))"
    "(ite (= q s) (ite (= p r) true p) (not q))";
  check true "(bvuge v #x05)"
    "(=> (= ((_ extract 7 3) v) #b00000) (bvule #b101 ((_ extract 2 0) v)))";
  check true "(bvule #x00 v)" "true";
  check true "(bvule #x01 v)"
    "(or (not (= ((_ extract 7 1) v) #b0000000)) (bvule #b1 ((_ extract 0 0) v)))";
  check false "(bvuge v #x05)"
    "(=> (= ((_ extract 7 3) v) #b00000) (bvule #b100 ((_ extract 2 0) v)))";
  check false "(bvuge v #x05)"
    "(and (= ((_ extract 7 3) v) #b00000) (bvule #b101 ((_ extract 2 0) v)))";
  check true "(= (ite p #b0 bit) #b1)" "(and (not p) (= bit #b1))";
  check true "(= #b1 (ite p bit #b0))" "(and p (= bit #b1))";
  check true "(= (ite p #b1 bit) #b1)" "(or p (= bit #b1))";
  check true "(= (ite p bit #b1) #b1)" "(or (not p) (= bit #b1))";
  check false "(= (ite p #b0 bit) #b1)" "(and p (= bit #b1))";
  check false "(= (ite p bit #b1) #b1)" "(or p (= bit #b1))";
  check true "#b1010" "(mkbv false true false true)";
  check false "#b1010" "(mkbv true false true false)";
  check true "(= (mkbv p false) (mkbv false p))" "(not p)";
  check true "(= (mkbv p true) (mkbv true false))" "false";
  check false "(= (mkbv p false) (mkbv false p))" "p";
  check true "((_ extract 2 1) (mkbv p false true false))" "#b10";
  check true "((_ extract 2 0) (mkbv p false true false))" "(mkbv p false true)";
  check false "((_ extract 2 1) (mkbv p false true false))" "#b01";
  check true "(concat (mkbv p false) (mkbv true p))" "(mkbv true p p false)";
  check false "(concat (mkbv p false) (mkbv true p))" "(mkbv p false true p)";
  check true "(concat v half bit)" "(concat v (concat half bit))";
  check true "(concat (mkbv p q) (mkbv r) (mkbv s))" "(mkbv s r p q)";
  check false "(concat (mkbv p q) (mkbv r) (mkbv s))" "(mkbv r s p q)";
  check true "(bvnot (concat v half))" "(concat (bvnot v) (bvnot half))";
  check false "(bvnot (concat v half))" "(concat (bvnot v) half)";
  check false "v" "(mkbv p p p p p p p p)";
  check true "(bvadd (mkbv p) (mkbv q))" "(mkbv (xor p q))";
  check true "(bvadd (mkbv p q) (mkbv r s))"
    "(mkbv (xor p r) (xor (xor q s) (and p r)))";
  check false "(bvadd (mkbv p q) (mkbv r s))" "(mkbv (xor p r) (xor q s))";
  check true "(bvadd (mkbv true true true) (mkbv true false false))" "#b000";
  check false "(bvadd (mkbv true true true) (mkbv true false false))" "#b100";
  check true "(bvadd (mkbv p q false) (mkbv true false false))"
    "(mkbv (not p) (xor q p) (and p q))";
  check true "(= (mkbv p q) (mkbv (not r) (not s)))"
    "(not (or (= r p) (= s q)))";
  check true "((_ zero_extend 0) v)" "v";
  check true "((_ zero_extend 24) v)" "(concat (_ bv0 24) v)";
  check true "(concat (_ bv0 24) v)" "((_ zero_extend 24) v)";
  check true "((_ zero_extend 1) bit)" "(concat #b0 bit)";
  check true "((_ zero_extend 65) wide)" "(concat (_ bv0 65) wide)";
  check true "((_ zero_extend 4095) bit)" "(concat (_ bv0 4095) bit)";
  check true "((_ zero_extend 24) #xff)" "#x000000ff";
  check true "((_ zero_extend 24) (ite p #x00 #xff))" "(concat (_ bv0 24) (ite p #x00 #xff))";
  check false "((_ zero_extend 24) v)" "(concat (_ bv1 24) v)";
  check false "((_ zero_extend 24) #xff)" "#xffffffff";
  check false "((_ zero_extend 1) bit)" "(concat bit #b0)";
  check false "((_ sign_extend 24) v)" "(concat (_ bv0 24) v)";
  check true "((_ extract 0 0) bit)" "bit";
  check true "((_ extract 7 0) v)" "v";
  check true "((_ extract 64 0) wide)" "wide";
  check true "((_ extract 11 4) (concat v half))" "v";
  check true "((_ extract 3 0) (concat v half))" "half";
  check true "((_ extract 8 1) (concat v bit))" "v";
  check true "((_ extract 7 4) #xa5)" "#xa";
  check true "((_ extract 3 0) #xa5)" "#x5";
  check true "((_ extract 64 64) (_ bv18446744073709551616 65))" "#b1";
  check false "((_ extract 7 4) #xa5)" "#x5";
  check false "((_ extract 7 0) (concat v half))" "v";
  check true "(= (concat v half) (concat v #xf))" "(= half #xf)";
  check false "(= (concat v half) (concat w #xf))" "(= half #xf)";
  check true "(= (concat v half) #xabc)" "(and (= half #xc) (= v #xab))";
  check true "(= #xabc (concat v half))"
    "(and (= half ((_ extract 3 0) #xabc)) (= v ((_ extract 11 4) #xabc)))";
  check false "(= (concat v half) #xabc)" "(and (= half #xb) (= v #xac))";
  check false "(= (concat v half) #xabc)" "(= half #xc)";
  check true "(= (concat #xab half) #xabc)" "(= half #xc)";
  check true "(= (concat bit half) #b11111)" "(and (= half #xf) (= bit #b1))";
  let inputs = parse c (declarations ^ "(assert (= (mkbv p true) #b11))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (f, args); _]) ->
       require (f.A.interp = Some Z3BvLemma.op_mkbv &&
                f.A.int_params = [Z.of_int 2])
         "native word identity or width was lost";
       List.iter (fun parameters ->
           require (Z3BvLemma.word_parts
             (A.App ({ f with A.int_params = List.map Z.of_int parameters }, args)) = None)
             "malformed word widths were trusted")
         [[]; [0]; [1]; [3]; [-2]; [2; 1]];
       require (Z3BvLemma.word_parts (A.App ({ f with A.interp = None }, args)) = None)
         "an uninterpreted word name was trusted";
       require (Z3BvLemma.word_parts
         (A.App ({ f with A.range = A.bool_sort }, args)) = None)
         "a word with a Boolean result sort was trusted";
       require (Z3BvLemma.word_parts
         (A.App (f, [Z3BvLemma.literal (Z.of_int 2) Z.zero; Z3ResolutionProofTheory.true_expr])) = None)
         "a word with a non-Boolean bit was trusted"
   | _ -> failwith "expected native word construction");
  let inputs = parse c (declarations ^ "(assert (= ((_ extract 7 0) v) v))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (f, args); _]) ->
       List.iter (fun parameters ->
           require (Z3BvLemma.extract_parts
             (A.App ({ f with A.int_params = List.map Z.of_int parameters }, args)) = None)
             "malformed extraction parameters were trusted")
         [[7; 7; 0]; [8; 8; 0]; [8; 7; -1]; [8; 0; 1]; [8; 7]];
       require (Z3BvLemma.extract_parts (A.App ({ f with A.interp = None }, args)) = None)
         "an uninterpreted extraction name was trusted"
   | _ -> failwith "expected native bit-vector extraction");
  let inputs = parse c (declarations ^ "(assert (= (concat v half) (concat w half)))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (f, args); _]) ->
       List.iter (fun parameters ->
           require (Z3BvLemma.concat_parts
             (A.App ({ f with A.int_params = List.map Z.of_int parameters }, args)) = None)
             "malformed concatenation widths were trusted")
         [[7; 5]; [8; 0]; [-1; 13]; [8; 4; 1]];
       require (Z3BvLemma.concat_parts (A.App ({ f with A.interp = None }, args)) = None)
         "an uninterpreted concatenation name was trusted"
   | _ -> failwith "expected native bit-vector concatenation");
  let inputs = parse c (declarations ^
    "(assert (= ((_ zero_extend 24) v) (concat (_ bv0 24) v)))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (f, args); target]) ->
       require (f.A.interp = Some Z3BvLemma.op_zero_extend &&
                f.A.int_params = List.map Z.of_int [8; 24])
         "native zero-extension identity or widths were lost";
       let reject f args =
         let source = A.App (f, args) in
         require (Z3BvLemma.zero_extend_parts source = None)
           "malformed zero extension was recognized";
         require (not (U.check_step U.RewriteRule (U.Equal (source, target)) []))
           "malformed zero extension justified a rewrite" in
       List.iter (fun parameters -> reject
           { f with A.int_params = List.map Z.of_int parameters } args)
         [[]; [8]; [8; 24; 0]; [0; 32]; [7; 25]; [8; -1]; [8; 4089]];
       List.iter (fun malformed -> reject malformed args)
         [{ f with A.interp = None }; { f with A.range = A.bool_sort };
          { f with A.domain = [A.bool_sort] }];
       reject f [];
       reject f (args @ args);
       reject f [Z3ResolutionProofTheory.true_expr]
   | _ -> failwith "expected native bit-vector zero extension");
  let inputs = parse c (declarations ^ "(assert (bvule v w))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (f, args) ->
       require (f.A.interp = Some Z3BvLemma.op_ule && f.A.int_params = [Z.of_int 8])
         "native comparison identity or operand width was lost";
       List.iter (fun parameters ->
           require (Z3BvLemma.unsigned_parts
             (A.App ({ f with A.int_params = List.map Z.of_int parameters }, args)) = None)
             "malformed unsigned comparison widths were trusted")
         [[]; [0]; [7]; [4097]; [8; 8]];
       List.iter (fun malformed ->
           require (Z3BvLemma.unsigned_parts (A.App (malformed, args)) = None)
             "malformed unsigned comparison signature was trusted")
         [{ f with A.interp = None };
          { f with A.range = Z3BvLemma.bv_sort (Z.of_int 8) };
          { f with A.domain = [A.bool_sort; A.bool_sort] }];
       require (Z3BvLemma.unsigned_parts (A.App (f, [List.hd args])) = None)
         "an unsigned comparison with missing operands was trusted";
       let self = [List.hd args; List.hd args] in
       List.iter (fun malformed ->
           require (Z3BvOrder.rewrite (A.App (malformed, self)) = None)
             "a malformed reflexive comparison was rewritten")
         [{ f with A.int_params = [Z.zero] };
          { f with A.int_params = [Z.of_int 7] };
          { f with A.interp = None };
          { f with A.range = Z3BvLemma.bv_sort (Z.of_int 8) };
          { f with A.domain = [A.bool_sort; A.bool_sort] }]
   | _ -> failwith "expected native unsigned comparison");
  let inputs = parse c (declarations ^ "(assert (= (concat v half bit) (concat w half bit)))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (f, args); _]) ->
       require (List.length args = 3 &&
                f.A.int_params = List.map Z.of_int [8; 4; 1])
         "native ternary concatenation widths were lost";
       List.iter (fun parameters ->
           require (Z3BvLemma.concat3_parts
             (A.App ({ f with A.int_params = List.map Z.of_int parameters }, args)) = None)
             "malformed ternary concatenation widths were trusted")
         [[8; 4]; [8; 4; 0]; [7; 5; 1]; [8; 4; 1; 1]];
       List.iter (fun malformed ->
           require (Z3BvLemma.concat3_parts (A.App (malformed, args)) = None)
             "malformed ternary concatenation signature was trusted")
         [{ f with A.interp = None }; { f with A.range = A.bool_sort };
          { f with A.domain = [A.bool_sort; A.bool_sort; A.bool_sort] }]
   | _ -> failwith "expected native ternary concatenation");
  let proof = document "(set-logic QF_BV)(assert (= #b0 (bvudiv #b1 #b0)))" in
  require (P.check_document proof = Some Z.zero)
    "division-by-zero benchmark proof did not check";
  let inputs = parse c (declarations ^ "(assert (= (bvudiv v #x00) #xff))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  match B.cached_expression st (List.hd inputs) with
  | A.App (_, [A.App (f, args); _]) ->
      require (Z3BvLemma.rewrite (A.App ({ f with A.interp = None }, args)) = None)
        "an uninterpreted division name was trusted"
  | _ -> failwith "expected native unsigned bit-vector division"

let fresh_bit_model_extension () =
  let module F = Z3BvFresh in
  let c = context () in
  let declarations =
    "(declare-const v (_ BitVec 3))(declare-const p Bool)\
     (declare-const q Bool)(declare-const r Bool)" in
  let inputs = parse c (declarations ^
    "(assert (= v #b101))(assert (= v (mkbv p q r)))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  let formulas = List.map (B.cached_expression st) inputs in
  let original, formula = match formulas with
    | [a; b] -> a, b | _ -> failwith "expected fresh-bit extension inputs" in
  let reconstruction = match F.check_condition [original] formula with
    | Some r -> r | None -> failwith "a fresh native word reconstruction was rejected" in
  let equation r = Z3ResolutionProofTheory.mk_eq_expr (F.source r) (F.word r) in
  let check expected inputs r =
    require (Option.is_some (F.check_condition inputs (equation r)) = expected)
      "incorrect fresh-bit extension condition" in
  check true [original] reconstruction;
  require (Option.is_some (F.check_condition [original]
      (Z3ResolutionProofTheory.mk_eq_expr (F.word reconstruction) (F.source reconstruction))))
    "reversed fresh-bit reconstruction was rejected";
  let first = List.hd reconstruction.F.symbols in
  check false [A.App (first, [])] reconstruction;
  let quantified = A.Quantifier (A.Forall_k, [A.bool_sort], A.bool_sort,
    Z3ResolutionProofTheory.mk_eq_expr (A.App (first, [])) (A.Var (Z.zero, A.bool_sort))) in
  check false [quantified] reconstruction;
  let symbol name = {
    A.decl_name = name; domain = []; range = A.bool_sort; interp = None; int_params = [];
  } in
  List.iter (fun f ->
      check false [original] { reconstruction with F.symbols = f :: List.tl reconstruction.F.symbols })
    [{ first with A.range = Z3BvLemma.bv_sort Z.one };
     { first with A.domain = [A.bool_sort] };
     { first with A.int_params = [Z.one] };
     { first with A.interp = Some Z3ValueTheory.op_true }];
  check false [original]
    { reconstruction with F.symbols = [first; first; List.nth reconstruction.F.symbols 2] };
  List.iter (fun original_decl ->
      check false [] { reconstruction with F.original = original_decl })
    [{ reconstruction.F.original with A.interp = Some Z3BvLemma.op_numeral };
     { reconstruction.F.original with A.domain = [A.bool_sort] };
     { reconstruction.F.original with A.int_params = [Z.one] };
     { reconstruction.F.original with A.range = A.bool_sort }];
  check false [] { reconstruction with F.constructor =
    { reconstruction.F.constructor with A.interp = None } };
  check true [] { reconstruction with F.constructor =
    { reconstruction.F.constructor with A.decl_name = "not-a-trusted-word-name" } };
  (* The model extension itself (`F.extend`) is ghost, like `Z3AstTheory.eval`, and is
     not extracted: that it reconstructs the values 0,1 / 0,1,5,7 / 0,128,165,255 of these
     words, satisfies the equation and leaves other symbols unchanged is checked by
     evaluation in `Z3BvFreshTests.model_extension_{1,3,8}`. *)
  List.iter (fun width ->
      let symbols = List.init width (fun n -> symbol ("ordinary-name-" ^ string_of_int n)) in
      let constructor = match Z3BvWord.word (F.atoms symbols) with
        | A.App (f, _) -> f | _ -> failwith "expected word constructor" in
      let r = { F.width = Z.of_int width;
        original = { reconstruction.F.original with A.range = Z3BvLemma.bv_sort (Z.of_int width) };
        constructor; symbols } in
      let unrelated = symbol "unrelated" in
      let assertions = [Z3ResolutionProofTheory.mk_eq_expr (F.source r) (F.source r);
                        A.App (unrelated, [])] in
      check true assertions r;
      require (not (U.check_step U.RewriteRule (U.Equal (F.source r, F.word r)) []))
        "fresh-bit reconstruction became an unconditional rewrite")
    [1; 3; 8]

let fresh_bit_context_extension () =
  let module F = Z3BvFresh in
  let module M = Z3BvFreshModel in
  let module R = Z3ResolutionProofTheory in
  let symbol name range = {
    A.decl_name = name; domain = []; range; interp = None; int_params = [];
  } in
  let reconstruction name names =
    let symbols = List.map (fun n -> symbol n A.bool_sort) names in
    let constructor = match Z3BvWord.word (F.atoms symbols) with
      | A.App (f, _) -> f | _ -> failwith "expected word constructor" in
    { F.width = Z.of_int 3; original = symbol name (Z3BvLemma.bv_sort (Z.of_int 3));
      constructor; symbols } in
  let r = reconstruction "v" ["p"; "q"; "r"] in
  let s = reconstruction "w" ["s"; "t"; "u"] in
  let equation r = R.mk_eq_expr (F.source r) (F.word r) in
  let inputs = [R.mk_eq_expr (F.source r) (F.source r)] in
  let formulas = [equation r; R.mk_eq_expr (F.word s) (F.source s)] in
  let rs = match M.check_context inputs formulas with
    | Some rs -> rs | None -> failwith "disjoint reconstruction context was rejected" in
  require (List.length rs = 2 && M.check_context inputs [] = Some [])
    "incorrect reconstruction context length";
  let shared = { s with F.symbols = List.hd r.F.symbols :: List.tl s.F.symbols } in
  require (M.check_context inputs [equation r; equation shared] = None)
    "cross-word bit collision was accepted";
  let first = A.App (List.hd r.F.symbols, []) in
  require (M.check_context [first] formulas = None)
    "input-visible context bit was accepted";
  let quantified = A.Quantifier (A.Forall_k, [A.bool_sort], A.bool_sort,
    R.mk_eq_expr first (A.Var (Z.zero, A.bool_sort))) in
  require (M.check_context [quantified] formulas = None)
    "context freshness ignored a binder";
  List.iter (fun name ->
      let unsafe = { r with F.symbols = symbol name A.bool_sort :: List.tl r.F.symbols } in
      require (Option.is_some (F.check_context inputs [equation unsafe]))
        "structural condition unexpectedly depended on a reserved name";
      require (M.check_context inputs [equation unsafe] = None)
        "semantic reserved-name collision was accepted")
    ["true"; "false"; "and"; "or"];
  (* The extensions (`F.extend_context`, `F.extend`, `F.number`) are ghost, like
     `Z3AstTheory.eval`, and are not extracted. That the batch extension keeps the
     inputs and satisfies both orientations, that the bit value of `r` in this model is 5,
     and that retraction preserves evaluation are checked by evaluation in
     `Z3BvFreshTests.context_extension` and `retraction`, on this fixture. The
     executable retraction is checked here with that bit value. *)
  let n = Z.of_int 5 in
  require (M.retract r.F.symbols n first = R.true_expr)
    "fresh bit did not retract to its Boolean literal";
  let applied = A.App (List.hd r.F.symbols, [A.Var (Z.zero, A.bool_sort)]) in
  require (M.retract r.F.symbols n applied = applied)
    "retraction changed a non-nullary application or bound variable";
  require (M.retract r.F.symbols n (F.source r) = F.source r)
    "retraction changed an original BV constant"

let fresh_bit_document_projections () =
  let module F = Z3BvFresh in
  let module W = Z3BvWord in
  let module R = Z3ResolutionProofTheory in
  let symbol name range = {
    A.decl_name = name; domain = []; range; interp = None; int_params = [];
  } in
  let reconstruction name names =
    let width = Z.of_int (List.length names) in
    let symbols = List.map (fun n -> symbol n A.bool_sort) names in
    let constructor = match W.word (F.atoms symbols) with
      | A.App (f, _) -> f | _ -> failwith "expected projection word constructor" in
    { F.width = width; original = symbol name (Z3BvLemma.bv_sort width);
      constructor; symbols } in
  let r = reconstruction "v" ["p"; "q"; "r"] in
  let s = reconstruction "w" ["s"; "t"; "u"] in
  let equation r = R.mk_eq_expr (F.source r) (F.word r) in
  let entry rule formula = { P.rule; formula; premise_ids = [] } in
  let make inputs equations = {
    P.declarations = [];
    expressions = inputs @ equations;
    assertions = inputs;
    entries = entry U.Asserted R.false_expr ::
      List.map (entry U.RewriteRule) equations;
    root = Z.zero;
  } in
  let hash _ = Z.zero in
  let check pending doc =
    let expected = Some (Z.of_int pending) in
    let actual = P.check_document doc in
    let show = function None -> "rejected" | Some n -> Z.to_string n in
    require (actual = expected && P.check_document_indexed hash doc = expected)
      (Printf.sprintf "incorrect fresh-bit document projection result: expected %s, got %s (%d entries)"
         (show expected) (show actual) (List.length doc.P.entries));
    let result, diagnostic = P.check_document_diagnosed_indexed hash doc in
    require (result = expected && P.diagnostic_result diagnostic = expected)
      "fresh-bit projection diagnostics disagreed with replay" in
  check 0 (make [R.false_expr] [equation r; R.mk_eq_expr (F.word s) (F.source s)]);
  check 0 (make [R.false_expr] [equation r; equation r]);
  check 0 (make [R.false_expr] [equation (reconstruction "bit" ["p"])]);
  check 0 (make [R.false_expr]
    [equation (reconstruction "v" ["true"; "false"; "and"])]);
  let first = A.App (List.hd r.F.symbols, []) in
  check 1 (make [R.false_expr; first] [equation r]);
  let quantified = A.Quantifier (A.Forall_k, [A.bool_sort], A.bool_sort,
    R.mk_eq_expr first (A.Var (Z.zero, A.bool_sort))) in
  check 1 (make [R.false_expr; quantified] [equation r]);
  let shared = { s with F.symbols = List.hd r.F.symbols :: List.tl s.F.symbols } in
  check 2 (make [R.false_expr] [equation r; equation shared]);
  let duplicate = { r with F.symbols =
    [List.hd r.F.symbols; List.hd r.F.symbols; List.nth r.F.symbols 2] } in
  check 1 (make [R.false_expr] [equation duplicate]);
  let interpreted = { (List.hd r.F.symbols) with A.interp = Some Z3ValueTheory.op_true } in
  check 1 (make [R.false_expr]
    [equation { r with F.symbols = interpreted :: List.tl r.F.symbols }]);
  let pair = { (symbol "pair" A.bool_sort) with A.domain = [A.bool_sort; A.bool_sort] } in
  let rec shared depth =
    if depth = 0 then first
    else let child = shared (depth - 1) in A.App (pair, [child; child]) in
  let large = shared 20 in
  let large_formula = R.mk_eq_expr large large in
  let large_document = make [R.false_expr] [equation r] in
  let large_document = { large_document with
    P.expressions = large_formula :: large_document.P.expressions;
    P.entries = large_document.P.entries @ [entry U.Reflexivity large_formula] } in
  check 1 large_document;
  let defs = F.projection_definitions [r] in
  let expanded = match Z3Definitions.expand (Z.of_int (List.length defs)) defs (F.word r) with
    | Some e -> e | None -> failwith "fresh-bit macro expansion failed" in
  require (W.equivalent (F.source r) expanded && W.equivalent expanded (F.source r))
    "projected reconstruction identity was not recognized";
  require (not (W.equivalent (F.source r) (F.word r)))
    "fresh bits became an unconditional reconstruction identity";
  (match expanded with
   | A.App (f, bits) ->
     require (not (W.equivalent (F.source r) (A.App (f, List.rev bits))))
       "reversed projection order was accepted";
     let bad = W.projection r.F.width (F.source r) r.F.width in
     require (not (W.equivalent (F.source r) (A.App (f, bad :: List.tl bits))))
       "out-of-range projection was accepted";
     let bad = W.projection (Z.of_int 4) (F.source r) Z.zero in
     require (not (W.equivalent (F.source r) (A.App (f, bad :: List.tl bits))))
       "wrong-width projection was accepted"
   | _ -> failwith "expected an expanded word");
  let variable = A.Var (Z.zero, Z3BvLemma.bv_sort r.F.width) in
  require (not (W.equivalent variable
    (W.word (W.projection_bits r.F.width variable Z.zero r.F.width))))
    "projection identity accepted an unbound variable";
  let with_premise = make [R.false_expr] [equation r] in
  let with_premise = { with_premise with P.entries =
    [List.hd with_premise.P.entries;
     { (List.nth with_premise.P.entries 1) with P.premise_ids = [Z.zero] }] } in
  require (P.document_definitions with_premise = Some [])
    "non-leaf reconstruction introduced fresh definitions"

let scoped_model_extension () =
  let module SM = Z3ScopedModel in
  let module F = Z3BvFresh in
  let module M = Z3BvFreshModel in
  let module R = Z3ResolutionProofTheory in
  let scope = [A.bool_sort; SM.int_sort] in
  let bvar = A.Var (Z.zero, A.bool_sort) in
  require (not (Z3Definitions.scoped [] bvar) && Z3Definitions.scoped scope bvar)
    "scope checking accepted an unbound variable or rejected a typed one";
  (* `SM.witness`, `Z3AstTheory.eval` and the extension `F.extend_context` are ghost and
     are not extracted. The evaluation facts this test used to check at run time (variable
     values in the typed and in a mistyped environment, reconstruction of the source value,
     the reversed equation, fresh atoms named like literals, the official literals, and
     scalar typing of every evaluated term) are checked by evaluation in
     `Z3BvFreshTests.scoped_witness` and `scoped_extension`, on this fixture. *)
  require (not (SM.scalar_typed A.bool_sort (Z3ValueTheory.VInt Z.zero)) &&
           not (SM.scalar_typed SM.int_sort (Z3ValueTheory.VBool false)))
    "scalar typing accepted a mismatched environment value";
  require (SM.arguments_typed scope [Z3ValueTheory.VBool false; Z3ValueTheory.VInt Z.zero] &&
           not (SM.arguments_typed scope [Z3ValueTheory.VInt Z.zero; Z3ValueTheory.VBool false]) &&
           not (SM.arguments_typed scope [Z3ValueTheory.VBool false]))
    "scalar argument typing ignored sorts or arity";
  let symbol name range = {
    A.decl_name = name; domain = []; range; interp = None; int_params = [];
  } in
  let symbols = List.map (fun name -> symbol name A.bool_sort) ["true"; "false"; "and"; "or"] in
  let constructor = match Z3BvWord.word (F.atoms symbols) with
    | A.App (f, _) -> f | _ -> failwith "expected scoped-model word constructor" in
  let r = { F.width = Z.of_int 4; original = symbol "v" (Z3BvLemma.bv_sort (Z.of_int 4));
            constructor; symbols } in
  let equations = [R.mk_eq_expr (F.word r) (F.source r)] in
  require (Option.is_some (F.check_context [] equations))
    "scoped structural context was rejected";
  require (M.check_context [] equations = None)
    "legacy model-safety guard unexpectedly accepted reserved fresh names";
  let quantified = A.Quantifier (A.Forall_k, scope, A.bool_sort,
    R.mk_eq_expr (A.Var (Z.zero, SM.int_sort)) (A.Var (Z.zero, SM.int_sort))) in
  require (Z3Definitions.scoped [] quantified)
    "mixed-sort quantified test was not well-scoped";
  require (not (U.check_step U.RewriteRule (U.Equal (F.source r, F.word r)) []))
    "scoped-model theorem enabled unconditional reconstruction acceptance"

let array_unequal_defaults () =
  let c = context () in
  let expression declarations text =
    let inputs = parse c (declarations ^ "(assert " ^ text ^ ")") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    B.cached_expression st (List.hd inputs) in
  let check expected declarations left right =
    let a = expression declarations left in
    let b = expression declarations right in
    require (U.check_step U.RewriteRule (U.Equal (a, b)) [] = expected)
      ("incorrect array rewrite: " ^ left ^ " -> " ^ right) in
  let left = "(store ((as const (Array Int Int)) 0) 2 3)" in
  let right = "(store ((as const (Array Int Int)) 1) 2 3)" in
  let source = "(= " ^ left ^ " " ^ right ^ ")" in
  let target = "(and (= 3 3) (= 3 3) (= 0 1))" in
  check true "" source target;
  check true "" target source;
  check true "" source "false";
  check false "" source "true";
  check false "" source "(and (= 3 3) (= 3 3) (= 0 0))";
  check false "" ("(= " ^ left ^ " " ^ left ^ ")") target;
  check true "(declare-const i Int)(declare-const j Int)(declare-const v Int)"
    ("(= (store (store " ^ left ^ " i 1) i 0) (store " ^ right ^ " j v))")
    "false";
  check true "" "(= ((as const (Array Int Int)) (- 8)) \
                      (store ((as const (Array Int Int)) 5) (- 400) 17))" "false";
  require (not (Z3ArrayEquality.unequal_defaults
    (expression "" "(= ((as const (Array Real Int)) 0) \
                        ((as const (Array Real Int)) 1))")))
    "Int-only default rule accepted Real indices";
  List.iter (fun (sort, first, second) ->
      let chain n = Printf.sprintf
        "(store (store ((as const (Array %s Int)) %d) %s 3) %s 3)"
        sort n first second in
      check false "" ("(= " ^ chain 0 ^ " " ^ chain 1 ^ ")") "false")
    ["Bool", "false", "true"; "(_ BitVec 1)", "#b0", "#b1"];
  let a = expression "" source in
  let expect_no_rule e =
    require (not (Z3ArrayEquality.unequal_defaults e))
      "malformed declaration passed array default checker";
    require (not (U.check_step U.RewriteRule
                    (U.Equal (e, Z3ResolutionProofTheory.false_expr)) []))
      "malformed declaration passed full rewrite checker" in
  let mutate_decl f =
    [{ f with A.interp = None };
     { f with A.decl_name = "forged" };
     { f with A.domain = [] };
     { f with A.range = A.BaseSort "Wrong" };
     { f with A.int_params = [Z.one] }] in
  (match a with
   | A.App (eq, [A.App (st, [A.App (co, [v]); k; w]); b]) ->
     List.iter (fun f -> expect_no_rule (A.App (f, [
       A.App (st, [A.App (co, [v]); k; w]); b]))) (mutate_decl eq);
     List.iter (fun f -> expect_no_rule (A.App (eq, [
       A.App (f, [A.App (co, [v]); k; w]); b]))) (mutate_decl st);
     List.iter (fun f -> expect_no_rule (A.App (eq, [
       A.App (st, [A.App (f, [v]); k; w]); b]))) (mutate_decl co);
     expect_no_rule (A.App (eq, [
       A.App (st, [A.App (co, [v]); Z3ResolutionProofTheory.true_expr; w]); b]));
     expect_no_rule (A.App (eq, [
       A.App (st, [A.App (co, [v]); k; Z3ResolutionProofTheory.true_expr]); b]))
   | _ -> failwith "unexpected array test shape");
  let doc = document ("(assert " ^ source ^ ")") in
  require (P.check_document doc = Some Z.zero)
    "native unequal-default array refutation retained an obligation";
  require (List.exists (fun entry -> entry.P.rule = U.RewriteRule &&
      match U.classify_fact entry.P.formula with
      | Some (U.Equal (a, b)) -> Z3TheoryNormalize.equivalent a b
      | _ -> false) doc.P.entries)
    "array reproducer did not exercise a verified rewrite"

let arithmetic_rewrites () =
  let c = context () in
  let check expected declarations left right =
    let source = Printf.sprintf "%s(assert (= %s %s))" declarations left right in
    let inputs = parse c source in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let formula = B.cached_expression st (List.hd inputs) in
    let conclusion = match U.classify_fact formula with
      | Some j -> j | None -> failwith "expected a typed rewrite conclusion" in
    require (U.check_step U.RewriteRule conclusion [] = expected)
      (Printf.sprintf "incorrect arithmetic rewrite: %s -> %s" left right)
  in
  let ints = "(declare-const x Int)(declare-const y Int)" in
  let reals = "(declare-const x Real)(declare-const y Real)" in
  List.iter (fun sort ->
    let declarations = Printf.sprintf
      "(declare-const x %s)(declare-const y %s)(declare-const z %s)" sort sort sort in
    check true declarations "(* x (+ y z))" "(+ (* x y) (* x z))";
    check true declarations "(+ (* x y) (* x z))" "(* x (+ y z))";
    check true declarations "(* (+ x y) z)" "(+ (* x z) (* y z))";
    check true declarations "(+ (* x z) (* y z))" "(* (+ x y) z)";
    check false declarations "(* x (+ y z))" "(+ (* x y) (* y z))";
    check false declarations "(* x (- y z))" "(+ (* x y) (* x z))"
  ) ["Int"; "Real"];
  check true ints "(<= x x)" "true";
  check true ints "(<= 0 x)" "(>= x 0)";
  check true reals "(< x y)" "(not (<= y x))";
  check true reals "(<= x y)" "(<= (+ x (* (- 1) y)) 0)";
  check true ints "(- x y)" "(+ x (* (- 1) y))";
  check true ints "(+ x y)" "(+ y x)";
  check false ints "(< x y)" "(<= x y)";
  check false ints "(+ x y)" "(+ x x)";
  check true reals "(+ x y)" "(+ y x)";
  check true reals "(- x y)" "(+ x (* (- 1) y))";
  check true reals "(- x)" "(* (- 1) x)";
  check true reals "(* (- 1) 6 x)" "(* (- 6) x)";
  check true reals "(/ 1 4)" "0.25";
  check true reals "(= x (+ 1 y))" "(= (+ x (* (- 1) y)) 1)";
  check true ints "(= 7 8)" "false";
  check true ints "false" "(= 7 8)";
  check true reals "(= (/ 1 4) 0.25)" "true";
  check true reals "(= 0.25 0.5)" "false";
  check true ints "(= (+ x 2) (+ 2 x))" "true";
  check false ints "(= 7 8)" "true";
  check false reals "(= (/ 1 4) 0.25)" "false";
  check false ints "(= x 7)" "false";
  check true ints "(= (+ (* (- 1) x) y) 0)" "(= (+ x (* (- 1) y)) 0)";
  check true reals "(= (+ (* (- 1) x) y) 3)" "(= (+ x (* (- 1) y)) (- 3))";
  check false reals "(= (+ (* (- 1) x) y) 3)" "(= (+ x (* (- 1) y)) 3)";
  check true ints "(= (+ (* 6 x) (* 3 y)) 9)" "(= (+ (* 2 x) y) 3)";
  check true reals "(= (* (- 2) x) 3)" "(= x (- 1.5))";
  check false ints "(= (+ (* 6 x) (* 3 y)) 9)" "(= (+ (* 2 x) y) 4)";
  check true reals "(<= (+ 10 (* 6 x)) 40)" "(<= x 5)";
  check true reals "(<= (* 2 x) 3)" "(<= x 1.5)";
  check true reals "(< (* (- 2) x) 3)" "(> x (- 1.5))";
  check true ints "(<= (* 6 x) 18)" "(<= x 3)";
  check true ints "(<= (+ 1 (* 4 x)) 2)" "(<= x 0)";
  check true ints "(>= (+ (* 4 x) (* 4 y)) 18)" "(>= (+ x y) 5)";
  check true ints "(<= (* (- 4) x) 2)" "(>= x 0)";
  check true ints "(not (>= (* 4 x) (- 2)))" "(<= x (- 1))";
  check false ints "(<= (+ 1 (* 4 x)) 2)" "(<= x 1)";
  check false ints "(>= (+ (* 4 x) (* 4 y)) 18)" "(>= (+ x y) 4)";
  check false reals "(<= (* 4 x) 2)" "(<= x 0)";
  check true ints "(= (* 2 x) 1)" "false";
  check true ints "(= (+ (* 4 x) (* 4 y)) 19)" "false";
  check true ints "(= (+ (* 4 x) (* 6 y)) 3)" "false";
  check true ints "false" "(= (+ (* (- 4) x) (* 6 y)) (- 3))";
  check false ints "(= (* 2 x) 2)" "false";
  check false ints "(= (+ (* 4 x) (* 6 y)) 2)" "false";
  check false reals "(= (* 2 x) 1)" "false";
  check false reals "(<= (* (- 2) x) 3)" "(<= x (- 1.5))";
  check false reals "(< (* 2 x) 3)" "(<= x 1.5)";
  check true ints "(ite (not (= x y)) 1 2)" "(ite (= x y) 2 1)";
  check true reals "(ite (= x y) x y)" "(ite (not (= x y)) y x)";
  check false ints "(ite (not (= x y)) 1 2)" "(ite (= x y) 1 2)";
  let numeric_branches = "(declare-const p Bool)(declare-const q Bool)" ^ ints in
  check true numeric_branches "(= (ite p 4 x) 1)" "(and (not p) (= x 1))";
  check true numeric_branches "(= (ite p 1 x) 1)" "(or p (= x 1))";
  check true numeric_branches "(= 1 (ite p 4 x))" "(and (not p) (= 1 x))";
  check true numeric_branches "(= (ite p 4 (ite q 1 x)) 1)"
    "(and (not p) (or q (= x 1)))";
  check false numeric_branches "(= (ite p 4 x) 1)" "(and p (= x 1))";
  check false numeric_branches "(= (ite p 1 x) 1)" "(and p (= x 1))";
  check true numeric_branches "(ite p (+ x 3) (+ y 3))" "(+ (ite p x y) 3)";
  check true numeric_branches "(+ 7 (ite p (+ x 3) (+ y 3)))"
    "(+ (ite p x y) 10)";
  check true numeric_branches "(ite p (+ x 3) (ite q (+ y 3) 3))"
    "(+ (ite p x (ite q y 0)) 3)";
  check false numeric_branches "(ite p (+ x 3) (+ y 3))" "(+ (ite p x y) 4)";
  check false numeric_branches "(ite p (+ x 3) (+ y 3))" "(+ (ite p y x) 3)";
  check true ("(declare-const p Bool)" ^ reals)
    "(= (ite p 4.5 x) 1.5)" "(and (not p) (= x 1.5))";
  let branches = "(declare-sort U 0)(declare-const a U)(declare-const b U)\
                  (declare-const p Bool)(declare-const q Bool)(declare-const r Bool)" in
  check true branches "(ite p a (ite q a b))" "(ite (or p q) a b)";
  check true branches "(ite p a (ite q a b))" "(ite p (ite true a b) (ite q a b))";
  check true branches "(ite (or p q) a b)" "(ite p a (ite q a b))";
  check true branches "(ite p a (ite q a (ite r a b)))" "(ite (or p (or q r)) a b)";
  check false branches "(ite p a (ite q b a))" "(ite (or p q) a b)";
  check false branches "(ite p a (ite q a b))" "(ite (and p q) a b)";
  check true branches "(ite p (ite q a b) b)" "(ite (and p q) a b)";
  check true branches "(ite (not p) (ite q a b) b)" "(ite (or p (not q)) b a)";
  check true branches "(ite (not (and p q)) a b)" "(ite (or (not p) (not q)) a b)";
  check false branches "(ite (not p) (ite q a b) b)" "(ite (or p q) b a)";
  check true reals "(= x y)" "(and (<= x y) (>= x y))";
  check true reals "(and (<= x y) (>= x y))" "(= x y)";
  check true ints "(= x y)" "(and (<= x y) (>= x y))";
  check false reals "(= x y)" "(and (< x y) (>= x y))";
  check false reals "(= x y)" "(and (<= x y) (<= x y))";
  check false reals "(= x (+ 1 y))" "(= (+ x (* (- 1) y)) 2)";
  check false reals "(+ x y)" "(+ x x)";
  check false reals "(<= (/ x 0) y)" "(<= x y)";
  check false ints "(* x y)" "(+ x y)";
  List.iter (fun declarations ->
      check true declarations "(* x y)" "(* y x)";
      check true declarations "(* (+ x (* (- 1) y)) y)"
        "(* y (+ x (* (- 1) y)))";
      check false declarations "(* x y)" "(* x x)";
      check true declarations "(* (+ 1 x) (* (- 1) y))"
        "(* (- 1) (* (+ 1 x) y))";
      check true declarations "(* x y x y)" "(* y (* x (* y x)))";
      check true declarations "(* x y y)" "(* y y x)";
      check false declarations "(* x y y)" "(* x x y)";
      check false declarations "(* x (* y y))" "(* x y)";
      check true declarations "(= (* x y) 0)" "(or (= x 0) (= y 0))";
      check true declarations "(= (* x y x) 0)" "(or (= x 0) (= y 0) (= x 0))";
      check false declarations "(= (* x y) 0)" "(and (= x 0) (= y 0))";
      check false declarations "(= (* x y) 0)" "(= x 0)";
      check true declarations "(<= (* x y) 0)"
        "(or (not (= (>= x 0) (>= y 0))) (or (= x 0) (= y 0)))";
      check true declarations "(>= (* x y) 0)"
        "(or (= (>= x 0) (>= y 0)) (or (= x 0) (= y 0)))";
      check false declarations "(>= (* x y) 0)" "(= (>= x 0) (>= y 0))";
      check true declarations "(<= (* x x x x) 0)" "(= x 0)";
      check false declarations "(<= (* x x x) 0)" "(= x 0)";
      check false declarations "(- x y)" "(- y x)")
    [ints; reals];
  check true ints "(* (+ 1 x) (+ 1 x))"
    "(+ (* 1 1) (* x 1) (* 1 x) (* x x))";
  check true reals "(* (+ 1.0 x) (+ 1.0 y))"
    "(+ (* 1.0 1.0) (* x 1.0) (* 1.0 y) (* x y))";
  check false ints "(* (+ 1 x) (+ 1 x))"
    "(+ (* 1 1) (* x 1) (* 1 x) (* x y))";
  check true ints "(div (* 10 x) 4)" "(div (* x 5) 2)";
  check true ints "(div (* 10 x) 4)"
    "(ite (= 0 4) (div (* 10 x) 0) (div (* x 5) 2))";
  check false ints "(div (* 10 x) 4)" "(div (* x 4) 2)";
  check false ints "(div (* 10 x) 0)" "(div (* x 5) 2)";
  check false ints "(div (* 10 x) 4)"
    "(ite (= 0 0) (div (* 10 x) 0) (div (* x 5) 2))";
  let x = A.Var (Z.zero, A.BaseSort "Int") in
  let malformed = { (Z3ResolutionProofTheory.eq_decl (A.BaseSort "Int"))
    with decl_name = "<="; interp = None } in
  require (not (U.check_step U.RewriteRule
      (U.Equal (A.App (malformed, [x; x]), Z3ResolutionProofTheory.true_expr)) []))
    "uninterpreted comparison was treated as arithmetic"

(* arith_rewriter::factor_le_ge_eq: p REL 0 with a common factor f of p and g = p / f.

   The kernel does not REJECT a `rewrite` step because no rule certifies it. For a well-formed,
   premise-free equation, the RewriteRule case of Z3UnifiedProof.check_node_with_membership
   returns Some (_, 0) when check_step succeeds and Some (_, 1), a pending obligation, when it
   fails; None (REJECT) is only for a structurally malformed node. An invalid step and a valid
   step outside this rule's shape are therefore both left uncertified (PARTIAL), never
   accepted. `pending` asserts that per node and `outcome` per refutation document, with the
   verdict text of the checker CLI (Z3NativeMain.result_text: None prints REJECT, Some 0
   ACCEPT, Some n PARTIAL n). *)
let arithmetic_factor_rewrites () =
  let module F = Z3ArithmeticFactor in
  let module LA = Z3LinearArithmeticAst in
  let c = context () in
  let accepted = ref 0 and invalid = ref 0 and unsupported = ref 0 in
  let terms_accepted = ref 0 and terms_invalid = ref 0 in
  (* The marshalled equation (= left right) as its declaration and both sides. With [binders]
     it is the body of (forall binders (= left right)), so its atoms are de Bruijn variables. *)
  let equation ?(binders = "") declarations left right =
    let source =
      if binders = "" then Printf.sprintf "%s(assert (= %s %s))" declarations left right
      else Printf.sprintf "%s(assert (forall (%s) (= %s %s)))" declarations binders left right in
    let inputs = parse c source in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match B.cached_expression st (List.hd inputs) with
    | A.App (d, [a; b]) when binders = "" -> d, a, b
    | A.Quantifier (_, _, _, A.App (d, [a; b])) when binders <> "" -> d, a, b
    | _ -> failwith "expected a factor rewrite equation" in
  let conclusion_of d a b =
    match U.classify_fact (A.App (d, [a; b])) with
    | Some conclusion -> conclusion
    | None -> failwith "expected a typed factor rewrite conclusion" in
  let step ?binders declarations left right =
    let d, a, b = equation ?binders declarations left right in
    conclusion_of d a b, a, b in
  (* The kernel's verdict on the step as a node: its pending obligations, or None for REJECT. *)
  let pending conclusion =
    match U.check_node [] { U.kind = U.RewriteRule; conclusion = conclusion; premises = [] } with
    | Some (_, obligations) -> Some obligations
    | None -> None in
  (* The CLI verdict on a refutation whose only rewrite is the step: unit resolution of
     (not (= left right)) with (= left right) derives false. *)
  let outcome declarations left right =
    let inputs = parse c (Printf.sprintf "%s(assert (= %s %s))(assert (not (= %s %s)))"
                            declarations left right left right) in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match List.map (B.cached_expression st) inputs with
    | [rewrite; negation] ->
        let entry rule formula premise_ids = { P.rule; formula; premise_ids } in
        Z3NativeMain.result_text (P.check_document {
          P.declarations = []; expressions = []; assertions = [negation];
          entries = [entry U.Asserted negation []; entry U.RewriteRule rewrite [];
                     entry U.UnitResolution Z3ResolutionProofTheory.false_expr [Z.zero; Z.one]];
          root = Z.of_int 2 })
    | _ -> failwith "expected a rewrite and its negation" in
  (* Accepted: the factor rule decides the step, the rewrite kernel certifies it without an
     obligation, and a refutation using it is ACCEPTed. *)
  let accept ?binders declarations left right =
    incr accepted;
    let name = left ^ " -> " ^ right in
    let conclusion, a, b = step ?binders declarations left right in
    require (F.check a b) ("factor rewrite rejected: " ^ name);
    require (U.check_step U.RewriteRule conclusion []) ("factor rewrite not certified: " ^ name);
    require (not (U.check_step U.RewriteRule conclusion [conclusion]))
      ("factor rewrite ignored an unexpected premise: " ^ name);
    require (not (U.check_step U.Commutativity conclusion []))
      ("factor rewrite accepted under another rule: " ^ name);
    require (pending conclusion = Some Z.zero) ("factor rewrite left an obligation: " ^ name);
    if binders = None then
      require (outcome declarations left right = "ACCEPT")
        ("factor rewrite refutation was not ACCEPT: " ^ name) in
  (* Not accepted: no rule certifies the step, the kernel leaves it as one pending obligation
     (not REJECT), and a refutation using it is PARTIAL 1. *)
  let uncertified ?binders what declarations left right =
    let name = left ^ " -> " ^ right in
    let conclusion, a, b = step ?binders declarations left right in
    require (not (F.check a b)) (what ^ " accepted by the factor rule: " ^ name);
    require (not (U.check_step U.RewriteRule conclusion [])) (what ^ " certified: " ^ name);
    require (pending conclusion = Some Z.one) (what ^ " was not left pending: " ^ name);
    if binders = None then
      require (outcome declarations left right = "PARTIAL 1")
        (what ^ " did not give a PARTIAL 1 refutation: " ^ name) in
  (* Invalid steps: no rule may certify them. *)
  let reject ?binders declarations left right =
    incr invalid;
    uncertified ?binders "invalid factor rewrite" declarations left right in
  (* Valid steps outside the rule's exact shape: not accepted by this rule either. *)
  let outside ?binders declarations left right =
    incr unsupported;
    uncertified ?binders "unsupported factor shape" declarations left right in
  (* The same decisions for marshalled terms that are rebuilt with a changed atom or numeral. *)
  let accept_terms what d a b =
    incr terms_accepted;
    let conclusion = conclusion_of d a b in
    require (F.check a b) ("factor rewrite rejected: " ^ what);
    require (U.check_step U.RewriteRule conclusion []) ("factor rewrite not certified: " ^ what);
    require (pending conclusion = Some Z.zero) ("factor rewrite left an obligation: " ^ what) in
  let reject_terms what d a b =
    incr terms_invalid;
    let conclusion = conclusion_of d a b in
    require (not (F.check a b)) ("invalid factor terms accepted: " ^ what);
    require (not (U.check_step U.RewriteRule conclusion [])) ("invalid factor terms certified: " ^ what);
    require (pending conclusion <> Some Z.zero) ("invalid factor terms left no obligation: " ^ what) in
  let rec map_term f e =
    match f e with
    | Some replacement -> replacement
    | None ->
        (match e with
         | A.App (decl, args) -> A.App (decl, List.map (map_term f) args)
         | A.Quantifier (kind, sorts, sort, body) -> A.Quantifier (kind, sorts, sort, map_term f body)
         | A.Var _ -> e) in
  (* The kernel REJECTs (None) only a malformed node, such as a rewrite with a premise; a
     well-formed step that no rule certifies stays pending. *)
  (let conclusion, _, _ = step "(declare-const p Bool)" "p" "p" in
   require (pending conclusion = Some Z.zero) "a reflexive rewrite was not certified";
   require (U.check_node [] { U.kind = U.RewriteRule; conclusion = conclusion;
                              premises = [{ U.conclusion = conclusion; hypotheses = [] }] } = None)
     "a rewrite with a premise was not rejected");
  List.iter (fun (s, zero, one, two, minus) ->
    let d = Printf.sprintf
      "(declare-const x %s)(declare-const y %s)(declare-const z %s)(declare-fun h (%s) %s)"
      s s s s s in
    let f fmt = Printf.sprintf fmt in
    (* z3test nl12: x*z + z <= 0, factor z, cofactor 1 + x. *)
    let le_target g g' = f "(or (not (= (>= z %s) (>= %s %s))) (or (= z %s) (= %s %s)))"
        zero g zero zero g' zero in
    let le_source = f "(<= (+ (* x z) z) %s)" zero in
    let one_x = f "(+ %s x)" one in
    accept d le_source (le_target one_x one_x);
    (* The two occurrences of the cofactor need only normalize alike. *)
    accept d le_source (le_target (f "(+ x %s)" one) one_x);
    (* z3test nl49: y*x - z*x = 0, factor x, cofactor z*(-1) + y. *)
    let eq_source = f "(= (+ (* y x) (* %s (* z x))) %s)" minus zero in
    let eq_cofactor = f "(+ (* z %s) y)" minus in
    accept d eq_source (f "(or (= x %s) (= %s %s))" zero eq_cofactor zero);
    (* z3test nl33: x - x*x >= 0, factor x, cofactor x*(-1) + 1. *)
    let ge_target fx g = f "(or (= (>= %s %s) (>= %s %s)) (or (= %s %s) (= %s %s)))"
        fx zero g zero fx zero g zero in
    let ge_cofactor = f "(+ (* x %s) %s)" minus one in
    accept d (f "(>= (+ x (* %s (* x x))) %s)" minus zero) (ge_target "x" ge_cofactor);
    (* An uninterpreted factor is an opaque atom. *)
    accept d (f "(>= (+ (* (h x) y) (h x)) %s)" zero) (ge_target "(h x)" (f "(+ y %s)" one));
    (* Wrong polarity: a >= source with the <= target, and a <= source without the negation. *)
    reject d (f "(>= (+ (* x z) z) %s)" zero) (le_target one_x one_x);
    reject d le_source (ge_target "z" one_x);
    (* Wrong cofactor, inconsistent cofactor occurrences, or an off-by-one source. *)
    let two_x = f "(+ (+ %s %s) x)" one one in
    reject d le_source (le_target two_x two_x);
    reject d le_source (le_target two_x one_x);
    reject d (f "(<= (+ (* x z) z %s) %s)" one zero) (le_target one_x one_x);
    (* Nonzero comparands on either side. *)
    reject d (f "(<= (+ (* x z) z) %s)" one) (le_target one_x one_x);
    reject d eq_source (f "(or (= x %s) (= %s %s))" one eq_cofactor zero);
    (* Wrong factor, and a false product rewrite that would refute a satisfiable formula. *)
    reject d eq_source (f "(or (= z %s) (= %s %s))" zero eq_cofactor zero);
    reject d (f "(>= (* x y) %s)" zero) (f "(or (= x %s) (= y %s))" zero zero);
    reject d (f "(= (+ (* x z) z) %s)" zero) (f "(or (= z %s) (= x %s))" zero zero);
    (* A missing source term, a zero factor, and a strict source relation. *)
    reject d (f "(<= (* x z) %s)" zero) (le_target one_x one_x);
    reject d eq_source (f "(or (= %s %s) (= %s %s))" zero zero eq_cofactor zero);
    reject d (f "(< (+ (* x z) z) %s)" zero) (le_target one_x one_x);
    (* Wrong Boolean connectives. *)
    reject d le_source (f "(and (not (= (>= z %s) (>= %s %s))) (or (= z %s) (= %s %s)))"
                          zero one_x zero zero one_x zero);
    reject d eq_source (f "(and (= x %s) (= %s %s))" zero eq_cofactor zero);
    (* Valid but outside the rule: flattened or reordered disjunctions, strict sign atoms,
       and a numeral factor. *)
    outside d le_source (f "(or (not (= (>= z %s) (>= %s %s))) (= z %s) (= %s %s))"
                           zero one_x zero zero one_x zero);
    outside d le_source (f "(or (or (= z %s) (= %s %s)) (not (= (>= z %s) (>= %s %s))))"
                           zero one_x zero zero one_x zero);
    outside d (f "(>= (+ x (* %s (* x x))) %s)" minus zero)
      (f "(or (= (> x %s) (> %s %s)) (or (= x %s) (= %s %s)))"
         zero ge_cofactor zero zero ge_cofactor zero);
    outside d (f "(= (+ (* %s x) (* %s y)) %s)" two two zero)
      (f "(or (= %s %s) (= (+ x y) %s))" two zero zero);
    (* Atoms that are de Bruijn variables of an enclosing quantifier, so the rewrite is an open
       term. The same variable on both sides is accepted; another variable is another atom. *)
    let uf = f "(declare-fun h (%s) %s)" s s in
    let binders = f "(x %s) (y %s) (z %s)" s s s in
    let le_by fx g = f "(or (not (= (>= %s %s) (>= %s %s))) (or (= %s %s) (= %s %s)))"
        fx zero g zero fx zero g zero in
    accept ~binders uf le_source (le_target one_x one_x);
    accept ~binders uf eq_source (f "(or (= x %s) (= %s %s))" zero eq_cofactor zero);
    accept ~binders uf (f "(>= (+ (* (h x) y) (h x)) %s)" zero)
      (ge_target "(h x)" (f "(+ y %s)" one));
    reject ~binders uf le_source (le_by "y" one_x);
    reject ~binders uf le_source (le_by "z" (f "(+ %s y)" one));
    reject ~binders uf eq_source (f "(or (= y %s) (= %s %s))" zero eq_cofactor zero);
    reject ~binders uf (f "(>= (+ (* (h x) y) (h x)) %s)" zero)
      (ge_target "(h z)" (f "(+ y %s)" one));
    (* Shifting every bound-variable index on both sides keeps the rewrite accepted; shifting
       it on one side does not. *)
    let open_d, open_a, open_b = equation ~binders uf le_source (le_target one_x one_x) in
    let shift = map_term (function
        | A.Var (index, sort) -> Some (A.Var (Z.succ index, sort))
        | _ -> None) in
    require (shift open_a <> open_a && shift open_b <> open_b)
      "the factor rewrite body has no bound variables";
    accept_terms (f "%s: bound variables shifted on both sides" s) open_d (shift open_a) (shift open_b);
    reject_terms (f "%s: bound variables shifted in the target" s) open_d open_a (shift open_b);
    reject_terms (f "%s: bound variables shifted in the source" s) open_d (shift open_a) open_b;
    (* Right-hand zeros whose numeral metadata is not the canonical zero of this sort. Each one,
       put in place of each zero of an accepted step, leaves the step uncertified. *)
    let sort = A.BaseSort s in
    let other = A.BaseSort (if s = "Int" then "Real" else "Int") in
    let is_zero e = LA.numeral e = Some (Z.zero, Z.one) in
    List.iter (fun (relation, source, target) ->
      let zd, a, b = equation d source target in
      require (F.check a b) ("step with canonical zeros rejected: " ^ source);
      let zero_decl = match a with
        | A.App (_, [_; A.App (numeral, [])]) -> numeral
        | _ -> failwith "expected a zero numeral" in
      let zeros = ref 0 in
      ignore (map_term (fun e -> if is_zero e then (incr zeros; Some e) else None)
                (A.App (zd, [a; b])));
      List.iter (fun (kind, bad) ->
        for index = 0 to !zeros - 1 do
          let seen = ref (-1) in
          let replace = map_term (fun e ->
              if is_zero e then begin
                incr seen;
                Some (if !seen = index then A.App (bad, []) else e)
              end else None) in
          let a' = replace a in
          let b' = replace b in
          require (a' <> a || b' <> b) "the zero was not replaced";
          reject_terms (f "%s %s: %s at zero %d" s relation kind index) zd a' b'
        done)
        [ "zero of the other sort", { zero_decl with A.range = other };
          "0/2", { zero_decl with A.int_params = [Z.zero; Z.of_int 2] };
          "zero without a denominator", { zero_decl with A.int_params = [Z.zero] };
          "zero with an extra parameter", { zero_decl with A.int_params = [Z.zero; Z.one; Z.of_int 7] };
          "uninterpreted zero with numeral parameters", { zero_decl with A.interp = None };
          "zero with another declaration kind",
            { zero_decl with A.interp = Some Z3ValueTheory.op_to_real };
          "zero with a domain", { zero_decl with A.domain = [sort] };
          "uninterpreted constant 0",
            { A.decl_name = "0"; domain = []; range = sort; interp = None; int_params = [] } ])
      ["<=", le_source, le_target one_x one_x;
       "=", eq_source, f "(or (= x %s) (= %s %s))" zero eq_cofactor zero];
    (* A declared constant named 0 is not the numeral. *)
    let named = f "%s(declare-const |0| %s)" d s in
    reject named (f "(<= (+ (* x z) z) |0|)") (le_target one_x one_x);
    reject named le_source
      (f "(or (not (= (>= z |0|) (>= %s |0|))) (or (= z |0|) (= %s |0|)))" one_x one_x);
    reject named eq_source (f "(or (= x |0|) (= %s |0|))" eq_cofactor))
    ["Int", "0", "1", "2", "(- 1)"; "Real", "0.0", "1.0", "2.0", "(- 1.0)"];
  let ints = "(declare-const x Int)(declare-const y Int)(declare-const z Int)" in
  outside ints "(= (+ (* y x) (* (- 1) (* z x))) 0)"
    "(or (= (to_real x) 0.0) (= (to_real (+ (* z (- 1)) y)) 0.0))";
  (* Integer division is an opaque atom, so the factorization is a ring identity. *)
  accept ints "(= (+ (* (div x 2) y) (div x 2)) 0)" "(or (= (div x 2) 0) (= (+ y 1) 0))";
  let reals = "(declare-const x Real)(declare-const y Real)" in
  accept reals "(>= (+ (* (/ x y) y) (/ x y)) 0.0)"
    "(or (= (>= (/ x y) 0.0) (>= (+ y 1.0) 0.0)) (or (= (/ x y) 0.0) (= (+ y 1.0) 0.0)))";
  (* (x / y) * y is not x: that would need a field law and y <> 0. *)
  reject reals "(= x 0.0)" "(or (= (/ x y) 0.0) (= y 0.0))";
  reject reals "(>= x 0.0)"
    "(or (= (>= (/ x y) 0.0) (>= y 0.0)) (or (= (/ x y) 0.0) (= y 0.0)))";
  (* The sort guard: to_real is opaque, so no identity of Int terms is pushed through it, and
     every comparison of the rewrite has the sort of p. *)
  let mixed =
    "(declare-const x Int)(declare-const z Int)(declare-const n Int)(declare-const t Real)" in
  let real_le fx g = Printf.sprintf
      "(or (not (= (>= %s 0.0) (>= %s 0.0))) (or (= %s 0.0) (= %s 0.0)))" fx g fx g in
  let int_le fx g = Printf.sprintf
      "(or (not (= (>= %s 0) (>= %s 0))) (or (= %s 0) (= %s 0)))" fx g fx g in
  (* A Real comparison of the Int p under to_real is one opaque atom, not x * z + z. *)
  outside mixed "(<= (to_real (+ (* x z) z)) 0.0)" (real_le "(to_real z)" "(to_real (+ 1 x))");
  (* A Real p whose cofactor has an Int term under to_real: to_real n and to_real (n + 1) are
     unrelated atoms, so only the spelling that uses to_real n is accepted. *)
  let real_p = "(<= (+ (* t (to_real n)) t) 0.0)" in
  accept mixed real_p (real_le "t" "(+ (to_real n) 1.0)");
  outside mixed real_p (real_le "t" "(to_real (+ n 1))");
  reject mixed real_p (real_le "t" "(+ (to_real n) 2.0)");
  reject mixed real_p (real_le "t" "(to_real (+ n 2))");
  (* An Int source with Real comparisons, a Real source with Int comparisons, and one Real
     comparison among Int ones. *)
  outside mixed "(<= (+ (* x z) z) 0)" (real_le "(to_real z)" "(to_real (+ 1 x))");
  outside mixed "(<= (+ (* (to_real x) (to_real z)) (to_real z)) 0.0)" (int_le "z" "(+ 1 x)");
  outside mixed "(<= (+ (* x z) z) 0)"
    "(or (not (= (>= z 0) (>= (+ 1 x) 0))) (or (= (to_real z) 0.0) (= (+ 1 x) 0)))";
  (* Atoms are compared with their whole declaration: a Real and an Int function with the same
     name and arguments are different atoms. The native view gives each declaration a unique
     name (decl!<id>:<name>), so the two functions are renamed to one name to collide. *)
  let overloaded =
    "(declare-fun hr (Int) Real)(declare-fun hi (Int) Int)(declare-const x Int)\
     (declare-const y Real)(declare-const k Int)" in
  let named_like suffix decl = String.ends_with ~suffix decl.A.decl_name in
  let rename = map_term (function
      | A.App (decl, args) when named_like ":hr" decl || named_like ":hi" decl ->
          Some (A.App ({ decl with A.decl_name = "h" }, args))
      | _ -> None) in
  let named_step left right =
    let d, a, b = equation overloaded left right in
    d, rename a, rename b in
  (match named_step "(= (hr x) (to_real (hi x)))" "true" with
   | _, A.App (_, [A.App (real_h, args); A.App (_, [A.App (int_h, args')])]), _ ->
       require (real_h.A.decl_name = int_h.A.decl_name && args = args' && real_h <> int_h)
         "the overloaded functions do not share a name and arguments"
   | _ -> failwith "expected the overloaded function applications");
  let retyped sort = map_term (function
      | A.App (decl, args) when decl.A.decl_name = "h" ->
          Some (A.App ({ decl with A.range = sort }, args))
      | _ -> None) in
  let ge_real fx g = Printf.sprintf
      "(or (= (>= %s 0.0) (>= %s 0.0)) (or (= %s 0.0) (= %s 0.0)))" fx g fx g in
  let ge_int fx g = Printf.sprintf
      "(or (= (>= %s 0) (>= %s 0)) (or (= %s 0) (= %s 0)))" fx g fx g in
  let real_atom = "(>= (+ (* (hr x) y) (hr x)) 0.0)" in
  let d, a, b = named_step real_atom (ge_real "(hr x)" "(+ y 1.0)") in
  accept_terms "Real function atom" d a b;
  reject_terms "Real function atom in place of the Int one"
    d a (retyped (A.BaseSort "Int") b);
  let d, a, b = named_step real_atom (ge_real "(to_real (hi x))" "(+ y 1.0)") in
  reject_terms "Int function atom under to_real for the Real one" d a b;
  let int_atom = "(>= (+ (* (hi x) k) (hi x)) 0)" in
  let d, a, b = named_step int_atom (ge_int "(hi x)" "(+ k 1)") in
  accept_terms "Int function atom" d a b;
  reject_terms "Int function atom in place of the Real one"
    d a (retyped (A.BaseSort "Real") b);
  let d, a, b = named_step int_atom (ge_int "(to_int (hr x))" "(+ k 1)") in
  reject_terms "Real function atom under to_int for the Int one" d a b;
  (* A declaration that differs only in its parameters is another atom, though its name and
     arguments are the same. *)
  let parameterized = map_term (function
      | A.App (decl, args) when decl.A.decl_name = "h" ->
          Some (A.App ({ decl with A.int_params = [Z.one] }, args))
      | _ -> None) in
  let d, a, b = named_step int_atom (ge_int "(hi x)" "(+ k 1)") in
  reject_terms "Int function atom with another declaration parameter" d a (parameterized b);
  let d, a, b = named_step real_atom (ge_real "(hr x)" "(+ y 1.0)") in
  reject_terms "Real function atom with another declaration parameter" d a (parameterized b);
  (* The expansion bound. Z3ArithmeticFactor.times compares the product of the operand sizes
     with max_terms (4096) before it calls Z3NlaLemma.multiply, and product multiplies one
     factor at a time through times, so every intermediate product is bounded too. A valid
     rewrite whose expansion is too large is not accepted by F.check, which decides it without
     expanding it. *)
  let sum prefix n =
    "(+ " ^ String.concat " " (List.init n (fun i -> Printf.sprintf "%s%d" prefix (i + 1))) ^ ")" in
  let wide = String.concat "" (List.concat_map (fun (prefix, count) ->
      List.init count (fun i -> Printf.sprintf "(declare-const %s%d Int)" prefix (i + 1)))
      ["x", 65; "y", 240; "w", 65]) in
  let sign_factors f g = Printf.sprintf
      "(or (not (= (>= %s 0) (>= %s 0))) (or (= %s 0) (= %s 0)))" f g f g in
  let decided what left right =
    let _, a, b = step wide left right in
    let start = Unix.gettimeofday () in
    let result = F.check a b in
    let elapsed = Unix.gettimeofday () -. start in
    Printf.printf "  %s: F.check %b in %.3fs\n%!" what result elapsed;
    result, elapsed in
  (* Products of sums with 65 * 65 = 4225 monomials, and of three sums whose second
     multiplication has 17 * 17 * 17 = 4913. The arithmetic rewriter's product rule still
     certifies these steps without expanding, so only F.check is asserted. *)
  List.iter (fun (what, left, right) ->
      let result, elapsed = decided what left right in
      require (not result) ("product beyond the expansion bound accepted: " ^ what);
      require (elapsed < 10.0) ("expansion bound did not stop the check: " ^ what))
    ["65 x 65 product",
       Printf.sprintf "(= (* %s %s) 0)" (sum "x" 65) (sum "y" 65),
       Printf.sprintf "(or (= %s 0) (= %s 0))" (sum "x" 65) (sum "y" 65);
     "65 x 65 product (<=)",
       Printf.sprintf "(<= (* %s %s) 0)" (sum "x" 65) (sum "y" 65),
       sign_factors (sum "x" 65) (sum "y" 65);
     "17 x 17 x 17 product",
       Printf.sprintf "(= (* %s %s %s) 0)" (sum "x" 17) (sum "y" 17) (sum "w" 17),
       Printf.sprintf "(or (= %s 0) (= (* %s %s) 0))" (sum "x" 17) (sum "y" 17) (sum "w" 17)];
  (* With an extra term, no other rule factors the step, so the bound decides it:
     X * Y + X * w1 = X * (Y + w1), where X * Y and X * (Y + w1) are expanded. The step is
     accepted when the largest expansion has 4096 monomials and stays pending at 4097. *)
  let extended m n =
    Printf.sprintf "(= (+ (* %s %s) (* %s w1)) 0)" (sum "x" m) (sum "y" n) (sum "x" m),
    Printf.sprintf "(or (= %s 0) (= (+ %s w1) 0))" (sum "x" m) (sum "y" n) in
  let extended_le m n =
    Printf.sprintf "(<= (+ (* %s %s) (* %s w1)) 0)" (sum "x" m) (sum "y" n) (sum "x" m),
    sign_factors (sum "x" m) (Printf.sprintf "(+ %s w1)" (sum "y" n)) in
  let extended3 n =
    Printf.sprintf "(= (+ (* %s %s %s) (* %s w1)) 0)" (sum "x" n) (sum "y" n) (sum "w" n) (sum "x" n),
    Printf.sprintf "(or (= %s 0) (= (+ (* %s %s) w1) 0))" (sum "x" n) (sum "y" n) (sum "w" n) in
  List.iter (fun (what, (left, right), within_bound) ->
      let result, elapsed = decided what left right in
      require (result = within_bound) ("wrong decision at the expansion bound: " ^ what);
      require (within_bound || elapsed < 10.0) ("expansion bound did not stop the check: " ^ what);
      if within_bound then accept wide left right else outside wide left right)
    ["64 x 63 + 64 x 1, f * g = 64 * 64 = 4096", extended 64 63, true;
     "17 x 240 + 17 x 1, f * g = 17 * 241 = 4097", extended 17 240, false;
     "65 x 65 + 65 x 1, X * Y = 4225", extended 65 65, false;
     "65 x 65 + 65 x 1 (<=), X * Y = 4225", extended_le 65 65, false;
     "15 x 15 x 15 + 15 x 1, f * g = 15 * 226 = 3390", extended3 15, true;
     "17 x 17 x 17 + 17 x 1, 17 * (17 * 17) = 4913", extended3 17, false];
  Printf.printf "  factor rewrites: %d accepted, %d invalid, %d outside the shape; \
                 rebuilt terms: %d accepted, %d invalid\n%!"
    !accepted !invalid !unsupported !terms_accepted !terms_invalid

(* arith_rewriter::mk_le_ge_eq_core lifts a conditional with a numeral branch out of a
   comparison with a numeral: (ite c t e) REL k becomes (or c (e REL k)) when t REL k holds and
   (and (not c) (e REL k)) when it does not, with (not c) and c for a numeral else branch. After
   cancel_monomials moved numeral addends, 1 + (ite c t e) >= k is rewritten through
   (ite c t e) >= k - 1 in the same step. Z3ConditionalRewrite splits on the guard and folds
   each branch: comparisons whose linear normal form is a constant become true or false, and
   and/or drop their literal arguments. Pending and outcome are asserted as for the factor
   rewrites above: an invalid step, and a valid step that is not in the checked shape, stays one
   pending obligation (PARTIAL), never ACCEPT and never REJECT. *)
let conditional_comparison_rewrites () =
  let module CR = Z3ConditionalRewrite in
  let module LA = Z3LinearArithmeticAst in
  let c = context () in
  let accepted = ref 0 and invalid = ref 0 and unsupported = ref 0 in
  let terms_accepted = ref 0 and terms_invalid = ref 0 in
  let equation ?(binders = "") declarations left right =
    let source =
      if binders = "" then Printf.sprintf "%s(assert (= %s %s))" declarations left right
      else Printf.sprintf "%s(assert (forall (%s) (= %s %s)))" declarations binders left right in
    let inputs = parse c source in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match B.cached_expression st (List.hd inputs) with
    | A.App (d, [a; b]) when binders = "" -> d, a, b
    | A.Quantifier (_, _, _, A.App (d, [a; b])) when binders <> "" -> d, a, b
    | _ -> failwith "expected a conditional comparison rewrite equation" in
  let conclusion_of d a b =
    match U.classify_fact (A.App (d, [a; b])) with
    | Some conclusion -> conclusion
    | None -> failwith "expected a typed conditional comparison rewrite conclusion" in
  let step ?binders declarations left right =
    let d, a, b = equation ?binders declarations left right in
    conclusion_of d a b, a, b in
  let pending conclusion =
    match U.check_node [] { U.kind = U.RewriteRule; conclusion = conclusion; premises = [] } with
    | Some (_, obligations) -> Some obligations
    | None -> None in
  let outcome declarations left right =
    let inputs = parse c (Printf.sprintf "%s(assert (= %s %s))(assert (not (= %s %s)))"
                            declarations left right left right) in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match List.map (B.cached_expression st) inputs with
    | [rewrite; negation] ->
        let entry rule formula premise_ids = { P.rule; formula; premise_ids } in
        Z3NativeMain.result_text (P.check_document {
          P.declarations = []; expressions = []; assertions = [negation];
          entries = [entry U.Asserted negation []; entry U.RewriteRule rewrite [];
                     entry U.UnitResolution Z3ResolutionProofTheory.false_expr [Z.zero; Z.one]];
          root = Z.of_int 2 })
    | _ -> failwith "expected a rewrite and its negation" in
  let accept ?binders declarations left right =
    incr accepted;
    let name = left ^ " -> " ^ right in
    let conclusion, a, b = step ?binders declarations left right in
    require (CR.equivalent a b) ("conditional comparison rewrite rejected: " ^ name);
    require (U.check_step U.RewriteRule conclusion [])
      ("conditional comparison rewrite not certified: " ^ name);
    require (not (U.check_step U.RewriteRule conclusion [conclusion]))
      ("conditional comparison rewrite ignored an unexpected premise: " ^ name);
    require (pending conclusion = Some Z.zero)
      ("conditional comparison rewrite left an obligation: " ^ name);
    if binders = None then
      require (outcome declarations left right = "ACCEPT")
        ("conditional comparison refutation was not ACCEPT: " ^ name) in
  let uncertified ?binders what declarations left right =
    let name = left ^ " -> " ^ right in
    let conclusion, a, b = step ?binders declarations left right in
    require (not (CR.equivalent a b)) (what ^ " accepted by the conditional rule: " ^ name);
    require (not (U.check_step U.RewriteRule conclusion [])) (what ^ " certified: " ^ name);
    require (pending conclusion = Some Z.one) (what ^ " was not left pending: " ^ name);
    if binders = None then
      require (outcome declarations left right = "PARTIAL 1")
        (what ^ " did not give a PARTIAL 1 refutation: " ^ name) in
  let reject ?binders declarations left right =
    incr invalid;
    uncertified ?binders "invalid conditional comparison rewrite" declarations left right in
  let outside ?binders declarations left right =
    incr unsupported;
    uncertified ?binders "unsupported conditional comparison shape" declarations left right in
  let accept_terms what d a b =
    incr terms_accepted;
    let conclusion = conclusion_of d a b in
    require (CR.equivalent a b) ("conditional comparison terms rejected: " ^ what);
    require (U.check_step U.RewriteRule conclusion []) ("conditional comparison terms not certified: " ^ what);
    require (pending conclusion = Some Z.zero) ("conditional comparison terms left an obligation: " ^ what) in
  let reject_terms what d a b =
    incr terms_invalid;
    let conclusion = conclusion_of d a b in
    require (not (CR.equivalent a b)) ("invalid conditional comparison terms accepted: " ^ what);
    require (not (U.check_step U.RewriteRule conclusion []))
      ("invalid conditional comparison terms certified: " ^ what);
    require (pending conclusion <> Some Z.zero)
      ("invalid conditional comparison terms left no obligation: " ^ what) in
  let rec map_term f e =
    match f e with
    | Some replacement -> replacement
    | None ->
        (match e with
         | A.App (decl, args) -> A.App (decl, List.map (map_term f) args)
         | A.Quantifier (kind, sorts, sort, body) -> A.Quantifier (kind, sorts, sort, map_term f body)
         | A.Var _ -> e) in
  List.iter (fun (s, zero, one, two, three, minus_one, minus_two) ->
    let f fmt = Printf.sprintf fmt in
    let d = f "(declare-const p Bool)(declare-const q Bool)(declare-const x %s)\
               (declare-const y %s)(declare-fun h (%s) %s)" s s s s in
    (* A then-branch numeral whose comparison is false gives (and (not c) ...), one whose
       comparison is true gives (or c ...), for >=, <=, <, > and =. *)
    let source = f "(>= (ite p %s x) %s)" zero one in
    let target = f "(and (not p) (>= x %s))" one in
    accept d source target;
    accept d (f "(>= (ite p %s x) %s)" three one) (f "(or p (>= x %s))" one);
    accept d (f "(<= (ite p %s x) %s)" one two) (f "(or p (<= x %s))" two);
    accept d (f "(<= (ite p %s x) %s)" three one) (f "(and (not p) (<= x %s))" one);
    accept d (f "(< (ite p %s x) %s)" zero one) (f "(or p (< x %s))" one);
    accept d (f "(> (ite p %s x) %s)" zero one) (f "(and (not p) (> x %s))" one);
    accept d (f "(= (ite p %s x) %s)" three one) (f "(and (not p) (= x %s))" one);
    (* A numeral else branch: the guard's polarity is swapped. *)
    accept d (f "(>= (ite p x %s) %s)" zero one) (f "(and p (>= x %s))" one);
    accept d (f "(>= (ite p x %s) %s)" three one) (f "(or (not p) (>= x %s))" one);
    (* Negative numerals, the conditional on the right, and a negated comparison. *)
    accept d (f "(>= (ite p %s x) %s)" minus_two minus_one) (f "(and (not p) (>= x %s))" minus_one);
    accept d (f "(<= %s (ite p %s x))" one zero) (f "(and (not p) (<= %s x))" one);
    accept d (f "(not (>= (ite p %s x) %s))" zero one) (f "(or p (not (>= x %s)))" one);
    (* z3test issue-963: both branches numerals under a compound guard, with the raw comparison
       of the else branch on the right; and the shifted form 1 + (ite ...) >= -1. *)
    let guard = f "(and (= %s %s) (= x y))" zero zero in
    accept d (f "(>= (ite %s %s %s) %s)" guard zero minus_one zero)
      (f "(or %s (>= %s %s))" guard minus_one zero);
    accept d (f "(>= (+ %s (ite %s %s %s)) %s)" one guard zero minus_one minus_one)
      (f "(or %s (>= %s %s))" guard minus_one minus_two);
    (* The shifted form with an opaque else branch: (or false (>= x -1)) and (>= (+ 1 x) 0)
       are compared after the literal false is dropped. *)
    accept d (f "(>= (+ %s (ite p %s x)) %s)" one zero zero) (f "(or p (>= x %s))" minus_one);
    (* z3test string6: a conditional else branch stays inside the comparison. *)
    accept d (f "(>= (ite p %s (ite q %s %s)) %s)" zero one minus_one zero)
      (f "(or p (>= (ite q %s %s) %s))" one minus_one zero);
    accept d (f "(>= (ite p %s (ite q %s x)) %s)" zero three one)
      (f "(and (not p) (or q (>= x %s)))" one);
    (* The split guard inside the compound guard of a nested conditional: its absorbing
       literal decides that guard. *)
    accept d (f "(>= (ite p %s (ite (and p q) %s x)) %s)" zero three one) target;
    accept d (f "(>= (ite p (ite (or p q) %s %s) x) %s)" zero three one) target;
    (* Wrong guard polarity, reversed branches, or and and against the ground comparison, and a
       true ground comparison taken as false. *)
    reject d source (f "(and p (>= x %s))" one);
    reject d (f "(>= (ite p x %s) %s)" zero one) target;
    reject d source (f "(or p (>= x %s))" one);
    reject d source (f "(or (not p) (>= x %s))" one);
    reject d (f "(>= (ite p %s x) %s)" three one) (f "(and (not p) (>= x %s))" one);
    reject d (f "(<= (ite p %s x) %s)" one two) (f "(and (not p) (<= x %s))" two);
    (* Another rest argument or bound, both mutated, and an off-by-one shift. *)
    reject d source (f "(and (not p) (>= y %s))" one);
    reject d source (f "(and (not p) (>= x %s))" two);
    reject d source (f "(or p (>= y %s))" one);
    reject d (f "(>= (+ %s (ite p %s x)) %s)" one zero zero) (f "(or p (>= x %s))" zero);
    reject d (f "(>= (+ %s (ite %s %s %s)) %s)" one guard zero minus_one one)
      (f "(or %s (>= %s %s))" guard minus_one minus_two);
    (* Another relation, strict for non-strict, and a strict source. *)
    reject d source (f "(and (not p) (<= x %s))" one);
    reject d source (f "(and (not p) (> x %s))" one);
    reject d (f "(> (ite p %s x) %s)" zero one) target;
    reject d (f "(= (ite p %s x) %s)" zero one) (f "(and (not p) (>= x %s))" one);
    (* A branch that is not a numeral has no ground comparison. *)
    reject d (f "(>= (ite p y x) %s)" one) target;
    reject d (f "(>= (ite p (h x) x) %s)" one) target;
    let named = f "%s(declare-const |%s| %s)" d zero s in
    reject named (f "(>= (ite p |%s| x) %s)" zero one) target;
    (* Wrong conclusions: an extra disjunct, a dropped guard, a dropped comparison, false. *)
    reject d (f "(>= (ite p %s x) %s)" three one) (f "(or p (>= x %s) q)" one);
    reject d source (f "(>= x %s)" one);
    reject d source "(not p)";
    reject d source "false";
    (* Atoms and guards that are bound variables of an enclosing quantifier: the same variables
       on both sides are accepted; another variable is another atom or guard. *)
    let binders = f "(x %s) (y %s)" s s in
    let bound_source = f "(>= (ite (> y %s) %s x) %s)" two zero one in
    let bound_target = f "(and (not (> y %s)) (>= x %s))" two one in
    accept ~binders d bound_source bound_target;
    reject ~binders d bound_source (f "(and (not (> x %s)) (>= x %s))" two one);
    reject ~binders d bound_source (f "(and (not (> y %s)) (>= y %s))" two one);
    let open_d, open_a, open_b = equation ~binders d bound_source bound_target in
    let shift = map_term (function
        | A.Var (index, sort) -> Some (A.Var (Z.succ index, sort))
        | _ -> None) in
    require (shift open_a <> open_a && shift open_b <> open_b)
      "the conditional comparison body has no bound variables";
    accept_terms (f "%s: bound variables shifted on both sides" s) open_d (shift open_a) (shift open_b);
    reject_terms (f "%s: bound variables shifted in the target" s) open_d open_a (shift open_b);
    reject_terms (f "%s: bound variables shifted in the source" s) open_d (shift open_a) open_b;
    (* A guard under a binder of the rewritten terms is not replaced, so this valid step stays
       pending. *)
    outside d (f "(forall ((z %s)) (>= (ite (> z %s) %s x) %s))" s two zero one)
      (f "(forall ((z %s)) (and (not (> z %s)) (>= x %s)))" s two one);
    (* Each numeral of an accepted step, replaced by a numeral of another value or sort, a
       malformed numeral, or an uninterpreted constant, leaves the step uncertified. *)
    let sort = A.BaseSort s in
    let other = A.BaseSort (if s = "Int" then "Real" else "Int") in
    let is_numeral e = LA.numeral e <> None in
    let zd, a, b = equation d source target in
    require (CR.equivalent a b) ("step with canonical numerals rejected: " ^ source);
    let numerals = ref [] in
    ignore (map_term (fun e -> if is_numeral e then (numerals := e :: !numerals; Some e) else None)
              (A.App (zd, [a; b])));
    let numerals = List.rev !numerals in
    require (List.length numerals = 3) "expected three numerals in the step";
    List.iteri (fun index numeral ->
        let decl, n, denominator = match numeral with
          | A.App (decl, []) ->
              (match decl.A.int_params with
               | [n; denominator] -> decl, n, denominator
               | _ -> failwith "expected numeral parameters")
          | _ -> failwith "expected a numeral" in
        List.iter (fun (kind, bad) ->
            let seen = ref (-1) in
            let replace = map_term (fun e ->
                if is_numeral e then begin
                  incr seen;
                  Some (if !seen = index then A.App (bad, []) else e)
                end else None) in
            let a' = replace a in
            let b' = replace b in
            require (a' <> a || b' <> b) "the numeral was not replaced";
            reject_terms (f "%s: %s at numeral %d" s kind index) zd a' b')
          [ "the next numeral", { decl with A.int_params = [Z.succ n; denominator] };
            "a numeral of the other sort", { decl with A.range = other };
            "an uninterpreted numeral", { decl with A.interp = None };
            "a numeral without a denominator", { decl with A.int_params = [n] };
            "a numeral with a domain", { decl with A.domain = [sort] };
            "an uninterpreted constant with the numeral's name",
              { A.decl_name = decl.A.decl_name; domain = []; range = sort; interp = None;
                int_params = [] } ])
      numerals)
    ["Int", "0", "1", "2", "3", "(- 1)", "(- 2)";
     "Real", "0.0", "1.0", "2.0", "3.0", "(- 1.0)", "(- 2.0)"];
  (* z3test z3.12: a guarded division, and Real fractions decided exactly. *)
  let reals = "(declare-const a Real)(declare-const b Real)" in
  accept reals "(>= (ite (= b 0.0) 0.0 (/ a b)) 1.0)" "(and (not (= b 0.0)) (>= (/ a b) 1.0))";
  accept reals "(<= (ite (= b 0.0) 0.5 a) 0.25)" "(and (not (= b 0.0)) (<= a 0.25))";
  accept reals "(<= (ite (= b 0.0) (/ 1.0 4.0) a) 0.25)" "(or (= b 0.0) (<= a 0.25))";
  reject reals "(<= (ite (= b 0.0) 0.5 a) 0.25)" "(or (= b 0.0) (<= a 0.25))";
  (* A division by zero is not a numeral. *)
  reject reals "(>= (ite (= b 0.0) (/ 1.0 0.0) a) 1.0)" "(and (not (= b 0.0)) (>= a 1.0))";
  Printf.printf "  conditional comparison rewrites: %d accepted, %d invalid, %d outside the shape; \
                 rebuilt terms: %d accepted, %d invalid\n%!"
    !accepted !invalid !unsupported !terms_accepted !terms_invalid

let bv_extract_rewrites () =
  let module BX = Z3BvExtract in
  let module BV = Z3BvLemma in
  let c = context () in
  let accepted = ref 0 and invalid = ref 0 and unsupported = ref 0 and terms_invalid = ref 0 in
  let declarations =
    "(declare-const p Bool)(declare-const q Bool)(declare-fun f ((_ BitVec 8)) Bool)\
     (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(declare-const z (_ BitVec 8))\
     (declare-const u (_ BitVec 16))(declare-const k (_ BitVec 7))(declare-const bit (_ BitVec 1))\
     (declare-const m (_ BitVec 66))(declare-const n (_ BitVec 66))\
     (declare-const big (_ BitVec 4096))(declare-const big2 (_ BitVec 4096))" in
  let equation ?(binders = "") left right =
    let source =
      if binders = "" then Printf.sprintf "%s(assert (= %s %s))" declarations left right
      else Printf.sprintf "%s(assert (forall (%s) (= %s %s)))" declarations binders left right in
    let inputs = parse c source in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match B.cached_expression st (List.hd inputs) with
    | A.App (d, [a; b]) when binders = "" -> d, a, b
    | A.Quantifier (_, _, _, A.App (d, [a; b])) when binders <> "" -> d, a, b
    | _ -> failwith "expected a bit-vector extraction rewrite equation" in
  let conclusion_of d a b =
    match U.classify_fact (A.App (d, [a; b])) with
    | Some conclusion -> conclusion
    | None -> failwith "expected a typed bit-vector extraction rewrite conclusion" in
  let pending conclusion =
    match U.check_node [] { U.kind = U.RewriteRule; conclusion = conclusion; premises = [] } with
    | Some (_, obligations) -> Some obligations
    | None -> None in
  let outcome left right =
    let inputs = parse c (Printf.sprintf "%s(assert (= %s %s))(assert (not (= %s %s)))"
                            declarations left right left right) in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    match List.map (B.cached_expression st) inputs with
    | [rewrite; negation] ->
        let entry rule formula premise_ids = { P.rule; formula; premise_ids } in
        Z3NativeMain.result_text (P.check_document {
          P.declarations = []; expressions = []; assertions = [negation];
          entries = [entry U.Asserted negation []; entry U.RewriteRule rewrite [];
                     entry U.UnitResolution Z3ResolutionProofTheory.false_expr [Z.zero; Z.one]];
          root = Z.of_int 2 })
    | _ -> failwith "expected a rewrite and its negation" in
  let accept left right =
    incr accepted;
    let name = left ^ " -> " ^ right in
    let d, a, b = equation left right in
    let conclusion = conclusion_of d a b in
    require (BX.check a b) ("extraction rewrite rejected: " ^ name);
    require (U.check_step U.RewriteRule conclusion []) ("extraction rewrite not certified: " ^ name);
    require (not (U.check_step U.RewriteRule conclusion [conclusion]))
      ("extraction rewrite ignored an unexpected premise: " ^ name);
    require (pending conclusion = Some Z.zero) ("extraction rewrite left an obligation: " ^ name);
    require (outcome left right = "ACCEPT") ("extraction refutation was not ACCEPT: " ^ name) in
  let uncertified ?binders what left right =
    let name = left ^ " -> " ^ right in
    let d, a, b = equation ?binders left right in
    let conclusion = conclusion_of d a b in
    require (not (BX.check a b)) (what ^ " accepted by the extraction rule: " ^ name);
    require (not (U.check_step U.RewriteRule conclusion [])) (what ^ " certified: " ^ name);
    require (pending conclusion = Some Z.one) (what ^ " was not left pending: " ^ name);
    if binders = None then
      require (outcome left right = "PARTIAL 1")
        (what ^ " did not give a PARTIAL 1 refutation: " ^ name) in
  let reject left right =
    incr invalid;
    uncertified "invalid extraction rewrite" left right in
  let outside ?binders left right =
    incr unsupported;
    uncertified ?binders "unsupported extraction shape" left right in
  let reject_terms what d a b =
    incr terms_invalid;
    let conclusion = conclusion_of d a b in
    require (not (BX.check a b)) ("invalid extraction terms accepted: " ^ what);
    require (not (U.check_step U.RewriteRule conclusion []))
      ("invalid extraction terms certified: " ^ what);
    require (pending conclusion <> Some Z.zero)
      ("invalid extraction terms left no obligation: " ^ what) in
  (* Low bits of sums and products, binary and n-ary, up to the full width and at 4096 bits. *)
  accept "((_ extract 3 0) (bvadd x y))" "(bvadd ((_ extract 3 0) x) ((_ extract 3 0) y))";
  accept "((_ extract 3 0) (bvmul x y))" "(bvmul ((_ extract 3 0) x) ((_ extract 3 0) y))";
  accept "((_ extract 3 0) (bvadd x y z))"
    "(bvadd ((_ extract 3 0) x) ((_ extract 3 0) y) ((_ extract 3 0) z))";
  accept "((_ extract 5 0) (bvmul x y z))"
    "(bvmul ((_ extract 5 0) x) ((_ extract 5 0) y) ((_ extract 5 0) z))";
  accept "((_ extract 0 0) (bvadd x y))" "(bvadd ((_ extract 0 0) x) ((_ extract 0 0) y))";
  accept "((_ extract 7 0) (bvadd x y))" "(bvadd ((_ extract 7 0) x) ((_ extract 7 0) y))";
  accept "((_ extract 0 0) (bvadd big big2))"
    "(bvadd ((_ extract 0 0) big) ((_ extract 0 0) big2))";
  (* The shapes of z3test 6079-8: a numeral plus a conditional, at widths 7 and 66. *)
  accept "((_ extract 4 0) (bvadd (_ bv1 7) (ite (= k (_ bv0 7)) k (_ bv0 7))))"
    "(bvadd ((_ extract 4 0) (_ bv1 7)) ((_ extract 4 0) (ite (= k (_ bv0 7)) k (_ bv0 7))))";
  accept "((_ extract 6 0) (bvadd (_ bv2 66) (ite (= m n) m (_ bv0 66))))"
    "(bvadd ((_ extract 6 0) (_ bv2 66)) ((_ extract 6 0) (ite (= m n) m (_ bv0 66))))";
  (* An argument that is itself an extraction is extracted from its operand, as by
     mk_extract_proc. *)
  accept "((_ extract 3 0) (bvmul ((_ extract 11 4) u) x))"
    "(bvmul ((_ extract 7 4) u) ((_ extract 3 0) x))";
  accept "((_ extract 2 0) (bvadd ((_ extract 15 8) u) ((_ extract 7 0) u)))"
    "(bvadd ((_ extract 10 8) u) ((_ extract 2 0) u))";
  (* Any slice of a conditional, with the same guard. *)
  accept "((_ extract 5 2) (ite p x y))" "(ite p ((_ extract 5 2) x) ((_ extract 5 2) y))";
  accept "((_ extract 3 0) (ite (f x) (ite q x y) z))"
    "(ite (f x) ((_ extract 3 0) (ite q x y)) ((_ extract 3 0) z))";
  accept "((_ extract 1 1) (ite p ((_ extract 9 2) u) x))"
    "(ite p ((_ extract 3 3) u) ((_ extract 1 1) x))";
  accept "((_ extract 7 7) (ite (bvule x y) x y))"
    "(ite (bvule x y) ((_ extract 7 7) x) ((_ extract 7 7) y))";
  accept "((_ extract 6 0) (ite (= m n) (_ bv1 66) (_ bv0 66)))"
    "(ite (= m n) ((_ extract 6 0) (_ bv1 66)) ((_ extract 6 0) (_ bv0 66)))";
  accept "((_ extract 4095 4094) (ite p big big2))"
    "(ite p ((_ extract 4095 4094) big) ((_ extract 4095 4094) big2))";
  (* Bits above the lowest depend on the carries out of the discarded bits:
     ((_ extract 1 1) (bvadd #b01 #b01)) is #b1, the distributed sum is #b0. *)
  reject "((_ extract 1 1) (bvadd x y))" "(bvadd ((_ extract 1 1) x) ((_ extract 1 1) y))";
  reject "((_ extract 1 1) (bvadd #b01 #b01))"
    "(bvadd ((_ extract 1 1) #b01) ((_ extract 1 1) #b01))";
  reject "((_ extract 3 2) (bvmul x y))" "(bvmul ((_ extract 3 2) x) ((_ extract 3 2) y))";
  reject "((_ extract 7 4) (bvadd x y z))"
    "(bvadd ((_ extract 7 4) x) ((_ extract 7 4) y) ((_ extract 7 4) z))";
  reject "((_ extract 5 1) (bvadd (_ bv1 7) (ite (= k (_ bv0 7)) k (_ bv0 7))))"
    "(bvadd ((_ extract 5 1) (_ bv1 7)) ((_ extract 5 1) (ite (= k (_ bv0 7)) k (_ bv0 7))))";
  (* Another slice, argument, operation or arity, division, and a composed extraction
     without its offset. *)
  reject "((_ extract 3 0) (bvadd x y))" "(bvadd ((_ extract 3 0) x) ((_ extract 4 1) y))";
  reject "((_ extract 3 0) (bvadd x y))" "(bvadd ((_ extract 3 0) x) ((_ extract 3 0) z))";
  reject "((_ extract 3 0) (bvadd x y))" "(bvmul ((_ extract 3 0) x) ((_ extract 3 0) y))";
  reject "((_ extract 3 0) (bvadd x y z))" "(bvadd ((_ extract 3 0) x) ((_ extract 3 0) y))";
  reject "((_ extract 3 0) (bvadd x y))"
    "(bvadd ((_ extract 3 0) x) ((_ extract 3 0) y) ((_ extract 3 0) z))";
  reject "((_ extract 3 0) (bvudiv x y))" "(bvudiv ((_ extract 3 0) x) ((_ extract 3 0) y))";
  reject "((_ extract 3 0) (bvmul ((_ extract 11 4) u) x))"
    "(bvmul ((_ extract 3 0) u) ((_ extract 3 0) x))";
  (* A negated, swapped or other guard, another slice or term in a branch, and a composed
     extraction without its offset. *)
  reject "((_ extract 5 2) (ite p x y))" "(ite (not p) ((_ extract 5 2) x) ((_ extract 5 2) y))";
  reject "((_ extract 5 2) (ite p x y))" "(ite p ((_ extract 5 2) y) ((_ extract 5 2) x))";
  reject "((_ extract 5 2) (ite p x y))" "(ite q ((_ extract 5 2) x) ((_ extract 5 2) y))";
  reject "((_ extract 5 2) (ite p x y))" "(ite p ((_ extract 5 2) x) ((_ extract 6 3) y))";
  reject "((_ extract 5 2) (ite p x y))" "(ite p ((_ extract 5 2) x) ((_ extract 5 2) z))";
  reject "((_ extract 1 1) (ite p ((_ extract 9 2) u) x))"
    "(ite p ((_ extract 1 1) u) ((_ extract 1 1) x))";
  (* Valid steps outside the shape stay pending: bitwise or, subtraction, reordered or
     evaluated arguments, two steps at once, and terms with variables bound outside them
     (Z3BvExtract checks closed terms only). The bounded evaluation of Z3BvExhaustive does not
     decide them either: bvor, bvsub and ite terms are opaque leaves, and the other leaves have
     more than 12 bits; the evaluated-numeral step over a 7-bit leaf is certified by that
     evaluation (checked-bounded-bit-vector-evaluation), so it is tested here at 66 bits. *)
  outside "((_ extract 5 2) (bvor x y))" "(bvor ((_ extract 5 2) x) ((_ extract 5 2) y))";
  outside "((_ extract 3 0) (bvsub x y))" "(bvsub ((_ extract 3 0) x) ((_ extract 3 0) y))";
  outside "((_ extract 3 0) (bvadd x y))" "(bvadd ((_ extract 3 0) y) ((_ extract 3 0) x))";
  outside "((_ extract 4 0) (bvadd (_ bv1 66) m))" "(bvadd #b00001 ((_ extract 4 0) m))";
  outside "((_ extract 3 0) (bvadd x (ite p y z)))"
    "(bvadd ((_ extract 3 0) x) (ite p ((_ extract 3 0) y) ((_ extract 3 0) z)))";
  outside ~binders:"(a (_ BitVec 8)) (b (_ BitVec 8))"
    "((_ extract 3 0) (bvadd a b))" "(bvadd ((_ extract 3 0) a) ((_ extract 3 0) b))";
  (* Bits of a binary concatenation of x (the high bits) and y (the low bits), as mk_extract
     splits it: within y, within x, or a concatenation of low bits of x and high bits of y,
     keeping an argument whose bits are all taken; at the boundary (bit 7 of y, bit 0 of x),
     for the full width, and at 4096 bits. *)
  accept "((_ extract 7 0) (concat x y))" "y";
  accept "((_ extract 5 2) (concat x y))" "((_ extract 5 2) y)";
  accept "((_ extract 7 7) (concat x y))" "((_ extract 7 7) y)";
  accept "((_ extract 15 8) (concat x y))" "x";
  accept "((_ extract 8 8) (concat x y))" "((_ extract 0 0) x)";
  accept "((_ extract 14 9) (concat x y))" "((_ extract 6 1) x)";
  accept "((_ extract 9 4) (concat x y))" "(concat ((_ extract 1 0) x) ((_ extract 7 4) y))";
  accept "((_ extract 8 7) (concat x y))" "(concat ((_ extract 0 0) x) ((_ extract 7 7) y))";
  accept "((_ extract 15 4) (concat x y))" "(concat x ((_ extract 7 4) y))";
  accept "((_ extract 9 0) (concat x y))" "(concat ((_ extract 1 0) x) y)";
  accept "((_ extract 15 0) (concat x y))" "(concat x y)";
  accept "((_ extract 3 1) (concat x ((_ extract 11 4) u)))" "((_ extract 7 5) u)";
  accept "((_ extract 4095 4095) (concat bit ((_ extract 4094 0) big)))" "bit";
  accept "((_ extract 4095 1) (concat bit ((_ extract 4094 0) big)))"
    "(concat bit ((_ extract 4094 1) big))";
  (* The shapes of z3test 6079-8: a bit below an extraction, and a numeral bit above a
     conditional. *)
  accept "((_ extract 14 14) (concat ((_ extract 15 2) u) bit))" "((_ extract 15 15) u)";
  accept "((_ extract 6 3) (concat ((_ extract 15 10) u) bit))" "((_ extract 15 12) u)";
  accept "((_ extract 2 0) (concat ((_ extract 7 2) u) bit))" "(concat ((_ extract 3 2) u) bit)";
  accept "((_ extract 0 0) (concat ((_ extract 7 2) u) bit))" "bit";
  accept "((_ extract 8 8) (concat #b0 (ite p x y)))" "#b0";
  accept "((_ extract 7 0) (concat #b0 (ite p x y)))" "(ite p x y)";
  accept "((_ extract 8 1) (concat #b0 (ite p x y)))" "(concat #b0 ((_ extract 7 1) (ite p x y)))";
  (* Another argument, offset, order or split, a dropped or an extra argument, another
     constant, and a composed extraction without its offset. *)
  reject "((_ extract 3 0) (concat x y))" "((_ extract 3 0) x)";
  reject "((_ extract 11 8) (concat x y))" "((_ extract 3 0) y)";
  reject "((_ extract 14 9) (concat x y))" "((_ extract 7 2) x)";
  reject "((_ extract 14 9) (concat x y))" "((_ extract 6 1) y)";
  reject "((_ extract 9 4) (concat x y))" "(concat ((_ extract 7 4) y) ((_ extract 1 0) x))";
  reject "((_ extract 9 4) (concat x y))" "(concat ((_ extract 1 0) y) ((_ extract 7 4) x))";
  reject "((_ extract 9 4) (concat x y))" "(concat ((_ extract 2 0) x) ((_ extract 7 5) y))";
  reject "((_ extract 9 4) (concat x y))" "(concat ((_ extract 2 1) x) ((_ extract 7 4) y))";
  reject "((_ extract 9 4) (concat x y))" "(concat ((_ extract 1 0) x) ((_ extract 6 3) y))";
  reject "((_ extract 9 4) (concat x y))" "(concat ((_ extract 1 0) x) ((_ extract 7 4) z))";
  reject "((_ extract 11 4) (concat x y))" "x";
  reject "((_ extract 11 4) (concat x y))"
    "(concat ((_ extract 3 0) x) ((_ extract 7 6) y) ((_ extract 5 4) z))";
  reject "((_ extract 15 0) (concat x y))" "(concat y x)";
  reject "((_ extract 8 1) (concat #b0 (ite p x y)))" "(concat #b1 ((_ extract 7 1) (ite p x y)))";
  reject "((_ extract 14 14) (concat ((_ extract 15 2) u) bit))" "((_ extract 13 13) u)";
  (* Valid steps outside the shape stay pending: a concatenation of three arguments on either
     side, and terms with variables bound outside them. *)
  outside "((_ extract 11 4) (concat x y))"
    "(concat ((_ extract 3 0) x) ((_ extract 7 6) y) ((_ extract 5 4) y))";
  outside "((_ extract 11 4) (concat x y z))" "(concat ((_ extract 3 0) y) ((_ extract 7 4) z))";
  outside ~binders:"(a (_ BitVec 8)) (b (_ BitVec 8))"
    "((_ extract 9 4) (concat a b))" "(concat ((_ extract 1 0) a) ((_ extract 7 4) b))";
  (* Declarations of an accepted step replaced by malformed or other ones. *)
  let with_decl e g = match e with
    | A.App (decl, args) -> A.App (g decl, args)
    | _ -> failwith "expected an application" in
  let first_argument e g = match e with
    | A.App (decl, arg :: rest) -> A.App (decl, with_decl arg g :: rest)
    | _ -> failwith "expected an application with arguments" in
  let params ps decl = { decl with A.int_params = List.map Z.of_int ps } in
  let interp op decl = { decl with A.interp = op } in
  let domain s decl = { decl with A.domain = [A.BaseSort s] } in
  let d, a, b = equation "((_ extract 3 0) (bvadd x y))"
                  "(bvadd ((_ extract 3 0) x) ((_ extract 3 0) y))" in
  require (BX.check a b) "the unmodified sum step was rejected";
  List.iter (fun (what, a', b') ->
      require (a' <> a || b' <> b) ("the step was not modified: " ^ what);
      reject_terms what d a' b')
    [ "source extraction of bits 3..1", with_decl a (params [8; 3; 1]), b;
      "source extraction from width 9", with_decl a (params [9; 3; 0]), b;
      "source extraction from width 0", with_decl a (params [0; 3; 0]), b;
      "source extraction of bits 8..5 of width 8", with_decl a (params [8; 8; 5]), b;
      "source extraction with low bit 4 above high bit 3", with_decl a (params [8; 3; 4]), b;
      "source extraction with two parameters", with_decl a (params [8; 3]), b;
      "source extraction with domain BV9", with_decl a (domain "BV9"), b;
      "uninterpreted source extraction", with_decl a (interp None), b;
      "source extraction of two arguments",
        (match a with A.App (e, [s]) -> A.App (e, [s; s]) | _ -> failwith "expected an extraction"), b;
      "source subtraction named bvadd", first_argument a (interp (Some BV.op_sub)), b;
      "uninterpreted source sum", first_argument a (interp None), b;
      "binary source sum of three arguments",
        (match a with
         | A.App (e, [A.App (g, [x1; x2])]) -> A.App (e, [A.App (g, [x1; x2; x2])])
         | _ -> failwith "expected an extracted sum"), b;
      "target sum of width 5", a, with_decl b (params [5]);
      "target sum of width 0", a, with_decl b (params [0]);
      "target product", a, with_decl b (interp (Some BV.op_mul));
      "uninterpreted target sum", a, with_decl b (interp None);
      "binary target sum of three arguments", a,
        (match b with A.App (g, [y1; y2]) -> A.App (g, [y1; y2; y2]) | _ -> failwith "expected a sum");
      "target extraction of bits 4..1", a, first_argument b (params [8; 4; 1]);
      "target extraction from width 9", a, first_argument b (params [9; 3; 0]);
      "target extraction of bits 8..5 of width 8", a, first_argument b (params [8; 8; 5]);
      "target extraction with low bit 4 above high bit 3", a, first_argument b (params [8; 3; 4]);
      "uninterpreted target extraction", a, first_argument b (interp None);
      "target extraction of no argument", a,
        (match b with
         | A.App (g, A.App (e, [_]) :: rest) -> A.App (g, A.App (e, []) :: rest)
         | _ -> failwith "expected a sum of extractions") ];
  (* The same step with x a bound variable (de Bruijn index 0) is outside the closed-term
     rule, and with index 0 in the source but 1 in the target it is invalid. *)
  let rec map_term g e =
    match g e with
    | Some replacement -> replacement
    | None ->
        (match e with
         | A.App (decl, args) -> A.App (decl, List.map (map_term g) args)
         | A.Quantifier (kind, sorts, sort, body) -> A.Quantifier (kind, sorts, sort, map_term g body)
         | A.Var _ -> e) in
  let x = match b with
    | A.App (_, A.App (_, [x]) :: _) -> x
    | _ -> failwith "expected a sum of extractions" in
  let bind index = map_term (fun e ->
      if e = x then Some (A.Var (Z.of_int index, A.BaseSort "BV8")) else None) in
  require (bind 0 a <> a && bind 0 b <> b) "x was not replaced by a bound variable";
  List.iter (fun (what, a', b') -> reject_terms what d a' b')
    [ "x bound on both sides", bind 0 a, bind 0 b;
      "x bound with index 0 in the source and 1 in the target", bind 0 a, bind 1 b ];
  let d, a, b = equation "((_ extract 5 2) (ite p x y))"
                  "(ite p ((_ extract 5 2) x) ((_ extract 5 2) y))" in
  require (BX.check a b) "the unmodified conditional step was rejected";
  List.iter (fun (what, a', b') ->
      require (a' <> a || b' <> b) ("the step was not modified: " ^ what);
      reject_terms what d a' b')
    [ "uninterpreted source conditional", first_argument a (interp None), b;
      "uninterpreted target conditional", a, with_decl b (interp None);
      "target conditional with a parameter", a, with_decl b (params [8]);
      "source extraction of bits 5..3", with_decl a (params [8; 5; 3]), b;
      "target branch extraction of bits 6..3", a, (match b with
        | A.App (g, [guard; t; e]) -> A.App (g, [guard; with_decl t (params [8; 6; 3]); e])
        | _ -> failwith "expected a conditional");
      "target conditional of two arguments", a, (match b with
        | A.App (g, [guard; t; _]) -> A.App (g, [guard; t])
        | _ -> failwith "expected a conditional");
      "source conditional of four arguments", (match a with
        | A.App (e, [A.App (g, [guard; t; u])]) -> A.App (e, [A.App (g, [guard; t; u; u])])
        | _ -> failwith "expected an extracted conditional"), b ];
  (* A concatenation step with malformed or other declarations, and with x bound. *)
  let d, a, b = equation "((_ extract 9 4) (concat x y))"
                  "(concat ((_ extract 1 0) x) ((_ extract 7 4) y))" in
  require (BX.check a b) "the unmodified concatenation step was rejected";
  List.iter (fun (what, a', b') ->
      require (a' <> a || b' <> b) ("the step was not modified: " ^ what);
      reject_terms what d a' b')
    [ "source concatenation of widths 8 and 9", first_argument a (params [8; 9]), b;
      "source concatenation of widths 9 and 7", first_argument a (params [9; 7]), b;
      "source concatenation of widths 0 and 8", first_argument a (params [0; 8]), b;
      "source concatenation with one parameter", first_argument a (params [16]), b;
      "source concatenation with domain BV8", first_argument a (domain "BV8"), b;
      "uninterpreted source concatenation", first_argument a (interp None), b;
      "source bitwise or named concat", first_argument a (interp (Some BV.op_or)), b;
      "source concatenation of three arguments",
        (match a with
         | A.App (e, [A.App (g, [x1; x2])]) -> A.App (e, [A.App (g, [x1; x2; x2])])
         | _ -> failwith "expected an extracted concatenation"), b;
      "source extraction of bits 10..4", with_decl a (params [16; 10; 4]), b;
      "source extraction from width 17", with_decl a (params [17; 9; 4]), b;
      "source extraction of bits 16..11 of width 16", with_decl a (params [16; 16; 11]), b;
      "source extraction with low bit 10 above high bit 9", with_decl a (params [16; 9; 10]), b;
      "target concatenation of widths 3 and 3", a, with_decl b (params [3; 3]);
      "target concatenation of widths 0 and 6", a, with_decl b (params [0; 6]);
      "uninterpreted target concatenation", a, with_decl b (interp None);
      "target concatenation of three arguments", a,
        (match b with A.App (g, [y1; y2]) -> A.App (g, [y1; y2; y2])
         | _ -> failwith "expected a concatenation");
      "target concatenation of one argument", a,
        (match b with A.App (g, [y1; _]) -> A.App (g, [y1])
         | _ -> failwith "expected a concatenation");
      "target extraction of bits 2..1", a, first_argument b (params [8; 2; 1]);
      "target extraction of bits 8..7 of width 8", a, first_argument b (params [8; 8; 7]);
      "target extraction with low bit 2 above high bit 1", a, first_argument b (params [8; 1; 2]);
      "uninterpreted target extraction", a, first_argument b (interp None) ];
  let x = match a with
    | A.App (_, [A.App (_, [x; _])]) -> x
    | _ -> failwith "expected an extracted concatenation" in
  let bind index = map_term (fun e ->
      if e = x then Some (A.Var (Z.of_int index, A.BaseSort "BV8")) else None) in
  require (bind 0 a <> a && bind 0 b <> b) "x was not replaced by a bound variable";
  List.iter (fun (what, a', b') -> reject_terms what d a' b')
    [ "x bound on both sides of a concatenation step", bind 0 a, bind 0 b;
      "x bound with index 0 in the concatenation and 1 in the target", bind 0 a, bind 1 b ];
  (* An argument kept whole for an extraction of fewer bits: the source extraction declared
     with the parameters and range of bits 3..0 (or 15..9) of the concatenation. The rule
     rejects the terms, and the kernel does not classify an equation of a 4-bit (7-bit) and
     an 8-bit term. *)
  let range s decl = { decl with A.range = A.BaseSort s } in
  let narrower what d a' b =
    incr terms_invalid;
    require (not (BX.check a' b)) ("invalid extraction terms accepted: " ^ what);
    require (U.classify_fact (A.App (d, [a'; b])) = None)
      ("an equation of terms of different widths was classified: " ^ what) in
  let d, a, b = equation "((_ extract 7 0) (concat x y))" "y" in
  require (BX.check a b) "the unmodified low-argument step was rejected";
  narrower "y as the bits 3..0 of the concatenation" d
    (with_decl a (fun e -> range "BV4" (params [16; 3; 0] e))) b;
  let d, a, b = equation "((_ extract 15 8) (concat x y))" "x" in
  require (BX.check a b) "the unmodified high-argument step was rejected";
  narrower "x as the bits 15..9 of the concatenation" d
    (with_decl a (fun e -> range "BV7" (params [16; 15; 9] e))) b;
  Printf.printf "  bit-vector extraction rewrites: %d accepted, %d invalid, %d outside the shape; \
                 %d malformed or open rebuilt terms\n%!"
    !accepted !invalid !unsupported !terms_invalid

let arithmetic_triangle_clauses () =
  let c = context () in
  let check expected clause =
    let input = List.hd (parse c
        ("(declare-const x Real)(declare-const y Real)(assert " ^ clause ^ ")")) in
    let st = B.marshal_expressions (B.empty_state ()) [input] in
    let formula = B.cached_expression st input in
    require (U.checked_theory_lemma (U.Unverified "th-lemma") (U.Holds formula) [] = expected)
      ("incorrect triangle-equality check: " ^ clause);
    require (not (U.checked_theory_lemma (U.Unverified "assumed:nlsat") (U.Holds formula) []))
      "an assumed NLSAT origin bypassed obligation tracking"
  in
  check true "(or (= x y) (not (<= (- x y) 0)) (not (>= (- x y) 0)))";
  check true "(or (= y x) (not (<= (- x y) 0)) (not (>= (- x y) 0)))";
  check true "(or (= x y) (not (>= (- x y) 0)) (not (<= (- x y) 0)))";
  check true "(or (= 1 x) (not (<= x 1)) (not (>= x 1)))";
  check true "(or (not (= x y)) (<= (- x y) 0))";
  check true "(or (not (= x y)) (>= (- x y) 0))";
  check false "(or (not (= x y)) (< (- x y) 0))";
  check false "(or (not (= x y)) (<= (- x y) (- 1)))";
  check false "(or (= x y) (not (< (- x y) 0)) (not (>= (- x y) 0)))";
  check false "(or (= x y) (not (<= (- x y) 0)) (not (<= (- x y) 0)))";
  check false "(or (= x (+ 1 y)) (not (<= (- x y) 0)) (not (>= (- x y) 0)))"

let arithmetic_implication source premises target expected =
    let c = context () in
    let source = source ^
      String.concat "" (List.map (fun e -> "(assert " ^ e ^ ")") (premises @ [target])) in
    let inputs = parse c source in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let judgments = List.map (fun e ->
        Option.get (U.classify_fact (B.cached_expression st e))) inputs in
    let conclusion = List.hd (List.rev judgments) in
    let facts = List.rev (List.tl (List.rev judgments)) in
    require (U.checked_theory_lemma (U.Unverified "th-lemma") conclusion facts = expected)
      ("incorrect arithmetic implication: " ^ source);
    require (not (U.checked_theory_lemma (U.Unverified "assumed:nlsat") conclusion facts))
      "arithmetic implication accepted assumed-origin evidence";
    let premises = List.map (fun conclusion ->
        { U.conclusion = conclusion; hypotheses = [] }) facts in
    require (match U.check_node [] {
        U.kind = U.Unverified "th-lemma"; conclusion = conclusion; premises } with
        | Some (_, pending) -> Z.equal pending (if expected then Z.zero else Z.one)
        | None -> false)
      "arithmetic implication lost its explicit obligation"

let arithmetic_implied_equalities () =
  let check sort = arithmetic_implication
      ("(declare-const x " ^ sort ^ ")(declare-const y " ^ sort ^ ")")
  in
  check "Int" ["(<= x 2)"; "(>= x 2)"] "(= 0 (+ (- 2) x))" true;
  check "Int" ["(not (<= x 2))"; "(not (>= x 4))"] "(= 1 (+ (- 2) x))" true;
  check "Real" ["(not (<= x 2))"; "(not (>= x 4))"] "(= 1 (+ (- 2) x))" false;
  check "Int" ["(<= (+ x y) 3)"; "(>= (+ x y) 3)"; "(= y 1)"] "(= x 2)" true;
  check "Real" ["(<= (* 2 x) 3)"; "(>= (* 4 x) 6)"] "(= x (/ 3 2))" true;
  check "Int" ["(<= x 2)"; "(>= x 2)"] "(= x 3)" false;
  check "Int" ["(<= x 2)"] "(= x 2)" false;
  check "Int" ["(<= x 2)"; "(>= y 2)"] "(= x 2)" false;
  check "Int" ["(<= (+ x y) 3)"; "(>= (+ x y) 3)"; "(= y 1)"] "(= x 1)" false

let arithmetic_implied_bounds () =
  let check sort = arithmetic_implication
      ("(declare-const x " ^ sort ^ ")(declare-const y " ^ sort ^ ")") in
  check "Real" ["(<= (+ (* 2 x) y) 7)"; "(>= y 1)"] "(<= x 3)" true;
  check "Real" ["(<= (+ (* 2 x) y) 7)"; "(>= y 1)"] "(<= x 2)" false;
  check "Int" ["(not (<= (+ (* 2 x) y) 7))"; "(<= y 2)"] "(>= x 3)" true;
  check "Real" ["(not (<= (+ (* 2 x) y) 7))"; "(<= y 2)"] "(>= x 3)" false;
  let declarations = String.concat "" (List.init 19 (fun i ->
      Printf.sprintf "(declare-const x%d Real)" i)) in
  let premises = List.init 18 (fun i ->
      Printf.sprintf "(<= (* 2 x%d) x%d)" i (i + 1)) in
  arithmetic_implication declarations premises "(<= (* 262144 x0) x18)" true;
  arithmetic_implication declarations premises "(<= (* 262145 x0) x18)" false

let arithmetic_inferred_splits () =
  let check sort = arithmetic_implication
      ("(declare-const x " ^ sort ^ ")(declare-const y " ^ sort ^ ")") in
  check "Int" ["(>= (- (* 10 x) (* 10 y)) 1)";
               "(<= (- (* 10 x) (* 10 y)) 9)"] "false" true;
  check "Int" ["(>= (- (* 10 x) (* 10 y)) 52)";
               "(<= (- (* 10 x) (* 10 y)) 59)"] "false" true;
  check "Int" ["(>= (- (* 10 x) (* 10 y)) (- 59))";
               "(<= (- (* 10 x) (* 10 y)) (- 52))"] "false" true;
  check "Real" ["(>= (- (* 10 x) (* 10 y)) 1)";
                "(<= (- (* 10 x) (* 10 y)) 9)"] "false" false;
  check "Int" ["(>= (- (* 10 x) (* 10 y)) 1)";
               "(<= (- (* 10 x) (* 10 y)) 10)"] "false" false

(* Integer rounding (Chvatal-Gomory) cuts. Each accepted refutation holds over the integers but its rational
   relaxation is satisfiable, so no Farkas vector exists; each rejected case is satisfiable (a wrong rounding
   direction, constant or premise set would "refute" it) or needs reasoning beyond one rounding step. The expected
   value is the kernel's decision on the actual premise ASTs. *)
let arithmetic_integer_rounding () =
  let ints = "(declare-const a Int)(declare-const b Int)(declare-const t Int)(declare-const s Int)\
              (declare-const v Int)(declare-const w Int)(declare-const z Int)" in
  let reals = "(declare-const a Real)(declare-const b Real)(declare-const t Real)(declare-const s Real)\
               (declare-const v Real)(declare-const w Real)(declare-const z Real)" in
  let mixed = "(declare-const a Int)(declare-const r Real)" in
  let check source premises expected = arithmetic_implication source premises "false" expected in
  (* The shape of the QF_LIA ring benchmarks: z is fixed to 0, v >= 0, and the carry term 256 t + 256 s + z is
     positive but every variable coefficient of it is a multiple of 256, so it is at least 256 and
     v + 256 t + 256 s exceeds 255. No row has two atoms, so the continued-fraction splits of Z3LpGomory
     do not apply. *)
  let ring = ["(<= (+ v (* 256 t) (* 256 s)) 255)"; "(>= v 0)"; "(>= (+ (* 256 t) (* 256 s) z) 1)";
              "(<= z 0)"; "(>= z 0)"] in
  check ints ring true;
  check ints ["(not (>= (+ v (* 256 t) (* 256 s)) 256))"; "(>= v 0)"; "(not (<= (+ (* 256 t) (* 256 s) z) 0))";
              "(<= z 0)"; "(>= z 0)"] true;
  check ints ["(<= (+ v (* 256 t) (* 256 s)) 255)"; "(>= v 0)"; "(>= (+ (* 256 t) (* 256 s) z) 1)"; "(= z 0)"] true;
  check ints ["(= w t)"; "(<= (+ v (* 256 w) (* 256 s)) 255)"; "(>= v 0)"; "(>= (* 256 (+ t s)) 1)"] true;
  (* A fractional two-sided bound on a multiple of a coefficient gcd. *)
  check ints ["(>= (* 256 a) 1)"; "(<= (* 256 a) 255)"] true;
  check ints ["(>= (- (* 6 a) (* 9 b)) 1)"; "(<= (- (* 6 a) (* 9 b)) 2)"] true;
  check ints ["(>= (* 3 a) (- 1))"; "(<= (* 3 a) (- 1))"] true;
  (* The premises may come in any order. *)
  check ints ["(<= z 0)"; "(>= (+ (* 256 t) (* 256 s) z) 1)"; "(>= z 0)"; "(>= v 0)";
              "(<= (+ v (* 256 t) (* 256 s)) 255)"] true;
  check ints ["(>= v 0)"; "(<= z 0)"; "(<= (+ v (* 256 t) (* 256 s)) 255)"; "(>= z 0)";
              "(>= (+ (* 256 t) (* 256 s) z) 1)"] true;
  (* Over the reals the same systems have a model; real-valued refutations are still accepted. *)
  check reals ["(>= (* 256 a) 1)"; "(<= (* 256 a) 255)"] false;
  check reals ring false;
  check reals ["(>= a 1)"; "(<= a 0)"] true;
  check reals ["(< a 0)"; "(> a 0)"] true;
  check reals ["(>= (* 2 a) 1)"; "(<= (+ a b) 0)"; "(>= b 0)"] true;
  (* Satisfiable near misses: a wrong rounding direction or constant would refute them. *)
  check ints ["(>= (* 3 a) (- 3))"; "(<= (* 3 a) (- 3))"] false;
  check ints ["(>= (* 3 a) 1)"; "(<= a 1)"] false;
  check ints ["(>= (* 256 a) 0)"; "(<= (* 256 a) 255)"] false;
  check ints ["(>= (* 256 a) 1)"; "(<= (* 256 a) 256)"] false;
  check ints ["(<= (+ v (* 256 t) (* 256 s)) 256)"; "(>= v 0)"; "(>= (+ (* 256 t) (* 256 s) z) 1)";
              "(<= z 0)"; "(>= z 0)"] false;
  (* Dropped, swapped or weakened premises of the accepted ring refutation. *)
  check ints ["(<= (+ v (* 256 t) (* 256 s)) 255)"; "(>= v 0)"; "(>= (+ (* 256 t) (* 256 s) z) 1)";
              "(>= z 0)"] false;
  check ints ["(<= (+ v (* 256 t) (* 256 s)) 255)"; "(>= v 0)"; "(>= (+ (* 256 t) (* 256 s) z) 1)";
              "(<= w 0)"; "(>= z 0)"] false;
  check ints ["(<= (+ v (* 256 t) (* 256 s)) 255)"; "(>= (+ (* 256 t) (* 256 s) z) 1)"; "(<= z 0)";
              "(>= z 0)"] false;
  check ints ["(<= (+ v (* 255 t) (* 255 s)) 255)"; "(>= v 0)"; "(>= (+ (* 255 t) (* 255 s) z) 1)";
              "(<= z 0)"; "(>= z 0)"] false;
  (* A Real atom in the row: integer rounding is not available. *)
  check mixed ["(>= (+ (* 2 a) (* 2 r)) 1)"; "(<= (+ a r) (/ 3 4))"] false;
  (* Integer-unsatisfiable systems that need more than one rounding step stay pending. The two-variable
     case 5a + 7b = 1 is decided by the existing continued-fraction split of Z3LpGomory; with three
     variables no row has a common factor and no split applies. *)
  check ints ["(= (+ (* 5 a) (* 7 b)) 1)"; "(>= a 0)"; "(>= b 0)"] true;
  check ints ["(= (+ (* 5 a) (* 7 b) (* 11 t)) 1)"; "(>= a 0)"; "(>= b 0)"; "(>= t 0)"] false

(* Bounded exhaustive evaluation of premise-free bit-vector theory lemmas and rewrites over opaque leaves
   (Z3BvExhaustive). The accepted cases are valid for every value of their leaves, with at most 12 leaf bits in
   total; the rejected ones are false for some value of a leaf, or valid but outside the evaluated fragment or
   bounds (and decided by no other kernel rule). The expected value is the kernel's decision on the marshaled
   ASTs. The first cases are the three obligations of SMT-LIB QF_ABV/egt/egt-0160. *)
let bv_bounded_evaluation () =
  let c = context () in
  let declarations =
    "(declare-const packet (Array (_ BitVec 32) (_ BitVec 8)))(declare-const x (_ BitVec 8))\
     (declare-const y (_ BitVec 4))(declare-const y5 (_ BitVec 5))(declare-const z (_ BitVec 12))\
     (declare-const v (_ BitVec 32))(declare-const k (_ BitVec 7))(declare-const p Bool)(declare-const q Bool)\
     (declare-fun f ((_ BitVec 8)) (_ BitVec 8))" in
  let judgment formula =
    let input = List.hd (parse c (declarations ^ "(assert " ^ formula ^ ")")) in
    let st = B.marshal_expressions (B.empty_state ()) [input] in
    Option.get (U.classify_fact (B.cached_expression st input)) in
  let pending kind j premises =
    match U.check_node [] { U.kind = kind; conclusion = j; premises } with
    | Some (_, pending) -> Some pending
    | None -> None in
  (* Keep the premise independent: p already entails the tested disjunction containing p. *)
  let premise = { U.conclusion = judgment "q"; hypotheses = [] } in
  let lemma expected formula =
    let j = judgment formula in
    require (U.checked_theory_lemma (U.Unverified "th-lemma") j [] = expected)
      ("incorrect bounded bit-vector theory lemma: " ^ formula);
    require (pending (U.Unverified "th-lemma") j [] = Some (if expected then Z.zero else Z.one))
      ("bounded bit-vector theory lemma lost its obligation: " ^ formula);
    (* Only premise-free `th-lemma` steps are evaluated. *)
    require (not (U.checked_theory_lemma (U.Unverified "th-lemma") j [premise.U.conclusion]))
      ("bounded evaluation ignored a premise: " ^ formula);
    require (not (U.checked_theory_lemma (U.Unverified "assumed:nlsat") j []))
      ("bounded evaluation accepted an assumed origin: " ^ formula) in
  let rewrite expected left right =
    let name = left ^ " -> " ^ right in
    let j = judgment ("(= " ^ left ^ " " ^ right ^ ")") in
    require (U.check_step U.RewriteRule j [] = expected) ("incorrect bounded bit-vector rewrite: " ^ name);
    require (pending U.RewriteRule j [] = Some (if expected then Z.zero else Z.one))
      ("bounded bit-vector rewrite lost its obligation: " ^ name);
    (match j with
     | U.Equal (a, b) ->
       require (U.check_step U.RewriteRule (U.Observational (a, b)) [] = expected)
         ("incorrect observational bounded bit-vector rewrite: " ^ name);
       require (not (U.check_step U.ApplyDefinition j [])) ("bounded evaluation decided a definition step: " ^ name)
     | _ -> failwith ("expected an equation: " ^ name));
    require (not (U.check_step U.RewriteRule j [premise.U.conclusion]))
      ("bounded rewrite accepted a premise: " ^ name);
    require (pending U.RewriteRule j [premise] = None) ("rewrite with a premise was not rejected: " ^ name);
    require (not (U.check_step U.Commutativity j [])) ("bounded evaluation decided a commutativity step: " ^ name) in
  let sel = "(select packet #x000000f1)" and other = "(select packet #x000000f2)" in
  let t = "(concat #x000000 " ^ sel ^ ")" in
  let s = "(bvadd #x000000f2 " ^ t ^ ")" in
  (* egt-0160: the bound split rewrite and the two range lemmas. *)
  rewrite true ("(bvule " ^ s ^ " #x00000223)")
    ("(and (= ((_ extract 31 10) " ^ s ^ ") (_ bv0 22)) (bvule ((_ extract 9 0) " ^ s ^ ") ((_ extract 9 0) #x00000223)))");
  lemma true ("(= ((_ extract 31 10) " ^ s ^ ") (_ bv0 22))");
  lemma true ("(or (bvule (bvadd (_ bv242 10) (concat #b00 " ^ sel ^ ")) (_ bv547 10)) false)");
  (* egt-7033: constant re-association with a 32-bit zero-extended 8-bit leaf. *)
  rewrite true ("(bvadd (bvadd #x00000002 " ^ t ^ ") #x00000001)") ("(bvadd #x00000003 " ^ t ^ ")");
  (* The bound split holds for every constant below 2^10; mutated numerals and a wrong extract range make the
     claims false for some leaf value. *)
  rewrite true ("(bvule " ^ s ^ " #x000001f0)")
    ("(and (= ((_ extract 31 10) " ^ s ^ ") (_ bv0 22)) (bvule ((_ extract 9 0) " ^ s ^ ") ((_ extract 9 0) #x000001f0)))");
  rewrite false ("(bvule " ^ s ^ " #x00000423)")
    ("(and (= ((_ extract 31 10) " ^ s ^ ") (_ bv0 22)) (bvule ((_ extract 9 0) " ^ s ^ ") ((_ extract 9 0) #x00000423)))");
  rewrite false ("(bvadd (bvadd #x00000002 " ^ t ^ ") #x00000001)") ("(bvadd #x00000004 " ^ t ^ ")");
  lemma false ("(= ((_ extract 31 10) (bvadd #x000003f2 " ^ t ^ ")) (_ bv0 22))");
  lemma false ("(or (bvule (bvadd (_ bv242 10) (concat #b00 " ^ sel ^ ")) (_ bv496 10)) false)");
  lemma false ("(= ((_ extract 31 8) " ^ s ^ ") (_ bv0 24))");
  lemma false "false";
  (* Carry: x + 1 wraps at 255 in 8 bits but not after zero extension to 9 bits. *)
  lemma false "(bvule x (bvadd x #x01))";
  lemma true "(bvule ((_ zero_extend 1) x) (bvadd ((_ zero_extend 1) x) #b000000001))";
  lemma true "(or (not (bvult x #x10)) (bvule x #x0f))";
  lemma false "(or (not (bvult x #x11)) (bvule x #x0f))";
  (* Unsigned comparisons on values with the top bit set. *)
  lemma true "(or (not (bvuge x #x80)) (bvult #x7f x))";
  lemma false "(bvule #x80 x)";
  (* A repeated leaf takes one value; distinct leaves are independent and never alias. *)
  lemma true "(= (bvadd x x) (concat ((_ extract 6 0) x) #b0))";
  lemma true ("(bvule ((_ zero_extend 4) ((_ extract 3 0) " ^ sel ^ ")) " ^ sel ^ ")");
  lemma false ("(= " ^ sel ^ " " ^ other ^ ")");
  lemma false ("(bvule " ^ sel ^ " " ^ other ^ ")");
  lemma false "(= (f x) (f #x00))";
  (* A closed uninterpreted constant is a leaf, never a fixed value. *)
  lemma false "(= x #x05)";
  (* The leaf-width bound: 4 + 8 = 12 bits are enumerated, 5 + 8 = 13 bits are not. *)
  lemma true "(= (concat y x) (bvadd (concat y #x00) (concat #x0 x)))";
  lemma true "(bvule ((_ zero_extend 4) z) #x0fff)";
  lemma false "(= (concat y5 x) (bvadd (concat y5 #x00) (concat #b00000 x)))";
  (* A valid step over a 32-bit leaf is beyond the bound: the bound split holds for every v. (The
     re-association (bvadd (bvadd #x00000002 v) #x00000001) -> (bvadd #x00000003 v) used to be the
     example here; Z3BvAddNormalize now certifies it, see checked-bit-vector-sum-normalization.) *)
  rewrite false "(bvule v #x00000223)"
    "(and (= ((_ extract 31 10) v) (_ bv0 22)) (bvule ((_ extract 9 0) v) ((_ extract 9 0) #x00000223)))";
  (* An extraction step outside the shapes of Z3BvExtract (the numeral is evaluated) over a 7-bit leaf. *)
  rewrite true "((_ extract 4 0) (bvadd (_ bv1 7) k))" "(bvadd #b00001 ((_ extract 4 0) k))";
  (* Operators outside the evaluated fragment: bvmul and bvudiv terms are opaque leaves, and Boolean terms such
     as the signed comparison bvsle (opaque in the native bridge) or a Boolean constant are not evaluated. *)
  lemma false "(= (bvmul #x02 x) (bvadd x x))";
  lemma false "(= (bvudiv x #x02) ((_ zero_extend 1) ((_ extract 7 1) x)))";
  lemma false "(or (bvsle x x) (bvult x #x00))";
  lemma false "(or p (bvult x #x00))"

(* The connectives are dispatched on the typed canonical declarations of Z3CanonicalOps (name, kind tag,
   domain, range, parameters). Z3 lets user datatypes have accessors and constructors named like
   connectives; the bridge marshals them with Z3's name and the datatype kind tags, so they must never
   be evaluated as connectives. The canonical connectives the bridge marshals are evaluated as before. *)
let canonical_dispatch () =
  let c = context () in
  (* A constructor may share a connective's name only with argument sorts the builtin does not take; it is
     declared apart from the accessors of the same names, which Z3 would not disambiguate. *)
  let accessors =
    "(declare-datatypes ((T 0)) (((mk (|and| Bool) (|or| Bool) (|not| Bool) (bits (_ BitVec 2))))))\
     (declare-const t T)(declare-const x (_ BitVec 2))(declare-const p Bool)" in
  let constructors =
    "(declare-datatypes ((S 0)) (((|or| (left Int) (right Int)) (|not| (inner Int)))))(declare-const s S)" in
  let parsed declarations formula =
    let input = List.hd (parse c (declarations ^ "(assert " ^ formula ^ ")")) in
    let st = B.marshal_expressions (B.empty_state ()) [input] in
    B.cached_expression st input in
  let expression = parsed accessors in
  let judgment formula = Option.get (U.classify_fact (expression formula)) in
  (* `checked` is the whole premise-free `th-lemma` check, `bounded` the bounded bit-vector evaluation alone. *)
  let lemma checked bounded formula =
    require (U.checked_theory_lemma (U.Unverified "th-lemma") (judgment formula) [] = checked)
      ("incorrect theory lemma check: " ^ formula);
    require (Z3BvExhaustive.valid (expression formula) = bounded)
      ("incorrect bounded evaluation: " ^ formula) in
  let head formula = match expression formula with
    | A.App (d, _) -> d
    | _ -> failwith ("expected an application: " ^ formula) in
  (* The declaration of the right-hand side of an equation. *)
  let right formula = match parsed constructors formula with
    | A.App (_, [_; A.App (d, _)]) -> d
    | _ -> failwith ("expected an equation with an application: " ^ formula) in
  let datatype name tag formula d =
    require (d.A.decl_name = name &&
             (match d.A.interp with Some k -> Z.equal k (Z.of_int tag) | None -> false))
      ("datatype declaration not marshaled with its name and kind tag: " ^ formula);
    require (not (Z3CanonicalOps.canonical_connective d))
      ("datatype declaration taken as a connective: " ^ formula) in
  List.iter (fun (name, formula) -> datatype name 202 formula (head formula))
    ["and", "(|and| t)"; "or", "(|or| t)"; "not", "(|not| t)"];
  List.iter (fun (name, formula) -> datatype name 200 formula (right formula))
    ["or", "(= s (|or| 1 2))"; "not", "(= s (|not| 3))"];
  require (Z3CanonicalOps.canonical_and (head "(and p (|and| t))"))
    "the native conjunction is not canonical";
  require (Z3CanonicalOps.canonical_or (head "(or p (|or| t))")) "the native disjunction is not canonical";
  require (Z3CanonicalOps.canonical_not (head "(not (|not| t))")) "the native negation is not canonical";
  require (Z3CanonicalOps.canonical_eq (head "(= x #b01)")) "the native equation is not canonical";
  (* The accessors are datatype operations: atoms of the Boolean structure and evaluated by the datatype
     rules, so true claims about them are checked and false ones are not, and the bounded evaluation never
     reads them as connectives. *)
  lemma false false "(|and| t)";
  lemma true false "(or (|and| t) (not (|and| t)))";
  lemma false false "(or (|and| t) (|or| t))";
  lemma false false "(and (|and| t) (not (|and| t)))";
  lemma true false "(|and| (mk true true true #b01))";
  lemma false false "(|and| (mk false true true #b01))";
  lemma true false "(not (|and| (mk false true true #b01)))";
  lemma true false "(not (|not| (mk true true false #b01)))";
  lemma true false "(= (bits (mk true true true #b01)) #b01)";
  lemma false false "(= (bits (mk true true true #b01)) #b10)";
  (* An accessor of bit-vector sort is an opaque leaf of the bounded evaluation; a clause with a Boolean
     disjunct it does not evaluate is not decided by it, even when another disjunct is true. *)
  lemma true true "(= (bvadd (bits t) #b00) (bits t))";
  lemma false false "(= (bits t) #b01)";
  lemma true false "(or (|and| t) (not (bvult (bits t) #b00)))";
  lemma true true "(or (not (bvult (bits t) #b10)) (bvule (bits t) #b01))";
  lemma false false "(or (not (bvult (bits t) #b11)) (bvule (bits t) #b01))";
  (* Accessors named `true`, `false` and `=>`, and constructors with arguments named `true` and `false` (Z3
     rejects nullary constructors with those names, whose argument sorts are the builtin constants'). Each
     datatype is declared alone, because Z3 then reads the bare symbols `true` and `false` as its accessors. *)
  let named_accessors =
    "(declare-datatypes ((U 0)) (((mkU (|true| Bool) (|false| Bool) (|=>| Bool)))))(declare-const v U)" in
  let named_constructors =
    "(declare-datatypes ((R 0)) (((|true| (val Int)) (|false| (other Int)))))(declare-const r R)" in
  let head_in declarations formula = match parsed declarations formula with
    | A.App (d, _) -> d
    | _ -> failwith ("expected an application: " ^ formula) in
  let right_in declarations formula = match parsed declarations formula with
    | A.App (_, [_; A.App (d, _)]) -> d
    | _ -> failwith ("expected an equation with an application: " ^ formula) in
  List.iter (fun (name, formula) -> datatype name 202 formula (head_in named_accessors formula))
    ["true", "(|true| v)"; "false", "(|false| v)"; "=>", "(|=>| v)"];
  List.iter (fun (name, formula) -> datatype name 200 formula (right_in named_constructors formula))
    ["true", "(= r (|true| 1))"; "false", "(= r (|false| 2))"];
  require (Z3CanonicalOps.canonical_true (head "true")) "the native constant true is not canonical";
  require (Z3CanonicalOps.canonical_false (head "false")) "the native constant false is not canonical";
  require (Z3CanonicalOps.canonical_implies (head "(=> p (|and| t))")) "the native implication is not canonical";
  (* Read as the constants, `(not (|false| v))` and `(or (|true| v) (|false| v))` would be tautologies; they
     are datatype accessors whose fields may both be false, so neither is checked. *)
  let lemma_in declarations checked bounded formula =
    let e = parsed declarations formula in
    require (U.checked_theory_lemma (U.Unverified "th-lemma") (Option.get (U.classify_fact e)) [] = checked)
      ("incorrect theory lemma check: " ^ formula);
    require (Z3BvExhaustive.valid e = bounded) ("incorrect bounded evaluation: " ^ formula) in
  lemma_in named_accessors false false "(|true| v)";
  lemma_in named_accessors false false "(not (|false| v))";
  lemma_in named_accessors false false "(or (|true| v) (|false| v))";
  lemma_in named_accessors false false "(|=>| v)";
  lemma_in named_accessors true false "(or (|true| v) (not (|true| v)))"

(* Modular normalization of bit-vector sums over opaque summands (Z3BvAddNormalize): the constant
   re-association rewrites of the QF_ABV pulse reports, bvadd(bvadd(c1, t), c2) = bvadd(c3, t) with
   c3 = c1 + c2 modulo 2^w over any term t, and the n-ary forms of the same flattening. The accepted cases
   have, on both sides, the same sequence of non-numeral summands (any closed term of the sum's sort, taken
   as an opaque atom) and numerals with the same total modulo 2^w. The rejected ones differ in a numeral, an
   atom, the sort or the width, or are valid but outside the normal form (reordered atoms, equal atoms
   merged into a product), or have a malformed declaration of a numeral or a sum; none of them is decided
   by another rule. The expected value is the kernel's decision on the marshaled ASTs. *)
let bv_sum_normalization () =
  let module BN = Z3BvAddNormalize in
  let module BV = Z3BvLemma in
  let c = context () in
  let accepted = ref 0 and invalid = ref 0 and outside = ref 0 and terms_invalid = ref 0 in
  (* Every case is run and all failures are reported together. *)
  let failures = ref [] in
  let guard f = try f () with exn -> failures := Printexc.to_string exn :: !failures in
  let declarations =
    "(declare-const packet (Array (_ BitVec 32) (_ BitVec 8)))(declare-const t (_ BitVec 32))\
     (declare-const u (_ BitVec 32))(declare-const v (_ BitVec 32))(declare-const x (_ BitVec 8))\
     (declare-const y (_ BitVec 8))(declare-const b (_ BitVec 1))(declare-const m (_ BitVec 66))\
     (declare-const big (_ BitVec 4096))(declare-const p Bool)(declare-const k (_ BitVec 7))\
     (declare-fun f ((_ BitVec 32)) (_ BitVec 32))(declare-fun g ((_ BitVec 8)) (_ BitVec 32))\
     (declare-fun g ((_ BitVec 32)) (_ BitVec 32))" in
  let marshal text =
    let inputs = parse c text in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    List.map (B.cached_expression st) inputs in
  let equation ?(binders = "") left right =
    let source =
      if binders = "" then Printf.sprintf "%s(assert (= %s %s))" declarations left right
      else Printf.sprintf "%s(assert (forall (%s) (= %s %s)))" declarations binders left right in
    match marshal source with
    | [A.App (d, [a; b])] when binders = "" -> d, a, b
    | [A.Quantifier (_, _, _, A.App (d, [a; b]))] when binders <> "" -> d, a, b
    | _ -> failwith "expected a bit-vector sum equation" in
  let conclusion_of d a b =
    match U.classify_fact (A.App (d, [a; b])) with
    | Some conclusion -> conclusion
    | None -> failwith "expected a typed bit-vector sum conclusion" in
  let pending ?(premises = []) conclusion =
    match U.check_node [] { U.kind = U.RewriteRule; conclusion = conclusion; premises } with
    | Some (_, obligations) -> Some obligations
    | None -> None in
  let outcome left right =
    match marshal (Printf.sprintf "%s(assert (= %s %s))(assert (not (= %s %s)))"
                     declarations left right left right) with
    | [rewrite; negation] ->
        let entry rule formula premise_ids = { P.rule; formula; premise_ids } in
        Z3NativeMain.result_text (P.check_document {
          P.declarations = []; expressions = []; assertions = [negation];
          entries = [entry U.Asserted negation []; entry U.RewriteRule rewrite [];
                     entry U.UnitResolution Z3ResolutionProofTheory.false_expr [Z.zero; Z.one]];
          root = Z.of_int 2 })
    | _ -> failwith "expected a rewrite and its negation" in
  let premise =
    match marshal (declarations ^ "(assert p)") with
    | [e] -> { U.conclusion = Option.get (U.classify_fact e); hypotheses = [] }
    | _ -> failwith "expected a Boolean premise" in
  (* A step is certified by the rewrite rule only, without premises: not with a premise, under another rule
     label, or as a theory lemma. *)
  let only_as_rewrite ?(narrow = false) name j =
    require (not (U.check_step U.RewriteRule j [premise.U.conclusion]))
      ("sum normalization accepted a premise: " ^ name);
    require (pending ~premises:[premise] j = None) ("a rewrite with a premise was not rejected: " ^ name);
    require (not (U.check_step U.ApplyDefinition j []))
      ("sum normalization decided a definition step: " ^ name);
    require (not (U.check_step U.Commutativity j []))
      ("sum normalization decided a commutativity step: " ^ name);
    (* The bounded evaluation of Z3BvExhaustive decides a theory lemma over at most 12 leaf bits by itself;
       the sum normalization decides none. *)
    if not narrow then
      require (not (U.checked_theory_lemma (U.Unverified "th-lemma") j []))
        ("sum normalization decided a theory lemma: " ^ name) in
  let accept ?(narrow = false) left right = guard @@ fun () ->
    incr accepted;
    let name = left ^ " -> " ^ right in
    let d, a, b = equation left right in
    let j = conclusion_of d a b in
    require (U.check_step U.RewriteRule j []) ("sum normalization did not certify: " ^ name);
    require (pending j = Some Z.zero) ("sum normalization left an obligation: " ^ name);
    require (U.check_step U.RewriteRule (U.Observational (a, b)) [])
      ("sum normalization did not certify the observational rewrite: " ^ name);
    only_as_rewrite ~narrow name j;
    require (outcome left right = "ACCEPT") ("sum normalization refutation was not ACCEPT: " ^ name);
    require (BN.equivalent a b) ("sum normalization rejected: " ^ name) in
  let uncertified what left right = guard @@ fun () ->
    let name = left ^ " -> " ^ right in
    let d, a, b = equation left right in
    let j = conclusion_of d a b in
    require (not (U.check_step U.RewriteRule j [])) (what ^ " certified: " ^ name);
    require (not (U.check_step U.RewriteRule (U.Observational (a, b)) []))
      (what ^ " certified as an observational rewrite: " ^ name);
    require (pending j = Some Z.one) (what ^ " was not left pending: " ^ name);
    only_as_rewrite name j;
    require (outcome left right = "PARTIAL 1") (what ^ " did not give a PARTIAL 1 refutation: " ^ name);
    require (not (BN.equivalent a b)) (what ^ " accepted by sum normalization: " ^ name) in
  let reject left right = incr invalid; uncertified "invalid sum" left right in
  let beyond left right = incr outside; uncertified "sum outside the normal form" left right in
  let reject_terms what d a b = guard @@ fun () ->
    incr terms_invalid;
    (* A conclusion that is not a typed judgment (the sides disagree in sort) is no step at all. *)
    (match U.classify_fact (A.App (d, [a; b])) with
     | Some j ->
         require (not (U.check_step U.RewriteRule j [])) ("malformed sum terms certified: " ^ what);
         require (pending j <> Some Z.zero) ("malformed sum terms left no obligation: " ^ what)
     | None -> ());
    require (not (BN.equivalent a b)) ("malformed sum terms accepted: " ^ what) in
  (* The report family at 32 bits: the numerals fold modulo 2^32 (4294967292 is -4), t is an
     uninterpreted constant. *)
  accept "(bvadd (bvadd #x00000002 t) #x00000001)" "(bvadd #x00000003 t)";
  accept "(bvadd (bvadd #xfffffffc t) #xfffffffc)" "(bvadd #xfffffff8 t)";
  accept "(bvadd (bvadd #xfffffff8 t) #x00000003)" "(bvadd #xfffffffb t)";
  accept "(bvadd (bvadd #xffffffff t) #x00000002)" "(bvadd #x00000001 t)";
  (* The numerals cancel: the other side is the bare atom, either way round, or a zero addend. *)
  accept "(bvadd (bvadd #xfffffffc t) #x00000004)" "t";
  accept "t" "(bvadd (bvadd #x00000004 t) #xfffffffc)";
  (* The n-ary forms of the reports: a ternary inner sum; two inner sums into a ternary sum; a numeral to
     the left of an outer sum with a ternary inner sum; several numerals among the atoms. *)
  accept "(bvadd (bvadd #x00000007 t u) #x00000009)" "(bvadd #x00000010 t u)";
  accept "(bvadd (bvadd #x00000001 t) (bvadd #x00000002 u))" "(bvadd #x00000003 t u)";
  accept "(bvadd #x00000004 (bvadd #x00000005 t u))" "(bvadd #x00000009 t u)";
  accept "(bvadd #x00000001 t #x00000002 u #x00000003)" "(bvadd #x00000006 (bvadd t u))";
  accept "(bvadd (bvadd #xfffffffe t u v) #x00000003)" "(bvadd #x00000001 t u v)";
  (* Other widths, each with an atom of that width. At 8, 1 and 7 bits the atom has at most 12 bits, which the
     bounded evaluation of Z3BvExhaustive decides as well. *)
  accept ~narrow:true "(bvadd (bvadd #x02 x) #x01)" "(bvadd #x03 x)";
  accept ~narrow:true "(bvadd (bvadd #xff x) #x01)" "x";
  accept ~narrow:true "(bvadd (bvadd #b1 b) #b1)" "b";
  accept ~narrow:true "(bvadd (bvadd (_ bv1 7) k) (_ bv1 7))" "(bvadd (_ bv2 7) k)";
  accept "(bvadd (bvadd (_ bv5 66) m) (_ bv7 66))" "(bvadd (_ bv12 66) m)";
  let two_pow n = Z.shift_left Z.one n in
  let numeral width n = Printf.sprintf "(_ bv%s %d)" (Z.to_string n) width in
  let top66 = numeral 66 (Z.pred (two_pow 66)) in
  accept (Printf.sprintf "(bvadd (bvadd %s m) %s)" top66 top66)
    (Printf.sprintf "(bvadd %s m)" (numeral 66 (Z.sub (two_pow 66) (Z.of_int 2))));
  accept (Printf.sprintf "(bvadd (bvadd %s m) (_ bv1 66))" top66) "m";
  accept "(bvadd (bvadd (_ bv5 4096) big) (_ bv7 4096))" "(bvadd (_ bv12 4096) big)";
  let top4096 = numeral 4096 (Z.pred (two_pow 4096)) in
  accept (Printf.sprintf "(bvadd (bvadd %s big) %s)" top4096 top4096)
    (Printf.sprintf "(bvadd %s big)" (numeral 4096 (Z.sub (two_pow 4096) (Z.of_int 2))));
  accept (Printf.sprintf "(bvadd (bvadd %s big) (_ bv1 4096))" top4096) "big";
  (* An atom is any closed term of the sort of the sum: an array read, a product (egt-3244), a
     concatenation of reads (xstrcoll), a difference, an application, a conditional. The same atom
     occurring twice is one atom. *)
  let sel n = Printf.sprintf "(select packet #x%08x)" n in
  let product = Printf.sprintf "(bvmul #x00000002 (concat #x000000 %s))" (sel 241) in
  accept (Printf.sprintf "(bvadd (bvadd #x00000004 %s) #x00000001)" product)
    (Printf.sprintf "(bvadd #x00000005 %s)" product);
  let reads = Printf.sprintf "(concat %s %s %s %s)" (sel 241) (sel 242) (sel 243) (sel 244) in
  accept (Printf.sprintf "(bvadd (bvadd #xfffffffc %s) #xfffffffc)" reads)
    (Printf.sprintf "(bvadd #xfffffff8 %s)" reads);
  accept "(bvadd (bvadd #x00000001 (bvsub t u)) #x00000002)" "(bvadd #x00000003 (bvsub t u))";
  accept "(bvadd (bvadd #x00000001 (f t)) #x00000002)" "(bvadd #x00000003 (f t))";
  accept "(bvadd (bvadd #x00000001 (ite p t u)) #x00000002)" "(bvadd #x00000003 (ite p t u))";
  accept "(bvadd (bvadd #x00000001 (bvadd (bvmul #x00000003 t) u)) #x00000002)"
    "(bvadd #x00000003 (bvmul #x00000003 t) u)";
  accept "(bvadd (bvadd #x00000001 t) t)" "(bvadd #x00000001 t t)";
  (* A wrong numeral total, modulo 2^w and not as integers; a dropped, extra or replaced atom; a numeral
     total on a side without atoms. *)
  reject "(bvadd (bvadd #x00000002 t) #x00000001)" "(bvadd #x00000004 t)";
  reject "(bvadd (bvadd #x00000002 t) #x00000001)" "(bvadd #x00000002 t)";
  reject "(bvadd (bvadd #xfffffffc t) #xfffffffc)" "(bvadd #xfffffff9 t)";
  reject "(bvadd (bvadd #xfffffffc t) #xfffffffc)" "(bvadd #x00000008 t)";
  reject "(bvadd (bvadd #xfffffffc t) #x00000003)" "t";
  reject "(bvadd (bvadd #xff x) #x01)" "(bvadd #x01 x)";
  reject "(bvadd (bvadd #b1 b) #b1)" "(bvadd #b1 b)";
  reject "(bvadd (bvadd (_ bv5 66) m) (_ bv7 66))" "(bvadd (_ bv13 66) m)";
  reject (Printf.sprintf "(bvadd (bvadd %s m) %s)" top66 top66)
    (Printf.sprintf "(bvadd %s m)" (numeral 66 (Z.sub (two_pow 66) (Z.of_int 3))));
  reject "(bvadd (bvadd (_ bv5 4096) big) (_ bv7 4096))" "(bvadd (_ bv13 4096) big)";
  reject (Printf.sprintf "(bvadd (bvadd %s big) %s)" top4096 top4096)
    (Printf.sprintf "(bvadd %s big)" (numeral 4096 (Z.sub (two_pow 4096) (Z.of_int 3))));
  reject (Printf.sprintf "(bvadd (bvadd %s big) (_ bv1 4096))" top4096) "(bvadd (_ bv1 4096) big)";
  reject "(bvadd (bvadd #x00000001 t) #x00000002)" "#x00000003";
  reject "(bvadd #x00000003 #x00000001)" "(bvadd #x00000003 t)";
  reject "(bvadd (bvadd #x00000001 t) u)" "(bvadd #x00000001 t)";
  reject "(bvadd (bvadd #x00000001 t) #x00000002)" "(bvadd #x00000003 t u)";
  reject "(bvadd (bvadd #x00000001 t) #x00000002)" "(bvadd #x00000003 u)";
  reject "(bvadd (bvadd #x00000001 t) u)" "(bvadd #x00000001 t t)";
  reject "(bvadd (bvadd #x00000007 t u) #x00000009)" "(bvadd #x00000011 t u)";
  reject "(bvadd (bvadd #x00000007 t u) #x00000009)" "(bvadd #x00000010 t u v)";
  reject "(bvadd (bvadd #x00000001 t) (bvadd #x00000002 u))" "(bvadd #x00000003 t)";
  reject "(bvadd #x00000004 (bvadd #x00000005 t u))" "(bvadd #x00000009 t t)";
  (* Distinct atoms stay distinct: other reads of one array, other applications, a constant and an
     application, overloaded functions of one name, other operands of a difference or a product. *)
  let read32 n = Printf.sprintf "(concat #x000000 %s)" (sel n) in
  reject (Printf.sprintf "(bvadd (bvadd #x00000002 %s) #x00000001)" (read32 241))
    (Printf.sprintf "(bvadd #x00000003 %s)" (read32 242));
  reject "(bvadd (bvadd #x00000002 (f t)) #x00000001)" "(bvadd #x00000003 (f u))";
  reject "(bvadd (bvadd #x00000002 (f t)) #x00000001)" "(bvadd #x00000003 t)";
  reject "(bvadd (bvadd #x00000002 (g t)) #x00000001)" "(bvadd #x00000003 (g ((_ extract 7 0) t)))";
  reject "(bvadd (bvadd #x00000002 (ite p t u)) #x00000001)" "(bvadd #x00000003 (ite p u t))";
  reject "(bvadd (bvadd #x00000002 (bvsub t u)) #x00000001)" "(bvadd #x00000003 (bvsub u t))";
  reject "(bvadd (bvadd #x00000002 (bvmul #x00000002 t)) #x00000001)"
    "(bvadd #x00000003 (bvmul #x00000003 t))";
  (* Valid steps outside the normal form stay pending: the order of the atoms is kept (the reports never
     reorder them), equal atoms are not merged into a product, a product is not distributed. Invalid:
     a high slice of a sum, whose carries differ from the sum of the slices. *)
  beyond "(bvadd (bvadd #x00000001 t) u)" "(bvadd #x00000001 u t)";
  beyond "(bvadd (bvadd #x00000002 t) t)" "(bvadd #x00000002 (bvmul #x00000002 t))";
  beyond "(bvadd #x00000001 (bvadd t t))" "(bvadd #x00000001 (bvmul #x00000002 t))";
  beyond "(bvadd #x00000001 (bvsub t #x00000001))" "t";
  reject "((_ extract 3 2) (bvadd x y))" "(bvadd ((_ extract 3 2) x) ((_ extract 3 2) y))";
  reject "((_ extract 1 1) (bvadd #b01 #b01))" "(bvadd ((_ extract 1 1) #b01) ((_ extract 1 1) #b01))";
  (* Steps under a binder are not decided (closed terms only). *)
  (let d, a, b = equation ~binders:"(a (_ BitVec 32))" "(bvadd (bvadd #x00000002 a) #x00000001)" "(bvadd #x00000003 a)" in
   incr outside;
   require (not (BN.equivalent a b)) "sum normalization accepted a bound variable";
   require (not (U.check_step U.RewriteRule (conclusion_of d a b) []))
     "sum normalization certified a bound variable");
  (* The size bound is tested first: a chain of 200 sums (401 occurrences) is certified, a chain of 300 (601
     occurrences) stays pending. Shared subterms count on the tree: a let-chain of depth 40 has 2^40
     occurrences and is refused without being traversed. *)
  let chain n = String.concat "" (List.init n (fun _ -> "(bvadd #x00000001 ")) ^ "t" ^ String.make n ')' in
  let count n = Printf.sprintf "#x%08x" n in
  accept (chain 200) (Printf.sprintf "(bvadd %s t)" (count 200));
  beyond (chain 300) (Printf.sprintf "(bvadd %s t)" (count 300));
  (let shared =
     "(let ((s0 (bvadd t u)))" ^
     String.concat "" (List.init 40 (fun i -> Printf.sprintf "(let ((s%d (bvadd s%d s%d)))" (i + 1) i i)) ^
     "s40" ^ String.make 41 ')' in
   let _, a, b = equation shared shared in
   incr outside;
   require (not (BN.equivalent a b)) "sum normalization traversed a shared tree of 2^40 occurrences");
  (* Declarations of an accepted step replaced by malformed or other ones: an out-of-range or negative
     numeral that is correct modulo 2^32 if it were reduced, a numeral of another width or sort, a width
     above 4096 or above 2^32, sums of another width, arity or kind. *)
  let with_decl e g = match e with
    | A.App (decl, args) -> A.App (g decl, args)
    | _ -> failwith "expected an application" in
  let nth_argument e n g = match e with
    | A.App (decl, args) -> A.App (decl, List.mapi (fun i x -> if i = n then with_decl x g else x) args)
    | _ -> failwith "expected an application with arguments" in
  let params ps decl = { decl with A.int_params = ps } in
  let ints ps = params (List.map Z.of_int ps) in
  let interp op decl = { decl with A.interp = op } in
  let range s decl = { decl with A.range = A.BaseSort s } in
  let domain ss decl = { decl with A.domain = List.map (fun s -> A.BaseSort s) ss } in
  let d, a, b = equation "(bvadd (bvadd #x00000002 t) #x00000001)" "(bvadd #x00000003 t)" in
  guard (fun () ->
      require (U.check_step U.RewriteRule (conclusion_of d a b) []) "the unmodified sum step was not certified");
  (* a = (bvadd (bvadd c1 t) c2) and b = (bvadd c3 t); the numerals have the parameters [width; value]. *)
  let in_inner g e = match e with
    | A.App (decl, [i; c2]) -> A.App (decl, [g i; c2])
    | _ -> failwith "expected a sum" in
  let first_numeral g e = in_inner (fun i -> nth_argument i 0 g) e in
  let modulus = two_pow 32 in
  let w32 = Z.of_int 32 in
  List.iter (fun (what, a', b') ->
      require (a' <> a || b' <> b) ("the step was not modified: " ^ what);
      reject_terms what d a' b')
    [ "source numeral 2 + 2^32 (not below 2^32)", first_numeral (params [w32; Z.add (Z.of_int 2) modulus]) a, b;
      "source numeral 2 - 2^32 (negative)", first_numeral (params [w32; Z.sub (Z.of_int 2) modulus]) a, b;
      "source numeral -2 where the step needs 2^32 - 2", first_numeral (params [w32; Z.of_int (-2)]) a, b;
      "source numeral of width 33 in a BV32 sum", first_numeral (ints [33; 2]) a, b;
      "source numeral of width 0", first_numeral (ints [0; 2]) a, b;
      "source numeral of width 2^32", first_numeral (params [two_pow 32; Z.of_int 2]) a, b;
      "source numeral of width 2^40", first_numeral (params [two_pow 40; Z.of_int 2]) a, b;
      "source numeral of width 4097", first_numeral (ints [4097; 2]) a, b;
      "source numeral with one parameter", first_numeral (ints [2]) a, b;
      "source numeral with three parameters", first_numeral (ints [32; 2; 0]) a, b;
      "source numeral with range BV33", first_numeral (range "BV33") a, b;
      "source numeral with a domain", first_numeral (domain ["BV32"]) a, b;
      "uninterpreted source numeral", first_numeral (interp None) a, b;
      "source numeral c2 of 2^32 + 1", (match a with
         | A.App (g, [i; c2]) -> A.App (g, [i; with_decl c2 (params [w32; Z.succ modulus])])
         | _ -> failwith "expected a sum"), b;
      "target numeral 3 + 2^32", a, nth_argument b 0 (params [w32; Z.add (Z.of_int 3) modulus]);
      "target numeral 3 - 2^32", a, nth_argument b 0 (params [w32; Z.sub (Z.of_int 3) modulus]);
      "target numeral of width 2^40", a, nth_argument b 0 (params [two_pow 40; Z.of_int 3]);
      "source outer sum of width 31", with_decl a (ints [31]), b;
      "source outer sum of width 0", with_decl a (ints [0]), b;
      "source outer sum of width 33", with_decl a (ints [33]), b;
      "source outer sum of width 2^32", with_decl a (params [two_pow 32]), b;
      "source outer sum of width 4097", with_decl a (ints [4097]), b;
      "source outer sum without width", with_decl a (ints []), b;
      "source outer sum with two parameters", with_decl a (ints [32; 32]), b;
      "source outer sum with range BV31", with_decl a (range "BV31"), b;
      "source outer sum with domain BV32 and BV31", with_decl a (domain ["BV32"; "BV31"]), b;
      "uninterpreted source outer sum", with_decl a (interp None), b;
      "source outer subtraction named bvadd", with_decl a (interp (Some BV.op_sub)), b;
      "source outer product named bvadd", with_decl a (interp (Some BV.op_mul)), b;
      "source outer sum of one argument", (match a with
         | A.App (g, [i; _]) -> A.App (g, [i])
         | _ -> failwith "expected a sum"), b;
      "source outer sum of no argument", (match a with
         | A.App (g, _) -> A.App (g, [])
         | _ -> failwith "expected a sum"), b;
      "source inner sum of width 31", in_inner (fun i -> with_decl i (ints [31])) a, b;
      "source inner sum of width 2^32", in_inner (fun i -> with_decl i (params [two_pow 32])) a, b;
      "source inner sum of width 4097", in_inner (fun i -> with_decl i (ints [4097])) a, b;
      "uninterpreted source inner sum", in_inner (fun i -> with_decl i (interp None)) a, b;
      "source inner subtraction named bvadd", in_inner (fun i -> with_decl i (interp (Some BV.op_sub))) a, b;
      "source inner sum of one argument", in_inner (fun i -> match i with
         | A.App (g, [c1; _]) -> A.App (g, [c1])
         | _ -> failwith "expected a sum") a, b;
      "target sum of width 31", a, with_decl b (ints [31]);
      "target sum of width 8", a, with_decl b (ints [8]);
      "target sum of width 2^40", a, with_decl b (params [two_pow 40]);
      "target sum of width 4097", a, with_decl b (ints [4097]);
      "target sum without width", a, with_decl b (ints []);
      "uninterpreted target sum", a, with_decl b (interp None);
      "target product named bvadd", a, with_decl b (interp (Some BV.op_mul));
      "target sum of one argument", a, (match b with
         | A.App (g, [_; y]) -> A.App (g, [y])
         | _ -> failwith "expected a sum");
      "target sum with range BV31", a, with_decl b (range "BV31") ];
  (* An atom of another sort in a sum: the Int constant n for t. *)
  let n_decl = { A.decl_name = "n"; domain = []; range = A.BaseSort "Int"; interp = None; int_params = [] } in
  let t_atom = match b with A.App (_, [_; t]) -> t | _ -> failwith "expected a sum" in
  let rec replace e = if e = t_atom then A.App (n_decl, [])
    else match e with
      | A.App (decl, args) -> A.App (decl, List.map replace args)
      | _ -> e in
  require (replace a <> a && replace b <> b) "t was not replaced by an Int constant";
  reject_terms "an Int constant as the atom on both sides" d (replace a) (replace b);
  reject_terms "an Int constant as the atom on the source side" d (replace a) b;
  Printf.printf "  bit-vector sum normalization: %d accepted, %d invalid, %d outside the normal form; \
                 rebuilt terms: %d invalid\n%!" !accepted !invalid !outside !terms_invalid;
  if !failures <> [] then failwith (String.concat "\n  " (List.rev !failures))

(* Custard leaves out the match cases that a refinement rules out, so a call
   outside the domain fails instead of returning a value. *)
let erased_refinement_guards () =
  (match Z3SeqTheory.nth [] Z.zero with
   | _ -> failwith "out-of-range sequence access returned a value"
   | exception Match_failure _ -> ())

let proof_check_callback () =
  let c = context () in
  let retained = ref None in
  let registration = Z3native.set_proof_check_callback c (fun proof assertions ->
    Gc.compact ();
    retained := Some (proof, assertions);
    require (Z3native.ast_vector_size c assertions = 1) "callback lost input assertions";
    let doc = B.marshal [Z3native.ast_vector_get c assertions 0] proof in
    require (P.check_document doc = Some Z.zero) "callback proof did not check";
    "native callback") in
  require (Z3native.eval_smtlib2_string c
    "(set-option :produce-proofs true)(assert false)(check-sat)" =
    "unsat\nnative callback\n") "native callback report was lost";
  Gc.compact ();
  (match !retained with
   | Some (proof, assertions) ->
       require (Z3native.ast_to_string c proof <> "" &&
                Z3native.ast_vector_size c assertions = 1)
         "borrowed callback handles did not retain their owners"
   | None -> failwith "proof callback did not run");
  Z3native.clear_proof_check_callback c;
  require (Z3native.eval_smtlib2_string c "(check-sat)" = "unsat\n")
    "cleared callback was still invoked";
  ignore (Sys.opaque_identity registration);
  let c = context () in
  let registration = Z3native.set_proof_check_callback c (fun proof assertions ->
      let inputs = List.init (Z3native.ast_vector_size c assertions)
          (Z3native.ast_vector_get c assertions) in
      require (P.check_document (B.marshal inputs proof) = Some Z.zero)
        "static tactic proof did not check";
      "checked tactic") in
  require (Z3native.eval_smtlib2_string c
      "(set-option :produce-proofs true)(set-logic QF_NRA)\
       (check-sat-using ctx-solver-simplify)\
       (push)(assert false)(check-sat-using ctx-solver-simplify)\
       (pop)(check-sat-using ctx-solver-simplify)" =
      "sat\nunsat\nchecked tactic\nsat\n")
    "static tactic registration or scoped callback was lost";
  Z3native.clear_proof_check_callback c;
  ignore (Sys.opaque_identity registration)

let proof_callback_exceptions () =
  let c = context () in
  ignore (Z3native.eval_smtlib2_string c "(set-option :produce-proofs true)(assert false)");
  let registration = Z3native.set_proof_check_callback c
      (fun _ _ -> failwith "proof callback exception") in
  (match Z3native.eval_smtlib2_string c "(check-sat)(check-sat)" with
   | _ -> failwith "callback exception was swallowed"
   | exception Failure message ->
       require (message = "proof callback exception") "callback exception was replaced");
  let replacement = Z3native.set_proof_check_callback c (fun _ _ -> "recovered") in
  require (Z3native.eval_smtlib2_string c "(check-sat)" = "unsat\nrecovered\n")
    "callback exception poisoned later evaluations";
  let invalid = Z3native.set_proof_check_callback c (fun _ _ -> "bad\000report") in
  (match Z3native.eval_smtlib2_string c "(check-sat)" with
   | _ -> failwith "embedded null in callback report was truncated"
   | exception Invalid_argument _ -> ());
  let oom = Z3native.set_proof_check_callback c (fun _ _ -> raise Out_of_memory) in
  (match Z3native.eval_smtlib2_string c "(check-sat)" with
   | _ -> failwith "callback out-of-memory exception was swallowed"
   | exception Out_of_memory -> ());
  Z3native.clear_proof_check_callback c;
  List.iter (fun token -> ignore (Sys.opaque_identity token))
    [registration; replacement; invalid; oom]

let proof_callback_ownership () =
  let c = context () in
  ignore (Z3native.eval_smtlib2_string c "(set-option :produce-proofs true)(assert false)");
  let old = ref (Some (Z3native.set_proof_check_callback c (fun _ _ -> "old"))) in
  let replacement = Z3native.set_proof_check_callback c (fun _ _ -> "replacement") in
  old := None;
  Gc.compact ();
  require (Z3native.eval_smtlib2_string c "(check-sat)" = "unsat\nreplacement\n")
    "collecting an old registration removed its replacement";
  Z3native.clear_proof_check_callback c;
  let owner = ref None in
  owner := Some (Z3native.set_proof_check_callback c (fun _ _ ->
    owner := None;
    Gc.compact ();
    "collected during callback"));
  require (Z3native.eval_smtlib2_string c "(check-sat)" =
    "unsat\ncollected during callback\n") "callback report was freed before native copying";
  require (Z3native.eval_smtlib2_string c "(check-sat)" = "unsat\n")
    "collected registration was not removed";
  let weak = Weak.create 1 in
  let register () =
    let captured = ref c in
    Weak.set weak 0 (Some captured);
    Z3native.set_proof_check_callback c (fun _ _ ->
      ignore (Sys.opaque_identity !captured); "captured context")
  in
  let token = register () in
  Gc.full_major ();
  require (Weak.check weak 0) "live registration lost its closure";
  Z3native.clear_proof_check_callback c;
  Gc.full_major ();
  require (not (Weak.check weak 0)) "unregistration leaked a closure capturing its context";
  ignore (Sys.opaque_identity token);
  ignore (Sys.opaque_identity replacement)

(* Finite-field sorts and operators are marshaled as interpreted terms, so rewrite
   steps taken from the QF_FF certificates are decided by polynomial arithmetic. *)
let ff_rewrites () =
  let c = context () in
  let declarations =
    "(set-logic QF_FF)(define-sort F17 () (_ FiniteField 17))\
     (define-sort F5 () (_ FiniteField 5))(define-sort F3 () (_ FiniteField 3))\
     (define-sort F2 () (_ FiniteField 2))(define-sort F7 () (_ FiniteField 7))\
     (declare-const x F17)(declare-const y F17)(declare-const t F3)\
     (declare-const u F5)(declare-const w F2)\
     (declare-const a F3)(declare-const b F3)(declare-const m F7)(declare-const n F7)" in
  let check expected left right =
    let inputs = parse c (declarations ^ "(assert (= " ^ left ^ " " ^ right ^ "))") in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let conclusion = Option.get (U.classify_fact (B.cached_expression st (List.hd inputs))) in
    require (U.check_step U.RewriteRule conclusion [] = expected)
      ("incorrect finite-field rewrite: " ^ left ^ " -> " ^ right)
  in
  (* The sort name and numerals carry the modulus and the canonical residue. *)
  let inputs = parse c (declarations ^ "(assert (= (as ff-1 F17) (ff.neg (as ff1 F17))))") in
  let st = B.marshal_expressions (B.empty_state ()) inputs in
  (match B.cached_expression st (List.hd inputs) with
   | A.App (_, [A.App (numeral, []); A.App (negation, [A.App (one, [])])]) ->
       require (numeral.A.range = A.BaseSort "FF17" &&
                numeral.A.int_params = [Z.of_int 17; Z.of_int 16] &&
                numeral.A.interp = Some Z3FiniteFieldLemma.op_ff_num)
         "a finite-field numeral lost its modulus or canonical residue";
       require (one.A.int_params = [Z.of_int 17; Z.one] &&
                negation.A.int_params = [Z.of_int 17] &&
                negation.A.interp = Some Z3FiniteFieldLemma.op_ff_neg)
         "a finite-field operator lost its modulus"
   | _ -> failwith "expected a native finite-field equality");
  check true "(ff.bitsum (as ff7 F17) (as ff2 F17))" "(as ff11 F17)";
  check true "(= (as ff11 F17) (as ff2 F17))" "false";
  check true "(= (as ff1 F2) (as ff0 F2))" "false";
  check true "(= (as ff3 F2) (as ff1 F2))" "true";
  check true "(ff.neg (as ff1 F17))" "(as ff16 F17)";
  check true "(ff.neg (as ff1 F17))" "(as ff-1 F17)";
  check true "(ff.add (as ff3 F5) (as ff3 F5))" "(as ff1 F5)";
  check true "(ff.mul (as ff3 F5) (as ff4 F5))" "(as ff2 F5)";
  check true "(ff.add x (as ff5 F17))" "(ff.add (as ff5 F17) x)";
  check true "(ff.neg y)" "(ff.mul (as ff16 F17) y)";
  check true "(ff.add x x)" "(ff.mul (as ff2 F17) x)";
  check true "(ff.mul (ff.add x y) (ff.mul x y))" "(ff.mul x y (ff.add x y))";
  check true "(ff.add (ite (= y x) y (as ff0 F17)) (ff.mul (as ff2 F17) x))"
    "(ff.add (ff.mul (as ff2 F17) x) (ite (= y x) y (as ff0 F17)))";
  check true "(ff.mul (ff.mul u u) (ff.mul (as ff4 F5) u))" "(ff.mul (as ff4 F5) u u u)";
  check true "(= (ff.mul (as ff16 F17) (ff.add (as ff5 F17) y)) (ff.mul (as ff16 F17) y))" "false";
  check true "(= (ff.add (as ff8 F17) (ff.bitsum x (as ff2 F17))) (ff.add (ff.mul (as ff6 F17) x) y))"
    "(= y (ff.add (as ff8 F17) (ff.mul (as ff11 F17) x) (ff.bitsum x (as ff2 F17))))";
  check true "(= (ff.mul (as ff12 F17) y (ff.add (as ff12 F17) y)) (as ff8 F17))"
    "(= (ff.mul y (ff.add (as ff12 F17) y)) (as ff12 F17))";
  check true "(= t (ff.mul (as ff2 F3) t))" "(= t (as ff0 F3))";
  check true "(= (as ff3 F5) (ff.mul (as ff4 F5) u u u))" "(= (ff.mul u u u) (as ff2 F5))";
  (* An ite compared with a numeral (QF_FF field-3/case-02 and field-7/case-01): a branch that
     differs from the numeral by a nonzero constant is dropped and the condition selects the
     other branch. *)
  check true "(= (ite (= a b) (as ff2 F3) (ff.bitsum b b)) (as ff1 F3))"
    "(and (= (ff.bitsum b b) (as ff1 F3)) (not (= a b)))";
  check true "(= (ite (= n m) (as ff5 F7) (as ff1 F7)) (as ff3 F7))" "(and false (= n m))";
  check true "(= (ite (= a b) b (as ff2 F3)) (as ff1 F3))" "(and (= b (as ff1 F3)) (= a b))";
  check true "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "(and (= b (as ff1 F3)) (not (= a b)))";
  check true "(= (ite (= a b) (as ff2 F3) (ff.mul (as ff2 F3) b)) (as ff0 F3))"
    "(and (= b (as ff0 F3)) (not (= a b)))";
  (* Steps that are not ring identities modulo the prime stay unmet. *)
  check false "(ff.add x (as ff1 F17))" "(ff.add x (as ff2 F17))";
  check false "(ff.bitsum (as ff7 F17) (as ff2 F17))" "(as ff12 F17)";
  check false "(= (as ff11 F17) (as ff2 F17))" "true";
  check false "(= (as ff3 F2) (as ff1 F2))" "false";
  check false "(ff.mul w w)" "w";
  check false "(= (ff.mul (as ff2 F3) t) (as ff1 F3))" "(= t (as ff1 F3))";
  check false "(= x (as ff0 F17))" "true";
  check false "(= x (as ff0 F17))" "false";
  check false "(ff.add x y)" "(ff.add x x)";
  (* An ite compared with a numeral: the wrong polarity, constant, condition or conclusion is
     unmet, as is a branch that equals the numeral or is not a constant different from it. *)
  check false "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "(and (= b (as ff1 F3)) (= a b))";
  check false "(= (ite (= a b) b (as ff2 F3)) (as ff1 F3))" "(and (= b (as ff1 F3)) (not (= a b)))";
  check false "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "(and (= b (as ff2 F3)) (not (= a b)))";
  check false "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "(and (= b (as ff1 F3)) (not (= b a)))";
  check false "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "(and false (not (= a b)))";
  check false "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "false";
  check false "(= (ite (= a b) (as ff1 F3) b) (as ff1 F3))" "(and (= b (as ff1 F3)) (not (= a b)))";
  check false "(= (ite (= a b) (as ff1 F3) (as ff1 F3)) (as ff1 F3))" "(and false (= a b))";
  check false "(= (ite (= a b) a b) (as ff1 F3))" "(and (= b (as ff1 F3)) (not (= a b)))";
  check false "(= (ite (= n m) (as ff5 F7) (as ff1 F7)) (as ff3 F7))" "(and false (= m n))";
  check false "(= (ite (= n m) (as ff5 F7) (as ff1 F7)) (as ff3 F7))" "(and true (= n m))";
  check false "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "(= b (as ff1 F3))";
  check false "(= (ite (= a b) (as ff2 F3) b) (as ff1 F3))" "(and (= b (as ff1 F3)) true)"

(* Finite-field theory lemmas (the `th-lemma` steps of the QF_FF certificates) are decided by
   evaluating the clause under every assignment of residues to its leaves, at most 4096 of
   them; the producer's certificate parameters are not read. *)
let ff_theory_lemmas () =
  let c = context () in
  let bits = List.init 13 (Printf.sprintf "x%d") in
  let declarations =
    "(set-logic QF_FF)(define-sort F2 () (_ FiniteField 2))(define-sort F3 () (_ FiniteField 3))\
     (define-sort F17 () (_ FiniteField 17))(define-sort F4099 () (_ FiniteField 4099))\
     (declare-const x F17)(declare-const y F17)(declare-const a F3)(declare-const b F3)\
     (declare-const t F4099)(declare-fun g (F3) F3)" ^
    String.concat "" (List.map (Printf.sprintf "(declare-const %s F2)") bits) in
  let check ?(premises = []) expected clause =
    let inputs = parse c (declarations ^
      String.concat "" (List.map (fun e -> "(assert " ^ e ^ ")") (premises @ [clause]))) in
    let st = B.marshal_expressions (B.empty_state ()) inputs in
    let judgments = List.map (fun e ->
        Option.get (U.classify_fact (B.cached_expression st e))) inputs in
    let conclusion = List.hd (List.rev judgments) in
    let facts = List.rev (List.tl (List.rev judgments)) in
    require (U.checked_theory_lemma (U.Unverified "th-lemma") conclusion facts = expected)
      ("incorrect finite-field theory lemma: " ^ clause);
    let premises = List.map (fun conclusion ->
        { U.conclusion = conclusion; hypotheses = [] }) facts in
    require (match U.check_node [] {
        U.kind = U.Unverified "th-lemma"; conclusion = conclusion; premises } with
        | Some (_, pending) -> Z.equal pending (if expected then Z.zero else Z.one)
        | None -> false)
      ("finite-field theory lemma lost its obligation: " ^ clause)
  in
  let ors lits = "(or " ^ String.concat " " lits ^ ")" in
  (* field-3/case-04: a conditional term selected by (= b a). *)
  let sel = "(ite (= b a) (as ff2 F3) (as ff1 F3))" in
  let lit_sel = "(not (= " ^ sel ^ " (as ff1 F3)))" in
  let lit_prod = "(not (= (ff.mul a b " ^ sel ^ ") (ff.add (as ff2 F3) a)))" in
  let lit_bits k =
    Printf.sprintf "(not (= (ff.bitsum (as ff0 F3) a) (ff.add (as ff%d F3) (ff.mul a b))))" k in
  (* field-17/case-03: 17^2 assignments. *)
  let sel17 = "(ite (= x y) y x)" in
  let lits17 =
    ["(not (= y " ^ sel17 ^ "))"; "(not (= x " ^ sel17 ^ "))";
     "(not (= (ff.bitsum (ff.mul (as ff16 F17) y) (ff.mul (as ff2 F17) x)) (as ff11 F17)))";
     "(not (= (ff.bitsum " ^ sel17 ^ " (as ff16 F17)) (ff.mul (ff.add (as ff6 F17) x) (ff.add y x))))"] in
  let quadratic17 k =
    Printf.sprintf "(or (not (= (ff.mul y (ff.add (as ff12 F17) y)) (as ff%d F17))))" k in
  (* In F_2 a product of bits is 1 only if each bit is 1: 2^12 assignments are at the bound. *)
  let product vars =
    "(or (not (= (ff.mul " ^ String.concat " " vars ^ ") (as ff1 F2))) (= x0 (as ff1 F2)))" in
  check true (ors [lit_sel; lit_prod; lit_bits 1]);
  check true (ors lits17);
  check true (quadratic17 12);
  check true (product (List.filteri (fun i _ -> i < 12) bits));
  check true "(or (= (g a) (as ff0 F3)) (= (g a) (as ff1 F3)) (= (g a) (as ff2 F3)))";
  (* A mutated numeral or a dropped literal makes the clause false. *)
  check false (ors [lit_sel; lit_prod; lit_bits 2]);
  check false (ors [lit_sel; lit_bits 1]);
  check false (quadratic17 13);
  check false (ors (List.filteri (fun i _ -> i < 3) lits17));
  (* The then branch is taken when the condition holds. *)
  check false "(or (not (= x y)) (= (ite (= x y) (as ff0 F17) x) y))";
  check true "(or (not (= x y)) (= (ite (= x y) x (as ff0 F17)) y))";
  (* Another field: the field-3 clause is false over F_17, and mixed moduli are not evaluated. *)
  check false (ors [
      "(not (= (ite (= y x) (as ff2 F17) (as ff1 F17)) (as ff1 F17)))";
      "(not (= (ff.mul x y (ite (= y x) (as ff2 F17) (as ff1 F17))) (ff.add (as ff2 F17) x)))";
      "(not (= (ff.bitsum (as ff0 F17) x) (ff.add (as ff1 F17) (ff.mul x y))))"]);
  check false "(or (= x0 (as ff0 F2)) (= x0 (as ff1 F2)) (= a (as ff0 F3)))";
  (* Over the bound: 2^13 assignments, or a single leaf over F_4099. *)
  check false (product bits);
  check false "(or (not (= (ff.mul t t) (as ff1 F4099))) (= t (as ff1 F4099)) (= t (as ff4098 F4099)))";
  (* An unsupported connective is not evaluated. *)
  check false "(=> (= a (as ff0 F3)) (= (ff.mul a b) (as ff0 F3)))";
  (* Premises are not used: a clause that holds only under its premise stays unmet, and the
     rule does not apply to a step with premises. *)
  check ~premises:["(= (ff.mul a a) (as ff1 F3))"] false "(or (= a (as ff1 F3)) (= a (as ff2 F3)))";
  check ~premises:["(= a b)"] false (ors [lit_sel; lit_prod; lit_bits 1])

(* Recorded finite-field ideal certificates (`ff-pac`), replayed by
   Z3FiniteFieldPac for any modulus when only definitions and positive
   premises are used. Every mutation of a real certificate is rejected, the
   inverse witness of a disequality is never used, the replay bounds hold,
   and the native flattening rejects malformed or oversized DAGs. *)
let ff_certificates () =
  let module FP = Z3FiniteFieldPac in
  let finite_field prime assertions =
    Printf.sprintf "(set-logic QF_FF)(define-sort F () (_ FiniteField %s))\
                    (declare-const x F)(declare-const y F)%s" prime assertions in
  let unit_ideal prime = finite_field prime
      "(assert (and (= (ff.mul x y) (as ff1 F)) (= (ff.mul x (ff.add y (as ff1 F))) (ff.add x (as ff2 F)))))" in
  let certificates doc = List.filter_map (fun e ->
      match e.P.rule with
      | U.FiniteFieldPac c -> Some (Option.get (U.classify_fact e.P.formula), c)
      | _ -> None) doc.P.entries in
  let checked (conclusion, c) = U.checked_theory_lemma (U.FiniteFieldPac c) conclusion [] in
  let formula = function U.Holds e -> e | _ -> failwith "expected a proposition" in
  List.iter (fun prime ->
      let doc = document (unit_ideal prime) in
      let found = certificates doc in
      require (found <> [] && List.for_all checked found)
        ("recorded finite-field certificate was not replayed over " ^ prime);
      require (P.check_document doc = Some Z.zero)
        ("finite-field refutation was not fully checked over " ^ prime))
    ["2147483647"; "2305843009213693951"; "170141183460469231731687303715884105727"];
  let conclusion, c = List.hd (certificates (document (unit_ideal "2147483647"))) in
  let rejected why c' conclusion' =
    require (not (U.checked_theory_lemma (U.FiniteFieldPac c') conclusion' []))
      ("mutated finite-field certificate accepted: " ^ why) in
  let map_nodes f = { c with FP.pac_nodes = List.mapi f c.FP.pac_nodes } in
  let coefficient = List.hd (List.filter_map (function
      | FP.PacMul (_, k, _) -> Some k | _ -> None) c.FP.pac_nodes) in
  let first_mul = ref true in
  rejected "coefficient" (map_nodes (fun _ n -> match n with
      | FP.PacMul (s, A.App (d, []), f) when !first_mul ->
          first_mul := false;
          let v = match d.A.int_params with [_; v] -> v | _ -> failwith "numeral" in
          let p = Z.of_string "2147483647" in
          FP.PacMul (s, A.App ({ d with A.int_params = [p; Z.rem (Z.succ v) p] }, []), f)
      | n -> n)) conclusion;
  rejected "input index" (map_nodes (fun _ n -> match n with
      | FP.PacInput i -> FP.PacInput (Z.add i (Z.of_int 1000)) | n -> n)) conclusion;
  rejected "future reference" (map_nodes (fun i n -> match n with
      | FP.PacAdd (_, r) -> FP.PacAdd (Z.of_int i, r) | n -> n)) conclusion;
  rejected "root" { c with FP.pac_root = Z.pred c.FP.pac_root } conclusion;
  rejected "missing support" { c with FP.pac_support = List.tl c.FP.pac_support } conclusion;
  rejected "extra support" { c with FP.pac_support = c.FP.pac_support @ [Z.of_int 2] } conclusion;
  rejected "reordered support" { c with FP.pac_support = List.rev c.FP.pac_support } conclusion;
  rejected "missing premise" { c with FP.pac_premises = List.tl c.FP.pac_premises } conclusion;
  (match formula conclusion with
   | A.App (d, first :: rest) ->
       rejected "dropped literal" c (U.Holds (A.App (d, rest)));
       (match first with
        | A.App (_, [premise]) ->
            rejected "unnegated literal" c (U.Holds (A.App (d, premise :: rest)));
            rejected "negated premise" { c with FP.pac_premises =
                List.map (fun p -> if p = premise then Z3ResolutionProofTheory.mk_not_expr p else p)
                  c.FP.pac_premises } conclusion
        | _ -> failwith "expected a negated premise literal")
   | _ -> failwith "expected a clause");
  (* Bounds: unreferenced padding after a valid certificate is still replayed,
     so the certificate is accepted up to each bound and rejected beyond it. *)
  let base = List.length c.FP.pac_nodes in
  let padded extra = { c with FP.pac_nodes = c.FP.pac_nodes @ extra } in
  let accepted why c' =
    require (U.checked_theory_lemma (U.FiniteFieldPac c') conclusion [])
      ("padded finite-field certificate rejected: " ^ why) in
  let inputs n = List.init n (fun _ -> FP.PacInput Z.zero) in
  accepted "node bound" (padded (inputs (100000 - base)));
  rejected "node bound" (padded (inputs (100001 - base))) conclusion;
  (* Each step multiplies by (1 + k*v) for a cycling variable v. *)
  let growth steps = FP.PacInput Z.zero :: List.concat (List.init steps (fun k ->
      let previous = Z.of_int (base + 2 * k) in
      [FP.PacMul (previous, coefficient, [Z.of_int (k mod 6)]);
       FP.PacAdd (previous, Z.of_int (base + 2 * k + 1))])) in
  accepted "polynomial bound" (padded (growth 6));
  rejected "polynomial bound" (padded (growth 24)) conclusion;
  let last = base + 2 * 6 in
  let repeated n = List.init n (fun k -> FP.PacAdd (Z.of_int (last + k), Z.of_int last)) in
  accepted "work bound" (padded (growth 6 @ repeated 20));
  rejected "work bound" (padded (growth 6 @ repeated 20000)) conclusion;
  (* Theory-lemma steps with premises keep their obligation. *)
  require (not (U.checked_theory_lemma (U.FiniteFieldPac c) conclusion
                 [U.Holds (List.hd c.FP.pac_premises)]))
    "finite-field certificate replayed for a step with premises";
  (* The inverse witness of a disequality needs a field: residual obligations. *)
  let residual = document (finite_field "2147483647"
      "(assert (= (ff.mul x x) (as ff0 F)))(assert (not (= x (as ff0 F))))") in
  require (List.exists (fun cert -> not (checked cert)) (certificates residual) &&
           P.check_document residual = Some Z.one) "inverse-witness certificate was replayed";
  let mixed = document (finite_field "2147483647"
      "(assert (= (ff.mul x y) (as ff1 F)))(assert (= (ff.mul x x) (as ff0 F)))") in
  require (List.length (List.filter checked (certificates mixed)) = 1 &&
           P.check_document mixed = Some Z.one) "mixed finite-field refutation changed";
  (* Native flattening of hand-built DAGs. *)
  let cx = context () in
  let symbol = Z3native.mk_string_symbol cx in
  let proof = Z3native.mk_uninterpreted_sort cx (symbol "P") in
  let integer = Z3native.mk_int_sort cx in
  let numeral, premise = match parse cx "(define-sort F () (_ FiniteField 7))(declare-const z F)\
                                         (assert (= z (as ff3 F)))" with
    | [e] -> List.nth (N.app_args cx (Z3native.to_app cx e)) 1, e
    | _ -> failwith "parse" in
  let decl name domain = Z3native.mk_func_decl cx (symbol name) (List.length domain) domain proof in
  let app d args = Z3native.mk_app cx d (List.length args) args in
  let index n = Z3native.mk_numeral cx n integer in
  let input i = app (decl "ff-input" [integer]) [index i] in
  let add l r = app (decl "ff-add" [proof; proof]) [l; r] in
  let mul s k f = app (decl "ff-mul" [proof; Z3native.get_sort cx k; integer]) [s; k; index f] in
  let pac ?(premises = [premise]) root =
    app (decl "ff-pac" [proof; proof; proof])
      [app (decl "ff-premises" (List.map (Z3native.get_sort cx) premises)) premises; root;
       app (decl "ff-support" [integer]) [index "0"]] in
  let view root = N.view_ff_pac cx (pac root) in
  (match view (mul (add (input "0") (input "1")) numeral "2") with
   | Some v ->
       require (match v.N.pac_nodes with
                | [N.PacInput i; N.PacInput j; N.PacAdd (l, r); N.PacMul (s, k, f)] ->
                    Z.equal i Z.zero && Z.equal j Z.one && Z.equal l Z.zero && Z.equal r Z.one &&
                    Z.equal s (Z.of_int 2) && Z3native.is_eq_ast cx k numeral &&
                    List.equal Z.equal f [Z.of_int 2]
                | _ -> false) "native finite-field certificate flattening";
       require (Z.equal v.N.pac_root (Z.of_int 3) && List.equal Z.equal v.N.pac_support [Z.zero] &&
                List.length v.N.pac_premises = 1)
         "native finite-field certificate root and support"
   | None -> failwith "well-formed native finite-field certificate rejected");
  let rec shared k node = if k = 0 then node else shared (k - 1) (add node node) in
  (match view (shared 60 (input "0")) with
   | Some v -> require (List.length v.N.pac_nodes = 61) "shared certificate nodes were duplicated"
   | None -> failwith "shared native certificate rejected");
  let rec chain k node = if k = 0 then node else chain (k - 1) (add node (input "0")) in
  require (Option.is_none (view (chain 200000 (input "1")))) "oversized native certificate accepted";
  List.iter (fun (why, root) -> require (Option.is_none (view root)) ("malformed native certificate: " ^ why))
    ["negative index", input "-1"; "huge index", input "4294967296";
     "non-field coefficient", mul (input "0") (index "3") "0";
     "unknown node", app (decl "ff-sub" [proof; proof]) [input "0"; input "1"]];
  require (Option.is_none (N.view_ff_pac cx (pac ~premises:[numeral] (input "0"))))
    "non-Boolean native certificate premise accepted"

let () =
  ignore (N.version ());
  List.iter (fun (name, test) ->
      test (); Printf.printf "PASS %s\n%!" name)
    ["shared-expression-identity", shared_expressions;
     "checked-clausal-refutations", clausal_proofs;
     "deep-expression-worklist", deep_expression;
     "proof-DAG-cache", proof_cache;
     "exact-native-numerals", exact_numerals;
     "authentic-Farkas-parameters", native_farkas;
     "certified-assign-bounds-parameters", native_assign_bounds;
     "checked-native-integer-LP-tightening", native_integer_tightening;
     "certified-native-Gomory-split-cuts", checked_gomory_cuts;
     "certified-duplicate-distinct-rewrites", distinct_reflexivity;
     "integer-tightening-candidate-mutations", integer_tightening_candidates;
     "typed-native-LP-certificate-decoding", native_lp_certificates;
     "authentic-bound-parameters", native_bound;
     "strict-inputs-and-scopes", strict_inputs_and_scopes;
     "indexed-assertion-membership", indexed_assertion_membership;
     "cached-definition-expansion", cached_definition_expansion;
     "ordered-congruence-matching", ordered_congruence_matching;
     "typed-obligation-diagnostics", typed_diagnostics;
     "precedence-aware-expression-printer", pretty_expressions;
     "readable-obligation-diagnostics", readable_conditions;
     "readable-same-proof-document", readable_same_proof;
     "readable-edge-conditions", readable_edge_cases;
     "identity-and-binders", identity_and_binders;
     "certified-hidden-binder-proof-DAGs", checked_binder_proofs;
     "definition-expanded-binder-certificates", checked_binder_definitions;
     "certified-native-quantifier-instances", checked_quantifier_instances;
     "certified-negative-NNF", checked_negative_nnf;
     "certified-quantifier-pulling", checked_quantifier_pulling;
     "certified-destructive-equality-resolution", checked_der_rules;
     "certified-Hilbert-choice-Skolemization", checked_skolemization;
     "certified-unused-block-Skolemization", checked_vacuous_skolemization;
     "certified-quantifier-reductions-and-lambdas", checked_quantifier_reductions;
     "certified-nested-NNF-replacement", checked_nested_nnf_replacement;
     "certified-theory-lemmas-and-definition-axioms", checked_theory_extensions;
     "concrete-sort-indexed-datatype-model", concrete_datatype_model;
     "contextual-sorted-datatype-proof-kernel", sorted_datatype_checker;
     "sorted-integer-Farkas", sorted_integer_farkas;
     "sorted-typed-epsilon-Skolemization", sorted_epsilon_skolemization;
     "readable-epsilon-provenance", readable_epsilon_provenance;
     "sorted-quantifier-Boolean-rewrites", sorted_quantifier_rewrites;
     "sorted-constant-folding-rewrites", sorted_constant_folding;
     "sorted-native-universal-flattening", sorted_quantifier_flattening;
     "sorted-native-quantifier-instances", sorted_quantifier_instances;
     "malformed-foreign-certificate", malformed_foreign_certificate;
     "assumed-NLSAT-obligation", assumed_nlsat;
     "checked-Boolean-constant-resolution", boolean_constant_resolution;
     "checked-integer-division-axioms", integer_division_axioms;
     "typed-observations-and-root-guard", typed_observations;
     "checked-arithmetic-rewrites", arithmetic_rewrites;
     "checked-arithmetic-factor-rewrites", arithmetic_factor_rewrites;
     "checked-conditional-comparison-rewrites", conditional_comparison_rewrites;
     "checked-array-unequal-defaults", array_unequal_defaults;
     "checked-bit-vector-rewrites", bv_rewrites;
     "checked-bit-vector-extraction-rewrites", bv_extract_rewrites;
     "checked-fresh-bit-model-extension", fresh_bit_model_extension;
     "checked-fresh-bit-context-extension", fresh_bit_context_extension;
     "fresh-bit-document-projections", fresh_bit_document_projections;
     "scoped-model-extension", scoped_model_extension;
     "contextual-boolean-rewrites", contextual_boolean_rewrites;
     "unused-quantifier-rewrites", unused_quantifier_rewrites;
     "checked-triangle-equality-clauses", arithmetic_triangle_clauses;
     "checked-implied-arithmetic-equalities", arithmetic_implied_equalities;
     "checked-implied-arithmetic-bounds", arithmetic_implied_bounds;
     "checked-inferred-integer-splits", arithmetic_inferred_splits;
     "checked-integer-rounding-cuts", arithmetic_integer_rounding;
     "checked-bounded-bit-vector-evaluation", bv_bounded_evaluation;
     "canonical-connective-dispatch", canonical_dispatch;
     "checked-bit-vector-sum-normalization", bv_sum_normalization;
     "erased-refinement-runtime-guards", erased_refinement_guards;
     "native-proof-check-callback", proof_check_callback;
     "proof-callback-exceptions", proof_callback_exceptions;
     "proof-callback-ownership", proof_callback_ownership;
     "checked-finite-field-rewrites", ff_rewrites;
     "checked-finite-field-theory-lemmas", ff_theory_lemmas;
     "checked-finite-field-certificates", ff_certificates]
