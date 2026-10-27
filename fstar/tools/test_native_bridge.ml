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
    equation = fact C.Eq [] (Z.zero, Z.one); pivot = None; definition1 = None;
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
               conclusion1 = conclusion; premises = [] } in
  require (match U.check_node_with_inputs true [input] node with
      | Some (_, pending) -> Z.equal pending Z.zero | None -> false)
    "input-aware binder certificate was not integrated in the node checker"

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
          "(assert (forall ((z Int)) (= " ^ left ^ " " ^ right ^ ")))") in
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
      require (U.check_binder certificate conclusion = expected)
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
          "(assert (forall ((z Int)) (= " ^ left ^ " " ^ right ^ ")))") in
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
      require (U.check_binder certificate conclusion = expected)
        ("incorrect open binder pull-quant decision: " ^ name);
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
                conclusion1 = bad; premises = [] } with
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
      require (match U.check_node [] { U.kind = rule; conclusion1 = conclusion; premises = [] } with
          | Some (_, n) -> Z.equal n (if expected then Z.zero else Z.one)
          | None -> false)
        ("quantified rewrite lost its obligation: " ^ name)) cases

let checked_nested_nnf_replacement () =
  List.iter (fun (name, left, right) ->
      let c = context () in
      let inputs = parse c
          ("(declare-fun p (Int) Bool)(declare-const c Bool)\
            (assert (forall ((x Int)) (= (+ x 0) x)))\
            (assert (= " ^ left ^ " " ^ right ^ "))") in
      let st = B.marshal_expressions (B.empty_state ()) inputs in
      let leaf_formula = match B.cached_expression st (List.hd inputs) with
        | A.Quantifier (_, _, _, body) -> body
        | _ -> failwith "missing arithmetic body" in
      let formula = B.cached_expression st (List.nth inputs 1) in
      let leaf = { U.binder_name = "rewrite"; binder_formula = leaf_formula;
                   binder_premises = []; binder_sorts = None } in
      let root = { U.binder_name = name; binder_formula = formula;
                   binder_premises = [Z.zero]; binder_sorts = None } in
      let certificate = { U.binder_entries = [leaf; root]; binder_root = Z.one } in
      let conclusion = Option.get (U.classify_fact formula) in
      require (U.check_binder certificate conclusion)
        ("NNF did not substitute a universally valid fact under a binder: " ^ name);
      require (not (U.check_binder { certificate with U.binder_entries =
          [{ leaf with U.binder_name = "hypothesis" }; root] } conclusion))
        "NNF generalized a hypothesis while rewriting a nested binder")
    ["nnf-pos", "(and (forall ((x Int)) (p (+ x 0))) c)",
       "(and (forall ((x Int)) (p x)) c)";
     "nnf-neg", "(not (and (forall ((x Int)) (p (+ x 0))) c))",
       "(or (exists ((x Int)) (not (p x))) (not c))"]

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
          U.kind = U.Unverified "th-lemma"; conclusion1 = conclusion; premises = [] } with
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
  let formula = match B.cached_expression st (List.hd inputs) with
    | A.Quantifier (_, _, _, body) -> body
    | _ -> failwith "missing quantified arithmetic clause" in
  let conclusion = Option.get (U.classify_fact formula) in
  let leaf = { U.binder_name = "th-lemma"; binder_formula = formula;
               binder_premises = []; binder_sorts = None } in
  let certificate = { U.binder_entries = [leaf]; binder_root = Z.zero } in
  require (U.check_binder certificate conclusion)
    "an independently checked theory lemma was rejected inside a binder";
  require (not (U.check_binder { certificate with U.binder_entries =
      [{ leaf with U.binder_name = "assumed:nlsat" }] } conclusion))
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
  let fallback value =
    if S.recognizer_value schema leaf value then nil_value else cons_value in
  require (S.accessor_value schema branch Z.zero fallback leaf_value = nil_value &&
           S.accessor_value schema branch Z.zero fallback fork_value = cons_value &&
           S.accessor_value schema branch Z.zero fallback branch_value = cons_value)
    "selectors did not preserve matching fields and argument-dependent wrong-constructor values";
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
  let convert _ _ = false in
  let leaf_bool, fork_bool, branch_bool, nil_bool, cons_bool =
    V.map_base convert leaf_value, V.map_base convert fork_value,
    V.map_base convert branch_value, V.map_base convert nil_value,
    V.map_base convert cons_value in
  let children = List.hd branch.S.accessors in
  let opaque = { children with A.decl_name = "opaque"; interp = None; int_params = [] } in
  let other = {
    V.application = (fun f args ->
      match args with
      | [value] when f = children ->
          if V.recognize leaf.S.constructor value then nil_bool else cons_bool
      | [_] when f = opaque -> nil_bool
      | _ -> failwith "canonical datatype operation escaped to the supplied interpretation");
    quantification = (fun kind bound body_sort body ->
      require (kind = A.Forall_k &&
               bound = [A.BaseSort "Int"; A.BaseSort "Bool"] &&
               body_sort = A.BaseSort "Bool")
        "typed evaluator changed a quantifier signature";
      let result = body [V.Scalar (A.BaseSort "Bool", true);
                         V.Scalar (A.BaseSort "Int", false)] in
      require (result = V.Scalar (A.BaseSort "Bool", true))
        "typed quantifier evaluation reversed de Bruijn bindings incorrectly";
      result);
  } in
  let booleans = { S.encode_bool = (fun b -> b); decode_bool = (fun b -> b);
                   boolean_isomorphism = () } in
  let interpreted = S.interpretation schema booleans other in
  let apply = interpreted.V.application in
  require (apply fork.S.constructor [leaf_bool; leaf_bool] = fork_bool &&
           apply fork.S.recognizer [fork_bool] = V.Scalar (A.BaseSort "Bool", true) &&
           apply branch.S.recognizer [fork_bool] = V.Scalar (A.BaseSort "Bool", false))
    "native constructor or recognizer dispatch was not canonical";
  require (apply children [branch_bool] = cons_bool &&
           apply children [leaf_bool] = nil_bool &&
           apply children [fork_bool] = cons_bool &&
           apply opaque [fork_bool] = nil_bool)
    "native selector dispatch lost matching fields or argument-dependent fallbacks";
  let scope = [leaf.S.constructor.A.range] in
  let rho _ = fork_bool in
  let expression = A.App (children, [A.Var (Z.zero, leaf.S.constructor.A.range)]) in
  require (Z3Definitions.scoped scope expression) "native evaluator fixture is not well sorted";
  require (V.evaluate sigma interpreted scope rho expression = cons_bool)
    "typed AST evaluator bypassed native selector dispatch";
  let quantified = A.Quantifier (A.Forall_k, [A.BaseSort "Int"; A.BaseSort "Bool"],
      A.BaseSort "Bool", A.Var (Z.zero, A.BaseSort "Bool")) in
  require (Z3Definitions.scoped [] quantified) "native quantifier fixture is not well sorted";
  require (V.evaluate sigma interpreted [] (fun _ -> failwith "empty environment") quantified =
           V.Scalar (A.BaseSort "Bool", true))
    "typed AST evaluator did not preserve the supplied quantifier interpretation";
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

let sorted_quantifier_rewrites () =
  let module K = Z3SortedProof in
  let module S = Z3DatatypeSignature in
  let c = context () in
  let declarations =
    "(declare-datatype T ((C (field Int)) (D)))\
     (declare-fun P (T) Bool)(declare-fun Q (T Int) Bool)\
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
    let result = K.check_node schema []
      { U.kind = U.RewriteRule; conclusion1 = conclusion; premises = [] } in
    let checked = match result with
      | Some (_, pending) -> Z.equal pending Z.zero
      | None -> failwith "sorted quantifier checker rejected a well-sorted equality" in
    require (checked = expected)
      ("unexpected sorted quantifier rewrite: " ^ left ^ " -> " ^ right);
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
  check false "(forall ((x T)) (P x))" "(forall ((x T)) (not (P x)))";
  check false "(forall ((x T)) (P x))" "(exists ((x T)) (P x))";
  check false "(forall ((x T) (y T)) (P x))" "(forall ((x T) (y T)) (P y))";
  check false
    "(forall ((x T)) (fake (P x) (Q x 0)))"
    "(forall ((x T)) (or (not (P x)) (Q x 0)))"

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
      conclusion1 = Option.get (U.classify_fact formula); premises = [] } in
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
          ("unexpected sorted quantifier instance: " ^ clause)
    | [] -> failwith "missing sorted instantiation fixture"
  in
  check_clause
    "(or (not (forall ((x T) (b Bool)) (or (P x) b)))\
         (or (P D) (forall ((y T)) (P y))))"
    ["D"; "(forall ((y T)) (P y))"] true;
  check_clause
    "(or (not (forall ((x T)) (exists ((y T)) (R x y))))\
         (exists ((y T)) (R D y)))"
    ["D"] false

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
  let project _ = function
    | Z3ValueTheory.VInt n -> n
    | _ -> failwith "expected a numeric test-model value" in
  List.iter (fun (width, values) ->
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
        "fresh-bit reconstruction became an unconditional rewrite";
      List.iter (fun n ->
          let base : Z3ValueTheory.value A.interpretation = {
            A.interp_app = (fun f vs ->
              match f.A.interp, vs with
              | Some op, _ when Z.equal op Z3BvLemma.op_mkbv ->
                  let rec number = function
                    | [] -> Z.zero
                    | Z3ValueTheory.VBool b :: rest ->
                        Z.add (if b then Z.one else Z.zero) (Z.mul (Z.of_int 2) (number rest))
                    | _ -> failwith "expected Boolean test-model bits" in
                  Z3ValueTheory.VInt (number vs)
              | Some op, [Z3ValueTheory.VInt a; Z3ValueTheory.VInt b]
                  when Z.equal op Z3ValueTheory.op_eq ->
                  Z3ValueTheory.VBool (Z.equal a b)
              | _ -> failwith "unexpected interpreted test-model application");
            A.uninterp_app = (fun f vs ->
              if f = r.F.original then Z3ValueTheory.VInt (Z.of_int n)
              else match vs with
                | [] -> Z3ValueTheory.VBool false
                | _ -> Z3ValueTheory.VInt (Z.of_int 37));
            A.interp_quant = (fun _ _ _ -> failwith "unexpected test-model quantifier");
          } in
          let extended = F.extend r base project in
          let rho _ = Z3ValueTheory.VInt Z.zero in
          (match A.eval extended (F.source r) rho, A.eval extended (F.word r) rho with
           | Z3ValueTheory.VInt a, Z3ValueTheory.VInt b ->
               require (Z.equal a (Z.of_int n) && Z.equal a b)
                 "fresh-bit extension did not reconstruct the original value"
           | _ -> failwith "expected numeric reconstructed values");
          (match A.eval extended (equation r) rho with
           | Z3ValueTheory.VBool true -> ()
           | _ -> failwith "reconstruction equality is false in the extension");
          (match A.eval extended (A.App (unrelated, [])) rho with
           | Z3ValueTheory.VBool false -> ()
           | _ -> failwith "extension changed an unrelated symbol");
          (match extended.A.uninterp_app (List.hd symbols) [Z3ValueTheory.VBool true] with
           | Z3ValueTheory.VInt v ->
               require (Z.equal v (Z.of_int 37)) "extension changed a non-nullary application"
           | _ -> failwith "expected unchanged non-nullary interpretation"))
        values)
    [1, [0; 1]; 3, [0; 1; 5; 7]; 8, [0; 128; 165; 255]]

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
  let base : Z3ValueTheory.value A.interpretation = {
    A.interp_app = (fun f vs ->
      match f.A.interp, vs with
      | Some op, [] when Z.equal op Z3ValueTheory.op_true -> Z3ValueTheory.VBool true
      | Some op, [] when Z.equal op Z3ValueTheory.op_false -> Z3ValueTheory.VBool false
      | Some op, [a; b] when Z.equal op Z3ValueTheory.op_eq -> Z3ValueTheory.VBool (a = b)
      | Some op, _ when Z.equal op Z3BvLemma.op_mkbv ->
          let rec number = function
            | [] -> Z.zero
            | Z3ValueTheory.VBool b :: rest ->
                Z.add (if b then Z.one else Z.zero) (Z.mul (Z.of_int 2) (number rest))
            | _ -> failwith "expected Boolean context-model bits" in
          Z3ValueTheory.VInt (number vs)
      | _ -> failwith "unexpected context-model interpreted application");
    A.uninterp_app = (fun f vs ->
      if f = r.F.original then Z3ValueTheory.VInt (Z.of_int 5)
      else if f = s.F.original then Z3ValueTheory.VInt (Z.of_int 2)
      else match vs with [] -> Z3ValueTheory.VBool false | _ -> Z3ValueTheory.VInt (Z.of_int 37));
    A.interp_quant = (fun _ bs body -> body (List.map (fun _ -> Z3ValueTheory.VBool true) bs));
  } in
  let project _ = function
    | Z3ValueTheory.VInt n -> n | _ -> failwith "expected numeric context-model value" in
  let rho _ = Z3ValueTheory.VInt Z.zero in
  let extended = F.extend_context rs base project in
  require (A.eval_args extended inputs rho = A.eval_args base inputs rho)
    "batch extension changed original inputs";
  List.iter (fun e ->
      require (A.eval extended e rho = Z3ValueTheory.VBool true)
        "batch extension did not satisfy all reconstruction orientations")
    formulas;
  let n = F.number r base project in
  let one = F.extend r base project in
  require (M.retract r.F.symbols n first = R.true_expr)
    "fresh bit did not retract to its Boolean literal";
  let applied = A.App (List.hd r.F.symbols, [A.Var (Z.zero, A.bool_sort)]) in
  require (M.retract r.F.symbols n applied = applied)
    "retraction changed a non-nullary application or bound variable";
  require (M.retract r.F.symbols n (F.source r) = F.source r)
    "retraction changed an original BV constant";
  List.iter (fun e ->
      require (A.eval one e rho = A.eval base (M.retract r.F.symbols n e) rho)
        "literal retraction did not preserve extended evaluation")
    [first; F.word r; applied; quantified]

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
  let rho = SM.default_environment scope in
  let bvar = A.Var (Z.zero, A.bool_sort) in
  let ivar = A.Var (Z.one, SM.int_sort) in
  require (not (Z3Definitions.scoped [] bvar) && Z3Definitions.scoped scope bvar)
    "scope checking accepted an unbound variable or rejected a typed one";
  require (A.eval SM.witness bvar rho = Z3ValueTheory.VBool false &&
           A.eval SM.witness ivar rho = Z3ValueTheory.VInt Z.zero)
    "typed scalar environment did not preserve variable values";
  require (not (SM.scalar_typed A.bool_sort (Z3ValueTheory.VInt Z.zero)) &&
           not (SM.scalar_typed SM.int_sort (Z3ValueTheory.VBool false)))
    "scalar typing accepted a mismatched environment value";
  require (A.eval SM.witness bvar (fun _ -> Z3ValueTheory.VInt Z.zero) =
             Z3ValueTheory.VInt Z.zero)
    "scoped contracts unexpectedly changed generic variable evaluation";
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
  let rs = match F.check_context [] equations with
    | Some rs -> rs | None -> failwith "scoped structural context was rejected" in
  require (M.check_context [] equations = None)
    "legacy model-safety guard unexpectedly accepted reserved fresh names";
  let base : Z3ValueTheory.value A.interpretation = {
    SM.witness with
    A.interp_app = (fun f vs ->
      if f.A.interp = Some Z3BvLemma.op_mkbv then (
        let rec number = function
          | [] -> Z.zero
          | Z3ValueTheory.VBool b :: rest ->
              Z.add (if b then Z.one else Z.zero) (Z.mul (Z.of_int 2) (number rest))
          | _ -> failwith "expected scoped-model word bits" in
        Z3ValueTheory.VInt (number vs))
      else SM.witness.A.interp_app f vs);
    A.uninterp_app = (fun f vs ->
      if f = r.F.original then Z3ValueTheory.VInt (Z.of_int 6)
      else SM.witness.A.uninterp_app f vs);
  } in
  let project _ = function
    | Z3ValueTheory.VInt n -> n | _ -> failwith "expected a numeric scoped-model value" in
  let extended = F.extend_context rs base project in
  let v = Z3ValueTheory.VInt (Z.of_int 6) in
  require (A.eval extended (F.source r) rho = v && A.eval extended (F.word r) rho = v)
    "scoped extension did not reconstruct the source value";
  require (A.eval extended (List.hd equations) rho = Z3ValueTheory.VBool true)
    "scoped extension did not satisfy reversed reconstruction";
  require (A.eval extended (A.App (List.nth symbols 0, [])) rho = Z3ValueTheory.VBool false &&
           A.eval extended (A.App (List.nth symbols 1, [])) rho = Z3ValueTheory.VBool true)
    "fresh uninterpreted atoms were confused with official literals";
  require (A.eval extended R.true_expr rho = Z3ValueTheory.VBool true &&
           A.eval extended R.false_expr rho = Z3ValueTheory.VBool false)
    "scoped extension changed official Boolean literals";
  let quantified = A.Quantifier (A.Forall_k, scope, A.bool_sort,
    R.mk_eq_expr (A.Var (Z.zero, SM.int_sort)) (A.Var (Z.zero, SM.int_sort))) in
  require (Z3Definitions.scoped [] quantified)
    "mixed-sort quantified test was not well-scoped";
  List.iter (fun e ->
      require (SM.scalar_typed (A.get_sort e) (A.eval extended e rho))
        "extension broke scoped scalar typing")
    [bvar; ivar; R.true_expr; R.false_expr; quantified; F.word r];
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
    let premises = List.map (fun conclusion1 ->
        { U.conclusion = conclusion1; hypotheses = [] }) facts in
    require (match U.check_node [] {
        U.kind = U.Unverified "th-lemma"; conclusion1 = conclusion; premises } with
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

let erased_refinement_guards () =
  require (A.__proj__BaseSort__item__name (A.BaseSort "Real") = "Real")
    "constructor projector changed on its valid domain";
  (match A.__proj__BaseSort__item__name (A.ArraySort ([], A.bool_sort)) with
   | _ -> failwith "invalid constructor projector returned a value"
   | exception Invalid_argument _ -> ());
  (match Z3SeqTheory.nth [] Z.zero with
   | _ -> failwith "out-of-range sequence access returned a value"
   | exception Invalid_argument _ -> ())

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
    let premises = List.map (fun conclusion1 ->
        { U.conclusion = conclusion1; hypotheses = [] }) facts in
    require (match U.check_node [] {
        U.kind = U.Unverified "th-lemma"; conclusion1 = conclusion; premises } with
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
     "sorted-quantifier-Boolean-rewrites", sorted_quantifier_rewrites;
     "sorted-native-universal-flattening", sorted_quantifier_flattening;
     "sorted-native-quantifier-instances", sorted_quantifier_instances;
     "malformed-foreign-certificate", malformed_foreign_certificate;
     "assumed-NLSAT-obligation", assumed_nlsat;
     "checked-Boolean-constant-resolution", boolean_constant_resolution;
     "checked-integer-division-axioms", integer_division_axioms;
     "typed-observations-and-root-guard", typed_observations;
     "checked-arithmetic-rewrites", arithmetic_rewrites;
     "checked-array-unequal-defaults", array_unequal_defaults;
     "checked-bit-vector-rewrites", bv_rewrites;
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
     "erased-refinement-runtime-guards", erased_refinement_guards;
     "native-proof-check-callback", proof_check_callback;
     "proof-callback-exceptions", proof_callback_exceptions;
     "proof-callback-ownership", proof_callback_ownership;
     "checked-finite-field-rewrites", ff_rewrites;
     "checked-finite-field-theory-lemmas", ff_theory_lemmas;
     "checked-finite-field-certificates", ff_certificates]
