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
  B.marshal assertions proof

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
   | _ -> failwith "input membership failure was not diagnosed")

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
    "term-valued lambda congruence was not checked"

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
  require (not (Z3QuantifierInstantiation.check [zero] formula))
    "nested substitution was accepted without a capture-avoidance proof"

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

let malformed_foreign_certificate () =
  let c = context () in
  let conclusion = List.hd (parse c "(assert false)") in
  let view = { N.proof_name = "th-lemma"; premises = []; conclusion;
               farkas = Some [Z.one, Z.zero]; assumed = None; lp_data = None;
               binding = None; instantiations = [] } in
  match B.native_rule view Z3ResolutionProofTheory.false_expr with
  | _ -> failwith "malformed foreign certificate was accepted"
  | exception N.Error _ -> ()

let assumed_nlsat () =
  let c = context () in
  let conclusion = List.hd (parse c "(assert false)") in
  let view = { N.proof_name = "th-lemma"; premises = []; conclusion;
               farkas = None; assumed = Some "nlsat"; lp_data = None;
               binding = None; instantiations = [] } in
  let rule = B.native_rule view Z3ResolutionProofTheory.false_expr in
  require (rule = U.Unverified "assumed:nlsat")
    "native NLSAT assumption lost its origin";
  let doc = document "(assert false)" in
  let entry = { P.rule = rule; formula = Z3ResolutionProofTheory.false_expr; premise_ids = [] } in
  require (P.check_document { doc with assertions = []; entries = [entry]; root = Z.zero } = Some Z.one)
    "assumed NLSAT lemma was certified without an obligation"

let typed_observations () =
  let c = context () in
  let source = List.hd (parse c "(declare-const x Int)(assert (= x x))") in
  let st = B.marshal_expressions (B.empty_state ()) [source] in
  let x = match B.cached_expression st source with
    | A.App (_, [x; _]) -> x | _ -> failwith "expected equality" in
  let foreign = { N.id = Z.of_int 12345; name = "~"; unique_name = "native-oeq";
                  op = N.Oeq; range = Z3native.mk_bool_sort c;
                  numeral = None; native_kind = Z.zero } in
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
  check true "(or (not (= x y)) (<= (- x y) 0))";
  check true "(or (not (= x y)) (>= (- x y) 0))";
  check false "(or (not (= x y)) (< (- x y) 0))";
  check false "(or (not (= x y)) (<= (- x y) (- 1)))";
  check false "(or (= x y) (not (< (- x y) 0)) (not (>= (- x y) 0)))";
  check false "(or (= x y) (not (<= (- x y) 0)) (not (<= (- x y) 0)))";
  check false "(or (= x (+ 1 y)) (not (<= (- x y) 0)) (not (>= (- x y) 0)))"

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

let () =
  ignore (N.version ());
  List.iter (fun (name, test) ->
      test (); Printf.printf "PASS %s\n%!" name)
    ["shared-expression-identity", shared_expressions;
     "deep-expression-worklist", deep_expression;
     "proof-DAG-cache", proof_cache;
     "exact-native-numerals", exact_numerals;
     "authentic-Farkas-parameters", native_farkas;
     "certified-assign-bounds-parameters", native_assign_bounds;
     "checked-native-integer-LP-tightening", native_integer_tightening;
     "certified-duplicate-distinct-rewrites", distinct_reflexivity;
     "integer-tightening-candidate-mutations", integer_tightening_candidates;
     "typed-native-LP-certificate-decoding", native_lp_certificates;
     "authentic-bound-parameters", native_bound;
     "strict-inputs-and-scopes", strict_inputs_and_scopes;
     "typed-obligation-diagnostics", typed_diagnostics;
     "identity-and-binders", identity_and_binders;
     "certified-hidden-binder-proof-DAGs", checked_binder_proofs;
     "certified-native-quantifier-instances", checked_quantifier_instances;
     "certified-negative-NNF", checked_negative_nnf;
     "malformed-foreign-certificate", malformed_foreign_certificate;
     "assumed-NLSAT-obligation", assumed_nlsat;
     "typed-observations-and-root-guard", typed_observations;
     "checked-arithmetic-rewrites", arithmetic_rewrites;
     "contextual-boolean-rewrites", contextual_boolean_rewrites;
     "unused-quantifier-rewrites", unused_quantifier_rewrites;
     "checked-triangle-equality-clauses", arithmetic_triangle_clauses;
     "erased-refinement-runtime-guards", erased_refinement_guards;
     "native-proof-check-callback", proof_check_callback;
     "proof-callback-exceptions", proof_callback_exceptions;
     "proof-callback-ownership", proof_callback_ownership]
