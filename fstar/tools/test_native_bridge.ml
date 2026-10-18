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
     (fun value -> Z.of_int (Hashtbl.hash value))];
  let values = [Z.zero; Z.one; Z.one; Z.of_int 65521] in
  List.iter (fun hash ->
    let index = Z3ProofSet.of_list hash values in
    List.iter (fun query ->
      require (Z3ProofSet.member hash query index = List.mem query values)
        "hash bucket did not preserve exact membership")
      [Z.zero; Z.one; Z.of_int 2; Z.of_int 65521])
    [(fun _ -> Z.zero); (fun value -> value)]

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
     "bv-premise", ["(= (bvand v v) w)"], "(= v w)", true;
     "invalid-bv-consequence", ["(= (bvand v v) w)"], "(= v (bvnot w))", false];
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
     "indexed-assertion-membership", indexed_assertion_membership;
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
     "certified-quantifier-reductions-and-lambdas", checked_quantifier_reductions;
     "certified-nested-NNF-replacement", checked_nested_nnf_replacement;
     "certified-theory-lemmas-and-definition-axioms", checked_theory_extensions;
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
