module N = Z3Native
module B = Z3NativeProof
module P = Z3ProofDocument
module U = Z3UnifiedProof
module A = Z3AstTheory

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

let native_integer_obligations () =
  let doc = document
      "(declare-const x Int)(declare-const y Int)(declare-const z Int)\
       (assert (= (+ x (* 2 y)) 0))(assert (= (+ x (* 2 z)) 1))" in
  require (List.exists (fun e -> e.P.rule = U.Unverified "arith/lp-integer-tighten") doc.entries)
    "integer LP inference metadata was hidden";
  match P.check_document doc with
  | Some pending -> require (Z.sign pending > 0) "integer LP inference was silently trusted"
  | None -> failwith "native integer proof document was malformed"

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

let malformed_foreign_certificate () =
  let c = context () in
  let conclusion = List.hd (parse c "(assert false)") in
  let view = { N.proof_name = "th-lemma"; premises = []; conclusion;
               farkas = Some [Z.one, Z.zero]; assumed = None } in
  match B.native_rule view Z3ResolutionProofTheory.false_expr with
  | _ -> failwith "malformed foreign certificate was accepted"
  | exception N.Error _ -> ()

let assumed_nlsat () =
  let c = context () in
  let conclusion = List.hd (parse c "(assert false)") in
  let view = { N.proof_name = "th-lemma"; premises = []; conclusion;
               farkas = None; assumed = Some "nlsat" } in
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
  check false reals "(+ x y)" "(+ y x)";
  check false reals "(<= (/ x 0) y)" "(<= x y)";
  check false ints "(* x y)" "(+ x y)";
  let x = A.Var (Z.zero, A.BaseSort "Int") in
  let malformed = { (Z3ResolutionProofTheory.eq_decl (A.BaseSort "Int"))
    with decl_name = "<="; interp = None } in
  require (not (U.check_step U.RewriteRule
      (U.Equal (A.App (malformed, [x; x]), Z3ResolutionProofTheory.true_expr)) []))
    "uninterpreted comparison was treated as arithmetic"

let () =
  ignore (N.version ());
  List.iter (fun (name, test) ->
      test (); Printf.printf "PASS %s\n%!" name)
    ["shared-expression-identity", shared_expressions;
     "deep-expression-worklist", deep_expression;
     "proof-DAG-cache", proof_cache;
     "exact-native-numerals", exact_numerals;
     "authentic-Farkas-parameters", native_farkas;
     "explicit-integer-LP-obligations", native_integer_obligations;
     "strict-inputs-and-scopes", strict_inputs_and_scopes;
     "typed-obligation-diagnostics", typed_diagnostics;
     "identity-and-binders", identity_and_binders;
     "malformed-foreign-certificate", malformed_foreign_certificate;
     "assumed-NLSAT-obligation", assumed_nlsat;
     "typed-observations-and-root-guard", typed_observations;
     "checked-arithmetic-rewrites", arithmetic_rewrites]
