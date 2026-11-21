module A = Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module P = Z3DocumentSyntax
module S = Z3DatatypeSignature
module Old = Z3NnfReplay
module New = Z3IndependentBinderReplay
module Elab = Z3IndependentBinderElaboration
module Root = Z3SortedRootDocument
module SkolemRoot = Z3IndependentSkolemRoot
module Scope = Z3BinderScopeSyntax
module Index = Z3ProofIndex
module Checker = Z3IndependentChecker

let require value message = if not value then failwith message
let symbol name domain range =
  { A.decl_name = name; domain; range; interp = None; int_params = [] }
let int_sort = A.SortApp (A.IntSymbol, [])
let schema = { S.sorts = []; cases = [] }

let reference_augment doc =
  let additions = List.fold_left (fun acc e ->
    match Elab.candidate schema doc.P.assertions e with
    | Some j -> Z3SortedProof.proposition j :: acc
    | None -> acc) [] doc.P.entries in
  let entries = List.map (fun e ->
    match Elab.candidate schema doc.P.assertions e with
    | Some _ -> { e with P.rule = U.Asserted }
    | None -> e) doc.P.entries in
  { doc with P.assertions = doc.P.assertions @ additions; entries }

let certificate_with_body_sort n binder_sort body_sort =
  let pred = symbol "p" (List.init n (fun _ -> body_sort)) A.bool_sort in
  let body = A.App (pred, List.init n (fun _ -> A.Var (Z.zero, body_sort))) in
  let quantified = A.Quantifier (A.Forall_k, [binder_sort], A.bool_sort, body) in
  let eq a b = A.App (R.eq_decl A.bool_sort, [a; b]) in
  let inner = { U.binder_name = "refl"; binder_formula = eq body body;
                binder_premises = []; binder_sorts = None } in
  let outer = { U.binder_name = "quant-intro"; binder_formula = eq quantified quantified;
                binder_premises = [Z.zero]; binder_sorts = Some [binder_sort] } in
  { U.binder_entries = [inner; outer]; binder_root = Z.one }, U.Equal (quantified, quantified)

let certificate n binder_sort = certificate_with_body_sort n binder_sort int_sort

let () =
  let check_name s =
    let expected = Scope.count_cells Z.zero (FStar_String.list_of_string s) in
    require (Z.equal (Scope.name_length s) expected) "native name length changed";
    require (Z.equal (Scope.name_pair_units s s) (Z.mul (Z.of_int 2) expected))
      "native equal-name charge changed" in
  List.iter check_name [
    ""; "ASCII"; "\194\162"; "\226\130\172"; "\240\159\152\128";
    "\128"; "\192\128"; "\226\130"; "\237\160\128"; "\244\144\128\128";
    "\224\128\128"; "\248\128\128\128"; "\255"; "\000"
  ];
  for a = 0 to 255 do
    for b = 0 to 255 do
      check_name (String.init 2 (function 0 -> Char.chr a | _ -> Char.chr b))
    done
  done;
  let rng = Random.State.make [| 2026; 11; 14 |] in
  for n = 0 to 4095 do
    check_name (String.init (n mod 64) (fun _ -> Char.chr (Random.State.int rng 256)))
  done;
  List.iter (fun byte -> check_name (String.make 1000000 byte)) ['a'; '\128'; '\255'];
  let wide_sort = A.BaseSort (String.make 64 'S') in
  let wide_cert, wide_conclusion = certificate_with_body_sort 900 wide_sort wide_sort in
  let wide_cache = Option.get (Old.judgments_of wide_cert.U.binder_entries Index.Empty Z.zero) in
  let wide_count = Scope.count_cells Z.zero wide_cert.U.binder_entries in
  require (not (Scope.binder_scoped_within (Scope.binder_demand_limit wide_count)
    (Z.mul (Z.of_int 4) (Scope.binder_work_limit wide_count)) wide_cert wide_cache))
    "wide-sort scope control did not exceed the previous budget";
  require (New.replay false [] wide_cert wide_conclusion = Old.Replayed)
    "expanded scope budget did not replay the wide-sort control";
  let cert, conclusion = certificate 10000 int_sort in
  require (Old.replay_with false [] cert conclusion = Old.Unreplayed) "old scope budget should be exceeded";
  require (New.replay false [] cert conclusion = Old.Replayed) "larger scope budget should replay";
  let formula = match conclusion with
    | U.Equal (a, b) -> A.App (R.eq_decl A.bool_sort, [a; b])
    | _ -> assert false in
  let entry = { P.rule = U.QuantifierIntroduction cert; formula; premise_ids = [] } in
  let doc = { P.declarations = []; expressions = []; assertions = [];
              entries = [entry]; root = Z.zero } in
  let augmented = Elab.augment schema doc in
  require (augmented = reference_augment doc) "single-pass elaboration changed the document";
  let selected_doc, selected = Elab.augment_with_selection schema doc in
  require (selected_doc = augmented && selected = [entry]) "selected binder was not recorded";
  require (SkolemRoot.binder_entries_covered_selected schema doc selected [entry])
    "selected binder not covered";
  require (SkolemRoot.binder_entries_covered_selected schema { doc with P.entries = [] } [] [entry])
    "missing expanded entry did not use replay fallback";
  require (List.length augmented.P.assertions = 1) "missing binder assertion";
  require ((List.hd augmented.P.entries).P.rule = U.Asserted) "binder entry not elaborated";
  require (not (Root.root_covered schema doc)) "old scope coverage should be exceeded";
  let with_premise = { doc with P.entries = [{ entry with P.premise_ids = [Z.zero] }] } in
  require ((Elab.augment schema with_premise).P.assertions = []) "entry with premises elaborated";
  let wrong_root = { cert with U.binder_root = Z.of_int 2 } in
  require (New.replay false [] wrong_root conclusion <> Old.Replayed) "invalid root accepted";
  let bad_premises = match cert.U.binder_entries with
    | [a; b] -> { cert with U.binder_entries = [a; { b with U.binder_premises = [Z.one] }] }
    | _ -> assert false in
  require (New.replay false [] bad_premises conclusion = Old.Malformed) "cyclic premise accepted";
  let cyclic = { doc with P.entries = [{ entry with P.rule = U.QuantifierIntroduction bad_premises }] } in
  require ((Elab.augment schema cyclic).P.assertions = []) "cyclic proof elaborated";
  require (Elab.augment schema cyclic = reference_augment cyclic) "malformed elaboration changed";
  let asserted = { P.rule = U.Asserted; formula = R.false_expr; premise_ids = [] } in
  let refutation entry = { doc with P.assertions = [R.false_expr]; entries = [entry; asserted]; root = Z.one } in
  let fallback_doc = refutation entry in
  require (Root.check_root_document_epsilon schema fallback_doc = Root.RootUncovered)
    "certificate fallback fixture is already covered";
  require (Checker.check schema fallback_doc = Root.RootCertified)
    "unused out-of-budget certificate blocked a checked refutation";
  require (Checker.check_diagnosed schema fallback_doc =
           (Root.RootCertified, P.DocumentChecked (Z.zero, [])))
    "certificate fallback changed the zero-obligation diagnostic";
  require (Checker.check_array schema fallback_doc = Root.RootCertified &&
           Checker.check_array_diagnosed schema fallback_doc =
           (Root.RootCertified, P.DocumentChecked (Z.zero, [])))
    "array wrapper lost the core certificate fallback";
  let unasserted = { fallback_doc with P.assertions = [] } in
  require (Checker.check schema unasserted = Root.RootRejected)
    "certificate fallback accepted an unasserted false conclusion";
  let pending = { fallback_doc with P.assertions = [];
    entries = [entry; { asserted with P.rule = U.Unverified "unsupported" }] } in
  require (Checker.check schema pending = Root.RootPending Z.one)
    "certificate fallback erased a pending obligation";
  require (SkolemRoot.check_binder schema (refutation entry) = Root.RootCertified) "binder root not certified";
  require (SkolemRoot.check_binder schema (refutation { entry with P.premise_ids = [Z.zero] }) <> Root.RootCertified)
    "binder with premises certified";
  require (SkolemRoot.check_binder schema
             (refutation { entry with P.rule = U.QuantifierIntroduction bad_premises }) <> Root.RootCertified)
    "cyclic binder certified";
  let mistyped, mistyped_conclusion = certificate 1 A.bool_sort in
  require (New.replay false [] mistyped mistyped_conclusion = Old.Unreplayed) "ill-scoped proof accepted";
  let mistyped_entry = { entry with P.rule = U.QuantifierIntroduction mistyped;
    formula = (match mistyped_conclusion with
      | U.Equal (a, b) -> A.App (R.eq_decl A.bool_sort, [a; b])
      | _ -> assert false) } in
  require (Checker.check schema (refutation mistyped_entry) <> Root.RootCertified)
    "certificate fallback bypassed entry scoping";
  let oversized, oversized_conclusion = certificate 50000 int_sort in
  require (New.replay false [] oversized oversized_conclusion = Old.Unreplayed) "oversized proof accepted";
  print_endline "bounded binder replay tests passed"
