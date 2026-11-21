module A = Z3AstTheory
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module S = Z3DatatypeSignature
module Old = Z3SortedProof
module New = Z3IndependentSkolemReplay
module Root = Z3SortedRootDocument
module Checker = Z3IndependentChecker
module R = Z3ClauseSyntax

let require value message = if not value then failwith message

let symbol name domain range =
  { A.decl_name = name; domain; range; interp = None; int_params = [] }

let int_sort = A.SortApp (A.IntSymbol, [])
let schema = { S.sorts = []; cases = [] }
let witness = symbol "sk" [] int_sort

let document n =
  let pred = symbol "p" (List.init n (fun _ -> int_sort)) A.bool_sort in
  let source = A.Quantifier (A.Exists_k, [int_sort], A.bool_sort,
                             A.App (pred, List.init n (fun _ -> A.Var (Z.zero, int_sort)))) in
  let inst = A.App (pred, List.init n (fun _ -> A.App (witness, []))) in
  let entry = { P.rule = U.Skolemization;
                formula = A.App (Z3ObservationalSyntax.typed_oeq_decl A.bool_sort, [source; inst]);
                premise_ids = [] } in
  let doc = { P.declarations = []; expressions = []; assertions = []; entries = [entry]; root = Z.zero } in
  doc, entry, inst

let () =
  let doc, entry, inst = document 2050 in
  require (Old.epsilon_definition schema entry = None) "old budget should exclude the candidate";
  let defs = New.context schema doc in
  require (List.length defs = 1) "new budget should collect the candidate";
  require (List.length (New.equations schema defs doc.P.entries) = 1) "missing choice equation";
  let expanded = New.elaborate schema defs doc in
  require ((List.hd expanded.P.entries).P.rule = U.Asserted) "choice entry not elaborated";
  require (New.context schema { doc with P.assertions = [inst] } = []) "nonfresh witness accepted";
  require (New.context schema { doc with P.entries = [{ entry with P.premise_ids = [Z.zero] }] } = [])
    "Skolem premise accepted";
  let too_large, _, _ = document 4100 in
  require (New.context schema too_large = []) "candidate exceeding 8192 nodes accepted";
  let false_entry = { P.rule = U.Asserted; formula = R.false_expr; premise_ids = [] } in
  let refutation = { doc with P.assertions = [R.false_expr];
    entries = [entry; false_entry]; root = Z.one } in
  List.iter (fun candidate ->
    let verdict, diagnostic = Checker.check_diagnosed schema candidate in
    require (verdict = Checker.check schema candidate) "cached core verdict changed";
    require (diagnostic = Checker.diagnose schema candidate) "cached core diagnostics changed")
    [doc; refutation; { refutation with P.entries = [false_entry]; root = Z.zero }];
  require (match Checker.check schema refutation with Root.RootPending _ -> true | _ -> false)
    "baseline Skolem control was not pending";
  require (Checker.check_definition schema refutation = Root.RootCertified)
    "definition route did not use the verified Skolem fallback";
  require (Checker.diagnose_definition schema refutation = P.DocumentChecked (Z.zero, []))
    "Skolem fallback diagnostics disagree with verdict";
  let unsafe = { refutation with P.assertions = [R.false_expr; inst] } in
  require (Checker.check_definition schema unsafe = Checker.check schema unsafe)
    "nonfresh Skolem fallback changed the original verdict";
  let definition = { false_entry with P.rule = U.DefinitionIntroduction } in
  let mixed = { refutation with P.entries = refutation.P.entries @ [definition] } in
  require (Checker.check_definition schema mixed = Checker.check schema mixed)
    "definition-free Skolem fallback ran on a mixed document";
  print_endline "bounded Skolem replay tests passed"
