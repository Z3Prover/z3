module A = Z3AstTheory
module D = Z3DefinitionSyntax
module R = Z3ClauseSyntax
module G = Z3IndependentGroundDefinition
module S = Z3DatatypeSignature
module Tags = Z3OperatorTags
module U = Z3UnifiedProofSyntax
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module Doc = Z3IndependentGroundDocument
module Checker = Z3IndependentChecker

let require value message = if not value then failwith message
let schema = { S.sorts = []; cases = [] }
let int_sort = A.SortApp (A.IntSymbol, [])
let array_sort = A.ArraySort ([int_sort], int_sort)
let decl name domain range interp int_params =
  { A.decl_name = name; domain; range; interp; int_params }
let constant name sort = A.App (decl name [] sort None [], [])
let array = constant "a" array_sort
let index = constant "i" int_sort
let value = constant "v" int_sort
let store = decl "store" [array_sort; int_sort; int_sort] array_sort (Some Tags.op_store) []
let body = A.App (store, [array; index; value])
let symbol = decl "fresh-array" [] array_sort None []
let name = A.App (symbol, [])
let definition = { D.symbol; variables = []; body }
let input = R.mk_eq_expr array array

let () =
  let formula = R.mk_eq_expr body name in
  let reverse = R.mk_eq_expr name body in
  require (G.recognize schema [input] formula = Some definition) "ground definition was not recognized";
  require (G.recognize schema [input] reverse = Some definition) "reversed definition was not recognized";
  require (G.recognize schema [R.mk_eq_expr name name] formula = None) "nonfresh input was accepted";
  require (G.recognize schema [input] (R.mk_eq_expr name name) = None) "cyclic definition was accepted";
  let tagged = A.App ({ symbol with A.interp = Some Tags.op_store }, []) in
  require (G.recognize schema [input] (R.mk_eq_expr body tagged) = None)
    "interpreted symbol was accepted";
  require (G.recognize schema [input] (R.mk_eq_expr name (A.Var (Z.zero, array_sort))) = None)
    "unscoped body was accepted";
  let malformed = match formula with
    | A.App (f, args) -> A.App ({ f with A.int_params = [Z.one] }, args)
    | _ -> assert false in
  require (G.recognize schema [input] malformed = None) "malformed equality was accepted";
  let rec oversized n e = if n = 0 then e else oversized (n - 1) (R.mk_eq_expr e e) in
  require (G.recognize schema [input] (oversized 14 R.true_expr) = None)
    "oversized formula was accepted";
  let entry = { P.rule = U.DefinitionIntroduction; formula; premise_ids = [] } in
  let asserted = { P.rule = U.Asserted; formula = R.false_expr; premise_ids = [] } in
  let document = { P.declarations = []; expressions = []; assertions = [R.false_expr];
                   entries = [entry; asserted]; root = Z.one } in
  require (Root.check_root_document_epsilon schema document = Root.RootPending Z.one)
    "ground definition was not originally pending";
  require (Doc.selected schema document <> None) "ground document was not selected";
  require (Checker.check_definition schema document = Root.RootCertified)
    "ground document was not certified";
  require (Checker.diagnose_definition schema document = P.DocumentChecked (Z.zero, []))
    "ground document diagnostic did not reflect replay";
  let nonfresh = { document with P.assertions = [R.false_expr; R.mk_eq_expr name name] } in
  require (Doc.selected schema nonfresh = None) "nonfresh document was selected";
  require (Checker.check_definition schema nonfresh = Root.check_root_document_epsilon schema nonfresh)
    "nonfresh document changed its verdict";
  let with_premise = { document with P.entries = [{ entry with P.premise_ids = [Z.zero] }; asserted] } in
  require (Doc.selected schema with_premise = None) "premise-bearing definition was selected";
  let cyclic = { document with P.entries =
    [{ entry with P.formula = R.mk_eq_expr name name }; asserted] } in
  require (Doc.selected schema cyclic = None) "cyclic document was selected";
  let duplicate = { document with P.entries =
    [entry; { entry with P.formula = R.mk_eq_expr name array }; asserted]; root = Z.of_int 2 } in
  require (Doc.selected schema duplicate = None) "unproved second definition was accepted";
  print_endline "ground definition tests passed"
