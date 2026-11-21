module A = Z3AstTheory
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module S = Z3DatatypeSignature
module Old = Z3SortedProof
module New = Z3IndependentDependentReplay
module Root = Z3IndependentSkolemRoot

let require value message = if not value then failwith message
let symbol name domain range =
  { A.decl_name = name; domain; range; interp = None; int_params = [] }
let int_sort = A.SortApp (A.IntSymbol, [])
let schema = { S.sorts = []; cases = [] }
let witness = symbol "sk" [int_sort] int_sort

let document n =
  let pred = symbol "p" (List.init (n + 1) (fun _ -> int_sort)) A.bool_sort in
  let source = A.Quantifier (A.Exists_k, [int_sort], A.bool_sort,
      A.App (pred, A.Var (Z.zero, int_sort) ::
                   List.init n (fun _ -> A.Var (Z.one, int_sort)))) in
  let inst = A.App (pred, A.App (witness, [A.Var (Z.zero, int_sort)]) ::
                          List.init n (fun _ -> A.Var (Z.zero, int_sort))) in
  let formula = A.App (Z3ObservationalSyntax.typed_oeq_decl A.bool_sort, [source; inst]) in
  let binder name premises =
    { U.binder_name = name; binder_formula = formula;
      binder_premises = premises; binder_sorts = None } in
  let step = binder "sk" [] in
  let cert = { U.binder_entries = [step; binder "nnf-neg" []]; binder_root = Z.one } in
  let entry = { P.rule = U.QuantifierIntroduction cert; formula; premise_ids = [] } in
  { P.declarations = []; expressions = []; assertions = []; entries = [entry]; root = Z.zero },
  step, inst

let () =
  let doc, step, inst = document 2050 in
  require (Old.dependent_definition schema step = None) "old budget should exclude the candidate";
  require (List.length (New.context schema doc []) = 1) "new budget should collect the candidate";
  require (Root.contexts_may_differ schema doc) "different contexts were not detected";
  require (New.context schema { doc with P.assertions = [inst] } [] = []) "nonfresh witness accepted";
  require (Root.contexts_may_differ schema { doc with P.assertions = [inst] })
    "candidate detection must not depend on original assertions";
  let small, _, _ = document 1 in
  require (not (Root.contexts_may_differ schema small)) "small definition should leave contexts equal";
  let oversized, _, _ = document 4100 in
  require (New.context schema oversized [] = []) "candidate exceeding 8192 nodes accepted";
  require (not (Root.contexts_may_differ schema oversized)) "oversized candidate changed the context";
  print_endline "bounded dependent Skolem replay tests passed"
