module Z3IndependentDependentReplay

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module D = Z3ExprScope
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module SK = Z3SkolemSyntax
module SP = Z3SortedProof
module L = FStar.List.Tot

let definition (s:S.checked_schema) (b:U.binder_entry) : option (DS.definition s) =
  if b.U.binder_name <> "sk" || b.U.binder_premises <> [] || Some? b.U.binder_sorts ||
     not (Some? (expression_budget 8192 b.U.binder_formula)) || D.scoped [] b.U.binder_formula
  then None
  else match U.classify_fact b.U.binder_formula with
  | Some (U.Observational x y) ->
    (match DS.definition_of s x y with
     | Some d -> if SP.boolean_expression s (DS.closure d) then Some d else None
     | None -> None)
  | _ -> None

let rec collect_inner (s:S.checked_schema) (defs:list SK.definition) (bs:list U.binder_entry)
  : Tot (option (list SK.definition)) (decreases bs) =
  match bs with
  | [] -> Some defs
  | b :: rest ->
    (match definition s b with
     | None -> collect_inner s defs rest
     | Some d ->
       (match SK.add_definition defs d with
        | None -> None
        | Some more -> collect_inner s more rest))

let rec collect (s:S.checked_schema) (defs:list SK.definition) (entries:list P.entry)
  : Tot (option (list SK.definition)) (decreases entries) =
  match entries with
  | [] -> Some defs
  | e :: rest ->
    (match SP.nnf_certificate e with
     | None -> collect s defs rest
     | Some c ->
       (match collect_inner s defs c.U.binder_entries with
        | None -> None
        | Some more -> collect s more rest))

let context (s:S.checked_schema) (doc:P.document)
            (closed:list (E.definition s){SK.ordered_context (E.erase s closed)})
  : dds:list (DS.definition s){
      SK.ordered_context (DS.erase s dds @ E.erase s closed) /\
      SK.fresh_inputs (DS.erase s dds) doc.P.assertions} =
  match collect s [] doc.P.entries with
  | None -> []
  | Some defs ->
    (match SK.order_context (L.length defs) (L.rev defs) with
     | None -> []
     | Some ordered ->
       (match SP.certify_dependent s ordered with
        | None -> []
        | Some dds ->
          if SK.ordered_context (DS.erase s dds @ E.erase s closed) &&
             SK.fresh_inputs (DS.erase s dds) doc.P.assertions
          then dds else []))

let rec inner_may_change (s:S.checked_schema) (bs:list U.binder_entry)
  : Tot bool (decreases bs) =
  match bs with
  | [] -> false
  | b :: rest ->
    if SP.dependent_definition s b <> definition s b then true
    else inner_may_change s rest

let rec entries_may_change (s:S.checked_schema) (entries:list P.entry)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest ->
    (match SP.nnf_certificate e with
     | None -> entries_may_change s rest
     | Some c -> inner_may_change s c.U.binder_entries || entries_may_change s rest)

let may_change (s:S.checked_schema) (doc:P.document) : bool =
  entries_may_change s doc.P.entries

let rec lemma_inner_unchanged (s:S.checked_schema) (defs:list SK.definition)
                              (bs:list U.binder_entry)
  : Lemma (requires not (inner_may_change s bs))
          (ensures collect_inner s defs bs == SP.collect_dependent s defs bs)
          (decreases bs) =
  match bs with
  | [] -> ()
  | b :: rest ->
    (match definition s b with
     | None -> lemma_inner_unchanged s defs rest
     | Some d ->
       (match SK.add_definition defs d with
        | None -> ()
        | Some more -> lemma_inner_unchanged s more rest))

let rec lemma_entries_unchanged (s:S.checked_schema) (defs:list SK.definition)
                                (entries:list P.entry)
  : Lemma (requires not (entries_may_change s entries))
          (ensures collect s defs entries == SP.collect_dependents s defs entries)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match SP.nnf_certificate e with
     | None -> lemma_entries_unchanged s defs rest
     | Some c ->
       lemma_inner_unchanged s defs c.U.binder_entries;
       (match collect_inner s defs c.U.binder_entries with
        | None -> ()
        | Some more -> lemma_entries_unchanged s more rest))

let lemma_unchanged (s:S.checked_schema) (doc:P.document)
                    (closed:list (E.definition s){SK.ordered_context (E.erase s closed)})
  : Lemma (requires not (may_change s doc))
          (ensures context s doc closed == SP.dependent_context s doc closed) =
  lemma_entries_unchanged s [] doc.P.entries

let test_int = SortApp IntSymbol []
let test_symbol (name:string) (domain:list sort) (range:sort) : func_decl =
  { decl_name = name; domain = domain; range = range; interp = None; int_params = [] }
let test_pred = test_symbol "p" [test_int; test_int] bool_sort
let test_witness = test_symbol "sk" [test_int] test_int
let test_source = Quantifier Exists_k [test_int] bool_sort
  (App test_pred [Var 0 test_int; Var 1 test_int])
let test_inst = App test_pred [App test_witness [Var 0 test_int]; Var 0 test_int]
let test_equation = App (Z3ObservationalSyntax.typed_oeq_decl bool_sort) [test_source; test_inst]
let test_be (name:string) (premises:list int) : U.binder_entry =
  { U.binder_name = name; binder_formula = test_equation; binder_premises = premises; binder_sorts = None }
let test_doc (b:U.binder_entry) (assertions:list expr) : P.document =
  let cert = { U.binder_entries = [b; test_be "nnf-neg" []]; binder_root = 1 } in
  { P.declarations = []; expressions = []; assertions = assertions;
    entries = [{ P.rule = U.QuantifierIntroduction cert; formula = test_equation; premise_ids = [] }];
    root = 0 }
let test_schema : S.checked_schema = { S.sorts = []; cases = [] }

let test_controls ()
  : Lemma (L.length (context test_schema (test_doc (test_be "sk" []) []) []) == 1 /\
           context test_schema (test_doc (test_be "sk" [0]) []) [] == [] /\
           context test_schema (test_doc (test_be "refl" []) []) [] == [] /\
           context test_schema (test_doc (test_be "sk" []) [test_inst]) [] == []) =
  assert_norm (L.length (context test_schema (test_doc (test_be "sk" []) []) []) == 1);
  assert_norm (context test_schema (test_doc (test_be "sk" [0]) []) [] == []);
  assert_norm (context test_schema (test_doc (test_be "refl" []) []) [] == []);
  assert_norm (context test_schema (test_doc (test_be "sk" []) [test_inst]) [] == [])
