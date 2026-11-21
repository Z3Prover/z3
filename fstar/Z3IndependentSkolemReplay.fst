module Z3IndependentSkolemReplay

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module D = Z3ExprScope
module E = Z3SortedSkolem
module SK = Z3SkolemSyntax
module SP = Z3SortedProof
module L = FStar.List.Tot

let definition (s:S.checked_schema) (e:P.entry) : option (E.definition s) =
  if e.P.rule <> U.Skolemization || e.P.premise_ids <> [] ||
     not (Some? (expression_budget 8192 e.P.formula)) then None
  else match U.classify_fact e.P.formula with
  | Some (U.Observational a b) -> E.definition_of s a b
  | _ -> None

let inner_definition (s:S.checked_schema) (b:U.binder_entry) : option (E.definition s) =
  if b.U.binder_name <> "sk" || b.U.binder_premises <> [] || Some? b.U.binder_sorts ||
     not (Some? (expression_budget 8192 b.U.binder_formula)) ||
     not (D.scoped [] b.U.binder_formula && SP.in_context s b.U.binder_formula) then None
  else match U.classify_fact b.U.binder_formula with
  | Some (U.Observational a c) -> E.definition_of s a c
  | _ -> None

let rec collect_inner (s:S.checked_schema) (defs:list SK.definition) (bs:list U.binder_entry)
  : Tot (option (list SK.definition)) (decreases bs) =
  match bs with
  | [] -> Some defs
  | b :: rest ->
    match inner_definition s b with
    | None -> collect_inner s defs rest
    | Some d ->
      (match SK.add_definition defs d with
       | None -> None
       | Some more -> collect_inner s more rest)

let rec collect (s:S.checked_schema) (defs:list SK.definition) (entries:list P.entry)
  : Tot (option (list SK.definition)) (decreases entries) =
  match entries with
  | [] -> Some defs
  | e :: rest ->
    let here = match definition s e with
      | None -> Some defs
      | Some d -> SK.add_definition defs d in
    (match here with
     | None -> None
     | Some more ->
       (match SP.nnf_certificate e with
        | None -> collect s more rest
        | Some c ->
          (match collect_inner s more c.U.binder_entries with
           | None -> None
           | Some next -> collect s next rest)))

let context (s:S.checked_schema) (doc:P.document)
  : ds:list (E.definition s){
      SK.ordered_context (E.erase s ds) /\ SK.fresh_inputs (E.erase s ds) doc.P.assertions} =
  SP.certified_context s doc (collect s [] doc.P.entries)

let entry_used (s:S.checked_schema) (ds:list (E.definition s)) (e:P.entry) : bool =
  match definition s e with None -> false | Some d -> L.mem d ds

let inner_used (s:S.checked_schema) (ds:list (E.definition s)) (b:U.binder_entry) : bool =
  match inner_definition s b with None -> false | Some d -> L.mem d ds

let rec inner_equations (s:S.checked_schema) (ds:list (E.definition s))
                        (bs:list U.binder_entry) (acc:list expr)
  : Tot (list expr) (decreases bs) =
  match bs with
  | [] -> acc
  | b :: rest ->
    if inner_used s ds b then
      (match U.classify_fact b.U.binder_formula with
       | Some j -> inner_equations s ds rest (SP.proposition j :: acc)
       | None -> inner_equations s ds rest acc)
    else inner_equations s ds rest acc

let rec equations_acc (s:S.checked_schema) (ds:list (E.definition s))
                      (entries:list P.entry) (acc:list expr)
  : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    let next =
      match SP.nnf_certificate e with
      | Some c -> inner_equations s ds c.U.binder_entries acc
      | None -> acc in
    let next' =
      if entry_used s ds e then
        match U.classify_fact e.P.formula with
        | Some j -> SP.proposition j :: next
        | None -> next
      else next in
    equations_acc s ds rest next'

let equations (s:S.checked_schema) (ds:list (E.definition s)) (entries:list P.entry) : list expr =
  equations_acc s ds entries []

let rec replay_entries_acc (s:S.checked_schema) (ds:list (E.definition s))
                           (entries acc:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    replay_entries_acc s ds rest ((if entry_used s ds e then { e with P.rule = U.Asserted } else e) :: acc)

let replay_entries (s:S.checked_schema) (ds:list (E.definition s)) (entries:list P.entry)
  : list P.entry = L.rev (replay_entries_acc s ds entries [])

let elaborate (s:S.checked_schema) (ds:list (E.definition s)) (doc:P.document) : P.document =
  if ds = [] then doc
  else { doc with P.assertions = doc.P.assertions @ equations s ds doc.P.entries;
                  P.entries = replay_entries s ds doc.P.entries }

let rec lemma_inner_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                              (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                              (ds:list (E.definition s)) (bs:list U.binder_entry) (acc:list expr)
  : Lemma (requires E.context_model s bc eq other ds /\ T.truths s bc eq other acc)
          (ensures T.truths s bc eq other (inner_equations s ds bs acc))
          (decreases bs) =
  match bs with
  | [] -> ()
  | b :: rest ->
    if inner_used s ds b then (
      let d = Some?.v (inner_definition s b) in
      E.lemma_context_member s bc eq other ds d;
      match U.classify_fact b.U.binder_formula with
      | Some (U.Observational a c) ->
        E.lemma_definition_parts s a c d;
        T.lemma_boolean_equality s bc eq other a c;
        lemma_inner_equations s bc eq other ds rest (SP.proposition (U.Observational a c) :: acc)
      | _ -> ())
    else lemma_inner_equations s bc eq other ds rest acc

let rec lemma_equations_acc (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (ds:list (E.definition s)) (entries:list P.entry) (acc:list expr)
  : Lemma (requires E.context_model s bc eq other ds /\ T.truths s bc eq other acc)
          (ensures T.truths s bc eq other (equations_acc s ds entries acc))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    let next =
      match SP.nnf_certificate e with
      | Some c -> inner_equations s ds c.U.binder_entries acc
      | None -> acc in
    (match SP.nnf_certificate e with
     | Some c -> lemma_inner_equations s bc eq other ds c.U.binder_entries acc
     | None -> ());
    if entry_used s ds e then (
      let d = Some?.v (definition s e) in
      E.lemma_context_member s bc eq other ds d;
      match U.classify_fact e.P.formula with
      | Some (U.Observational a b) ->
        E.lemma_definition_parts s a b d;
        T.lemma_boolean_equality s bc eq other a b;
        lemma_equations_acc s bc eq other ds rest (SP.proposition (U.Observational a b) :: next)
      | _ -> ())
    else lemma_equations_acc s bc eq other ds rest next

let lemma_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (ds:list (E.definition s)) (entries:list P.entry)
  : Lemma (requires E.context_model s bc eq other ds)
          (ensures T.truths s bc eq other (equations s ds entries)) =
  lemma_equations_acc s bc eq other ds entries []

let test_int = SortApp IntSymbol []
let test_symbol name domain range =
  { decl_name = name; domain = domain; range = range; interp = None; int_params = [] }
let test_pred = test_symbol "p" [test_int] bool_sort
let test_witness = test_symbol "sk" [] test_int
let test_inst = App test_pred [App test_witness []]
let test_source = Quantifier Exists_k [test_int] bool_sort (App test_pred [Var 0 test_int])
let test_entry = { P.rule = U.Skolemization;
  P.formula = Z3ObservationalSyntax.mk_oeq_expr test_source test_inst; P.premise_ids = [] }
let test_doc = { P.declarations = []; P.expressions = []; P.assertions = [];
  P.entries = [test_entry]; P.root = 0 }
let test_schema = { S.sorts = []; S.cases = [] }
let test_other = test_symbol "other" [test_int] bool_sort
let test_other_source = Quantifier Exists_k [test_int] bool_sort (App test_other [Var 0 test_int])
let test_conflict = { test_entry with P.formula =
  Z3ObservationalSyntax.mk_oeq_expr test_other_source (App test_other [App test_witness []]) }

let test_context () : Lemma True =
  assert_norm (L.length (context test_schema test_doc) = 1);
  assert_norm (equations test_schema (context test_schema test_doc) test_doc.P.entries =
    [SP.proposition (U.Observational test_source test_inst)]);
  assert_norm ((elaborate test_schema (context test_schema test_doc) test_doc).P.entries =
    [{ test_entry with P.rule = U.Asserted }]);
  assert_norm (context test_schema { test_doc with P.assertions = [test_inst] } = []);
  assert_norm (context test_schema { test_doc with P.entries =
    [{ test_entry with P.premise_ids = [0] }] } = []);
  assert_norm (context test_schema { test_doc with P.entries =
    [{ test_entry with P.rule = U.RewriteRule }] } = []);
  assert_norm (context test_schema { test_doc with P.entries = [test_entry; test_conflict] } = [])

