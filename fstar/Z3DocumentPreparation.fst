module Z3DocumentPreparation

open Z3AstTheory
open Z3ClauseSyntax
open Z3ObservationalSyntax
open Z3UnifiedProofSyntax
include Z3DocumentSyntax
open Z3ProofIndex
module D = Z3DefinitionRecognition
module SK = Z3SkolemSyntax
module BF = Z3BvFreshSyntax
module S = Z3ProofSet
module IT = Z3IdTable
module L = FStar.List.Tot

let rec axiom_branches_rev (entries:list entry) (branches:list expr)
  : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> branches
  | e :: rest ->
    let branches =
      if e.rule = DefAxiom && D.axiom_branch e.formula && not (D.tautology 128 e.formula)
      then e.formula :: branches else branches in
    axiom_branches_rev rest branches

let axiom_branches (entries:list entry) : list expr =
  L.rev (axiom_branches_rev entries [])

let rec collect_definitions (defs:list D.definition) (branches:list expr) (entries:list entry)
  : Tot (option (list D.definition)) (decreases entries) =
  match entries with
  | [] -> Some defs
  | e :: rest ->
    if e.rule <> DefinitionIntroduction && e.rule <> DefAxiom
    then collect_definitions defs branches rest
    else if Cons? e.premise_ids || not (D.scoped [] e.formula) then None
    else
      let candidate = if e.rule = DefinitionIntroduction then D.definition_of e.formula
                      else D.axiom_definition e.formula branches in
      match candidate with
      | None ->
        if e.rule = DefinitionIntroduction then None else collect_definitions defs branches rest
      | Some d ->
        D.add_definition defs d >>= (fun defs' -> collect_definitions defs' branches rest)

let rec reconstruction_equations (entries:list entry) (found:list expr)
  : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> found
  | e :: rest ->
    let found =
      if e.rule <> RewriteRule || e.premise_ids <> [] then found
      else match BF.candidate e.formula with
      | None -> found
      | Some r ->
        let equation = mk_eq_expr (BF.source r) (BF.word r) in
        if BF.valid r &&
           (e.formula = equation || e.formula = mk_eq_expr (BF.word r) (BF.source r)) &&
           not (L.mem equation found)
        then equation :: found else found in
    reconstruction_equations rest found

let rec add_definitions (defs more:list D.definition)
  : Tot (option (list D.definition)) (decreases more) =
  match more with
  | [] -> Some defs
  | d :: rest -> D.add_definition defs d >>= (fun next -> add_definitions next rest)

let document_definitions (doc:document) : option (list D.definition) =
  collect_definitions [] (axiom_branches doc.entries) doc.entries >>= (fun defs ->
  let equations = reconstruction_equations doc.entries [] in
  let inputs = Z3List.append doc.assertions (Z3List.map (fun d -> d.D.body) defs) in
  let bounded (e:expr) = Some? (expression_budget 65536 e) in
  // Avoid expanding heavily shared DAGs into unbounded trees.
  if equations = [] || not (Z3List.for_all bounded inputs &&
                           Z3List.for_all (fun e -> bounded e.formula) doc.entries)
  then Some defs else
  match BF.check_context inputs equations with
  | None -> Some defs
  | Some rs ->
    // Eliminate fresh bits throughout the proof; their reconstructions must still replay.
    match add_definitions defs (BF.projection_definitions rs) with
    | Some expanded -> Some expanded
    | None -> Some defs)

let expand_rule (defs:list D.definition) (kind:rule) : option rule =
  if defs = [] then Some kind
  else match kind with
  | QuantifierIntroduction certificate ->
    opt_map_tail (fun e ->
      D.expand (L.length defs) defs e.binder_formula >>= (fun formula ->
      Some { e with binder_formula = formula })) certificate.binder_entries >>= (fun entries ->
    Some (QuantifierIntroduction { certificate with binder_entries = entries }))
  | _ -> Some kind

let rec expand_binder_entries_using (transform:D.expander) (defs:list D.definition)
                                   (entries:list binder_entry)
  : Tot (result:option (list binder_entry){result ==
      opt_map (fun e ->
        D.expand (L.length defs) defs e.binder_formula >>= (fun formula ->
        Some { e with binder_formula = formula })) entries})
        (decreases entries) =
  match entries with
  | [] -> Some []
  | e :: rest ->
    let expanded = transform (L.length defs) defs e.binder_formula >>= (fun formula ->
      Some { e with binder_formula = formula }) in
    assert (expanded == (D.expand (L.length defs) defs e.binder_formula >>= (fun formula ->
      Some { e with binder_formula = formula })));
    let remaining = expand_binder_entries_using transform defs rest in
    assert (remaining == opt_map (fun e ->
      D.expand (L.length defs) defs e.binder_formula >>= (fun formula ->
      Some { e with binder_formula = formula })) rest);
    match expanded, remaining with
    | Some e', Some rest' -> Some (e' :: rest')
    | _, _ -> None

let expand_rule_using (transform:D.expander) (defs:list D.definition) (kind:rule)
  : result:option rule{result == expand_rule defs kind} =
  if defs = [] then Some kind
  else match kind with
  | QuantifierIntroduction certificate ->
    expand_binder_entries_using transform defs certificate.binder_entries >>= (fun entries ->
    Some (QuantifierIntroduction { certificate with binder_entries = entries }))
  | _ -> Some kind

let collect_skolem_formula (skolems:list SK.definition) (formula:expr)
  : option (list SK.definition) =
  match is_oeq formula with
  | Some (a, b) ->
    (match SK.definition_of a b with Some d -> SK.add_definition skolems d | None -> Some skolems)
  | None -> Some skolems

let rec collect_binder_skolems (skolems:list SK.definition) (entries:list binder_entry)
  : Tot (option (list SK.definition)) (decreases entries) =
  match entries with
  | [] -> Some skolems
  | e :: rest ->
    (if e.binder_name = "sk" then collect_skolem_formula skolems e.binder_formula
     else Some skolems) >>= (fun more -> collect_binder_skolems more rest)

let rec collect_skolems (defs:list D.definition) (skolems:list SK.definition) (entries:list entry)
  : Tot (option (list SK.definition)) (decreases entries) =
  match entries with
  | [] -> Some skolems
  | e :: rest ->
    (match e.rule with
     | Skolemization ->
       D.expand (L.length defs) defs e.formula >>= (collect_skolem_formula skolems)
     | QuantifierIntroduction _ ->
       expand_rule defs e.rule >>= (fun kind ->
       match kind with
       | QuantifierIntroduction certificate -> collect_binder_skolems skolems certificate.binder_entries
       | _ -> None)
     | _ -> Some skolems) >>= (fun more -> collect_skolems defs more rest)

let rec collect_skolems_using (transform:D.expander) (defs:list D.definition)
                             (skolems:list SK.definition) (entries:list entry)
  : Tot (result:option (list SK.definition){result == collect_skolems defs skolems entries})
        (decreases entries) =
  match entries with
  | [] -> Some skolems
  | e :: rest ->
    (match e.rule with
     | Skolemization ->
       transform (L.length defs) defs e.formula >>= (collect_skolem_formula skolems)
     | QuantifierIntroduction _ ->
       expand_rule_using transform defs e.rule >>= (fun kind ->
       match kind with
       | QuantifierIntroduction certificate -> collect_binder_skolems skolems certificate.binder_entries
       | _ -> None)
     | _ -> Some skolems) >>= (fun more -> collect_skolems_using transform defs more rest)

type input_lookup =
  assertions:list judgment ->
  Tot (contains:(judgment -> bool){forall (query:judgment).
    contains query == L.mem query assertions})

let linear_lookup : input_lookup =
  fun assertions -> fun query -> L.mem query assertions

let indexed_lookup (hash:judgment -> nat) : input_lookup =
  fun assertions ->
  if L.length assertions <= 16 then linear_lookup assertions
  else let index = S.of_list hash assertions in
  fun query -> S.member hash query index

let rec enough_asserted (remaining:nat) (entries:list entry) : Tot bool (decreases entries) =
  if remaining = 0 then true
  else match entries with
  | [] -> false
  | e :: rest -> enough_asserted (if e.rule = Asserted then remaining - 1 else remaining) rest

let document_lookup (hash:judgment -> nat) (doc:document) : input_lookup =
  if enough_asserted 17 doc.entries then indexed_lookup hash else linear_lookup

(* The proof-id -> fact cache.  The specification ([check_document] and the
   functions it calls) keeps the transparent [index_tree], so that tests can
   evaluate it by normalization.  The executable path ([check_document_using],
   [diagnose_document_using]) uses the abstract [Z3IdTable.t], an immutable array
   under Cherry; [agrees] relates the two. *)
let agrees (#a:Type0) (tbl:IT.t a) (tree:index_tree a) : prop =
  forall (key:int). IT.find tbl key == index_find tree key

let lemma_agrees_empty (#a:Type0) : Lemma (agrees (IT.empty #a) Empty) = ()

let lemma_agrees_put (#a:Type0) (tbl:IT.t a) (tree:index_tree a) (key:nat) (value:a)
  : Lemma (requires agrees tbl tree) (ensures agrees (IT.put tbl key value) (index_put tree key value)) =
  let at (query:int) : Lemma (IT.find (IT.put tbl key value) query == index_find (index_put tree key value) query) =
    if query >= 0 then lemma_index_put tree key value query in
  FStar.Classical.forall_intro at

let rec lemma_agrees_opt_map (#a:Type0) (tbl:IT.t a) (tree:index_tree a) (ids:list int)
  : Lemma (requires agrees tbl tree)
          (ensures opt_map (IT.find tbl) ids == opt_map (index_find tree) ids) (decreases ids) =
  match ids with [] -> () | _ :: rest -> lemma_agrees_opt_map tbl tree rest

let prepare_entry_from (transform:D.expander) (bound:bool) (defs:list D.definition)
                       (premises:option (list checked_fact)) (e:entry) : option proof_node =
  if bound && not (D.scoped [] e.formula) then None else
  (if defs = [] then Some e.formula else transform (L.length defs) defs e.formula) >>= (fun formula ->
  if bound && not (D.scoped [] formula) then None else
  classify_fact formula >>= (fun concl ->
  premises >>= (fun premises ->
  expand_rule_using transform defs e.rule >>= (fun kind ->
  Some { kind = kind; conclusion = concl; premises = premises }))))

let prepare_entry_using (transform:D.expander) (bound:bool) (defs:list D.definition)
                  (prev:IT.t checked_fact) (e:entry) : option proof_node =
  prepare_entry_from transform bound defs (opt_map_tail (IT.find prev) e.premise_ids) e

let prepare_entry_table (bound:bool) (defs:list D.definition)
                        (prev:IT.t checked_fact) (e:entry) : option proof_node =
  prepare_entry_using D.linear_expander bound defs prev e

let prepare_entry (bound:bool) (defs:list D.definition)
                  (prev:index_tree checked_fact) (e:entry) : option proof_node =
  prepare_entry_from D.linear_expander bound defs (opt_map_tail (index_find prev) e.premise_ids) e

let lemma_prepare_entry_using (transform:D.expander) (bound:bool) (defs:list D.definition)
                             (prev:IT.t checked_fact) (e:entry)
  : Lemma (prepare_entry_using transform bound defs prev e == prepare_entry_table bound defs prev e)
  = ()

let lemma_prepare_entry_table (bound:bool) (defs:list D.definition)
                              (prev:IT.t checked_fact) (tree:index_tree checked_fact) (e:entry)
  : Lemma (requires agrees prev tree)
          (ensures prepare_entry_table bound defs prev e == prepare_entry bound defs tree e)
  = lemma_agrees_opt_map prev tree e.premise_ids

let prepare_skolem_context (defs:list D.definition) (original expanded:list expr) (entries:list entry)
  : option (list SK.definition) =
  collect_skolems defs [] entries >>= (fun choices ->
  SK.order_context (L.length choices) choices >>= (fun skolems ->
  if not (SK.fresh_inputs skolems original && SK.fresh_inputs skolems expanded) then None
  else Some skolems))

let prepare_skolem_context_using (transform:D.expander) (defs:list D.definition)
                                 (original expanded:list expr) (entries:list entry)
  : result:option (list SK.definition){
      result == prepare_skolem_context defs original expanded entries} =
  collect_skolems_using transform defs [] entries >>= (fun choices ->
  SK.order_context (L.length choices) choices >>= (fun skolems ->
  if not (SK.fresh_inputs skolems original && SK.fresh_inputs skolems expanded) then None
  else Some skolems))

let prepare_document_inputs_using (transform:D.expander) (doc:document)
  : option (bool & list D.definition & list judgment & list expr) =
  let bound = not (ground_exprs doc.expressions) in
  if not (logical_decls doc.declarations) ||
     (bound && not (well_formed_exprs doc.expressions)) ||
     not (ordinary_facts doc.assertions) ||
     (bound && not (scoped_assertions doc.assertions)) then None else
  document_definitions doc >>= (fun defs ->
  if not (D.acyclic_using transform (L.length defs) defs defs) then None else
  (if defs = [] then Some doc.assertions
   else D.expand_list_using transform (L.length defs) defs doc.assertions) >>= (fun expanded ->
  opt_map_tail classify_fact expanded >>= (fun inputs ->
  Some (bound, defs, inputs, expanded))))

let prepare_document_inputs (doc:document) : option (bool & list D.definition & list judgment & list expr) =
  prepare_document_inputs_using D.linear_expander doc

let lemma_prepare_document_inputs_using (transform:D.expander) (doc:document)
  : Lemma (prepare_document_inputs_using transform doc == prepare_document_inputs doc)
  = ()

let prepare_document_using (transform:D.expander) (doc:document)
  : option (bool & list D.definition & list judgment & list SK.definition) =
  prepare_document_inputs_using transform doc >>= (fun (bound, defs, inputs, expanded) ->
  prepare_skolem_context_using transform defs doc.assertions expanded doc.entries >>= (fun skolems ->
  Some (bound, defs, inputs, skolems)))

let prepare_document (doc:document) : option (bool & list D.definition & list judgment & list SK.definition) =
  prepare_document_using D.linear_expander doc

let lemma_prepare_document_using (transform:D.expander) (doc:document)
  : Lemma (prepare_document_using transform doc == prepare_document doc)
  = lemma_prepare_document_inputs_using transform doc;
    match prepare_document_inputs doc with
    | None -> ()
    | Some (_, defs, _, expanded) ->
      assert (prepare_skolem_context_using transform defs doc.assertions expanded doc.entries ==
              prepare_skolem_context_using D.linear_expander defs doc.assertions expanded doc.entries)

noeq
type entries_diagnostic =
  | EntriesChecked : cache:IT.t checked_fact -> pending:nat ->
                     obligations:list unmet_obligation -> entries_diagnostic
  | EntriesRejected : reason:document_diagnostic -> entries_diagnostic

let entries_agree (r:option (IT.t checked_fact & nat)) (s:option (index_tree checked_fact & nat)) : prop =
  match r, s with
  | None, None -> True
  | Some (tbl, n), Some (tree, m) -> n == m /\ agrees tbl tree
  | _, _ -> False

