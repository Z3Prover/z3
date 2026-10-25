module Z3ProofDocument

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3UnifiedProof
open Z3ProofIndex
module D = Z3Definitions
module SK = Z3Skolemization
module S = Z3ProofSet
module L = FStar.List.Tot

type entry = {
  rule: rule;
  formula: expr;
  premise_ids: list int;
}

type document = {
  declarations: list func_decl;
  expressions: list expr;
  assertions: list expr;
  entries: list entry;
  root: int;
}

let rule_of_name (name:string) : option rule =
  if name = "asserted" then Some Asserted
  else if name = "def-axiom" then Some DefAxiom
  else if name = "intro-def" then Some DefinitionIntroduction
  else if name = "apply-def" then Some ApplyDefinition
  else if name = "hypothesis" then Some Hypothesis
  else if name = "lemma" then Some LemmaRule
  else basic_rule_of_name name

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

let expand_rule (defs:list D.definition) (kind:rule) : option rule =
  if defs = [] then Some kind
  else match kind with
  | QuantifierIntroduction certificate ->
    opt_map (fun e ->
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

let prepare_entry_using (transform:D.expander) (bound:bool) (defs:list D.definition)
                  (prev:index_tree checked_fact) (e:entry) : option proof_node =
  if bound && not (D.scoped [] e.formula) then None else
  (if defs = [] then Some e.formula else transform (L.length defs) defs e.formula) >>= (fun formula ->
  if bound && not (D.scoped [] formula) then None else
  classify_fact formula >>= (fun concl ->
  opt_map (index_find prev) e.premise_ids >>= (fun premises ->
  expand_rule_using transform defs e.rule >>= (fun kind ->
  Some { kind = kind; conclusion = concl; premises = premises }))))

let prepare_entry (bound:bool) (defs:list D.definition)
                  (prev:index_tree checked_fact) (e:entry) : option proof_node =
  prepare_entry_using D.linear_expander bound defs prev e

let lemma_prepare_entry_using (transform:D.expander) (bound:bool) (defs:list D.definition)
                             (prev:index_tree checked_fact) (e:entry)
  : Lemma (prepare_entry_using transform bound defs prev e == prepare_entry bound defs prev e)
  = ()

let check_entry_with_lookup (skolems:list SK.definition) (strict bound:bool)
                           (defs:list D.definition) (assertions:list judgment) (contains:judgment -> bool)
                           (prev:index_tree checked_fact) (e:entry)
  : option (checked_fact & nat) =
  prepare_entry bound defs prev e >>= check_node_with_membership skolems strict assertions contains

let check_entry_with_context (skolems:list SK.definition)
                            (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                            (prev:index_tree checked_fact) (e:entry)
  : option (checked_fact & nat) =
  check_entry_with_lookup skolems strict bound defs assertions (linear_lookup assertions) prev e

let check_entry (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                (prev:index_tree checked_fact) (e:entry)
  : option (checked_fact & nat) =
  check_entry_with_context [] strict bound defs assertions prev e

let rec check_entries_with_lookup (skolems:list SK.definition) (strict bound:bool)
                                 (defs:list D.definition) (assertions:list judgment) (contains:judgment -> bool)
                      (acc:index_tree checked_fact) (next trusted:nat) (entries:list entry)
  : Tot (option (index_tree checked_fact & nat)) (decreases entries) =
  match entries with
  | [] -> Some (acc, trusted)
  | e :: rest ->
    check_entry_with_lookup skolems strict bound defs assertions contains acc e >>= (fun nt ->
    check_entries_with_lookup skolems strict bound defs assertions contains (index_put acc next (fst nt))
                  (next + 1) (trusted + snd nt) rest)

let check_entries (skolems:list SK.definition) (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                  (acc:index_tree checked_fact) (next trusted:nat) (entries:list entry)
  : option (index_tree checked_fact & nat) =
  check_entries_with_lookup skolems strict bound defs assertions (linear_lookup assertions) acc next trusted entries

type entry_checker =
  skolems:list SK.definition -> strict:bool -> bound:bool -> defs:list D.definition ->
  assertions:list judgment -> contains:(judgment -> bool) ->
  prev:index_tree checked_fact -> e:entry ->
  Tot (result:option (checked_fact & nat){
    result == check_entry_with_lookup skolems strict bound defs assertions contains prev e})

let checker_using (transform:D.expander) : entry_checker =
  fun skolems strict bound defs assertions contains prev e ->
    lemma_prepare_entry_using transform bound defs prev e;
    prepare_entry_using transform bound defs prev e >>= check_node_with_membership skolems strict assertions contains

let rec check_entries_using (check:entry_checker) (skolems:list SK.definition)
                           (strict bound:bool) (defs:list D.definition)
                           (assertions:list judgment) (contains:judgment -> bool) (acc:index_tree checked_fact)
                           (next trusted:nat) (entries:list entry)
  : Tot (result:option (index_tree checked_fact & nat){
      result == check_entries_with_lookup skolems strict bound defs assertions contains acc next trusted entries})
        (decreases entries) =
  match entries with
  | [] -> Some (acc, trusted)
  | e :: rest ->
    check skolems strict bound defs assertions contains acc e >>= (fun nt ->
    check_entries_using check skolems strict bound defs assertions contains (index_put acc next (fst nt))
      (next + 1) (trusted + snd nt) rest)

let lemma_check_entry_lookup (skolems:list SK.definition) (strict bound:bool) (defs:list D.definition)
                             (assertions:list judgment) (contains:judgment -> bool)
                             (prev:index_tree checked_fact) (e:entry)
  : Lemma (requires (forall (query:judgment). contains query == L.mem query assertions))
          (ensures check_entry_with_lookup skolems strict bound defs assertions contains prev e ==
                   check_entry_with_context skolems strict bound defs assertions prev e)
  = match prepare_entry bound defs prev e with
    | None -> ()
    | Some node -> lemma_check_node_membership skolems strict assertions contains node

let rec lemma_check_entries_lookup (skolems:list SK.definition) (strict bound:bool) (defs:list D.definition)
                                   (assertions:list judgment) (contains:judgment -> bool)
                                   (acc:index_tree checked_fact) (next trusted:nat) (entries:list entry)
  : Lemma (requires (forall (query:judgment). contains query == L.mem query assertions))
          (ensures check_entries_with_lookup skolems strict bound defs assertions contains acc next trusted entries ==
                   check_entries skolems strict bound defs assertions acc next trusted entries)
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      lemma_check_entry_lookup skolems strict bound defs assertions contains acc e;
      (match check_entry_with_context skolems strict bound defs assertions acc e with
       | None -> ()
       | Some (fact, local) ->
         lemma_check_entries_lookup skolems strict bound defs assertions contains (index_put acc next fact)
           (next + 1) (trusted + local) rest)

let rec ground_exprs (exprs:list expr) : Tot bool (decreases exprs) =
  match exprs with
  | [] -> true
  | App f args :: rest ->
    sorts_match args f.domain && ordinary_facts args && ground_exprs rest
  | _ -> false

let rec well_formed_exprs (exprs:list expr) : Tot bool (decreases exprs) =
  match exprs with
  | [] -> true
  | App f args :: rest ->
    sorts_match args f.domain && ordinary_facts args && well_formed_exprs rest
  | Quantifier k bs s b :: rest ->
    s = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort) &&
    ordinary_facts [b] && well_formed_exprs rest
  | Var _ _ :: rest -> well_formed_exprs rest

let rec scoped_assertions (assertions:list expr) : Tot bool (decreases assertions) =
  match assertions with
  | [] -> true
  | a :: rest -> D.scoped [] a && scoped_assertions rest

let rec boolean_domains (dom:list sort) : Tot bool (decreases dom) =
  match dom with
  | [] -> true
  | s :: rest -> s = bool_sort && boolean_domains rest

let logical_decl (f:func_decl) : bool =
  if f.decl_name = "not" then
    f.interp = Some op_not && f.domain = [bool_sort] && f.range = bool_sort
  else if f.decl_name = "and" || f.decl_name = "or" then
    f.interp = Some (if f.decl_name = "and" then op_and else op_or) &&
    boolean_domains f.domain && f.range = bool_sort
  else if f.decl_name = "implies" || f.decl_name = "=>" then
    f.interp = Some op_implies && f.domain = [bool_sort; bool_sort] && f.range = bool_sort
  else if f.decl_name = "=" then
    (match f.domain with
     | [s; t] -> s = t && f.interp = Some op_eq && f.range = bool_sort
     | _ -> false)
  else if f.decl_name = "xor" then f = Z3BooleanRewrite.boolean_xor_decl
  else if f.decl_name = "distinct" then Z3DistinctAst.distinct_declaration f
  else if f.decl_name = "~" then
    (match f.domain with
     | [s; t] -> s = t && f = typed_oeq_decl s
     | _ -> false)
  else if f.interp = Some op_oeq then false
  else if f.decl_name = "true" || f.decl_name = "false" then
    f.interp = Some (if f.decl_name = "true" then op_true else op_false) &&
    f.domain = [] && f.range = bool_sort
  else true

let rec logical_decls (decls:list func_decl) : Tot bool (decreases decls) =
  match decls with
  | [] -> true
  | d :: rest -> logical_decl d && logical_decls rest

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
  collect_definitions [] (axiom_branches doc.entries) doc.entries >>= (fun defs ->
  if not (D.acyclic_using transform (L.length defs) defs defs) then None else
  (if defs = [] then Some doc.assertions
   else D.expand_list_using transform (L.length defs) defs doc.assertions) >>= (fun expanded ->
  opt_map classify_fact expanded >>= (fun inputs ->
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

let finish_document (doc:document) (defs:list D.definition) (result:index_tree checked_fact & nat)
  : option nat =
  index_find (fst result) doc.root >>= (fun node ->
  if false_judgment node.conclusion && node.hypotheses = [] &&
     D.check_fresh_inputs defs doc.assertions
  then Some (snd result) else None)

let check_document_with_lookup (lookup:input_lookup) (doc:document) : option nat =
  prepare_document doc >>= (fun (bound, defs, inputs, skolems) ->
  check_entries_with_lookup skolems true bound defs inputs (lookup inputs) Empty 0 0 doc.entries >>=
  finish_document doc defs)

let check_document (doc:document) : option nat =
  check_document_with_lookup linear_lookup doc

let check_document_using (transform:D.expander) (lookup:input_lookup) (doc:document)
  : result:option nat{result == check_document_with_lookup lookup doc} =
  lemma_prepare_document_using transform doc;
  prepare_document_using transform doc >>= (fun (bound, defs, inputs, skolems) ->
  check_entries_using (checker_using transform) skolems true bound defs inputs (lookup inputs)
    Empty 0 0 doc.entries >>= finish_document doc defs)

let check_document_indexed (hash:judgment -> nat) (doc:document) : option nat =
  check_document_using (D.memoized_expander (fun (_, e) -> hash (Holds e)))
    (document_lookup hash doc) doc

let lemma_check_document_lookup (lookup:input_lookup) (doc:document)
  : Lemma (check_document_with_lookup lookup doc == check_document doc)
  = match prepare_document doc with
    | None -> ()
    | Some (bound, defs, inputs, skolems) ->
      lemma_check_entries_lookup skolems true bound defs inputs (lookup inputs) Empty 0 0 doc.entries

let lemma_check_document_indexed (hash:judgment -> nat) (doc:document)
  : Lemma (check_document_indexed hash doc == check_document doc)
  = lemma_check_document_lookup (document_lookup hash doc) doc

type diagnostic_stage =
  | LogicalDeclarations
  | ExpressionWellFormedness
  | OriginalAssertions
  | AssertionScope
  | DefinitionCollection
  | DefinitionCycle
  | DefinitionExpansion
  | SkolemCollection
  | SkolemCycle
  | SkolemFreshness
  | InputClassification
  | ProofEntry
  | MissingPremise
  | MissingRoot
  | OpenRoot
  | DefinitionFreshness

type unmet_obligation = {
  obligation_index: nat;
  obligation_rule: rule;
  obligation_conclusion: judgment;
  obligation_premises: list judgment;
  obligation_source: expr;
  obligation_count: nat;
}

type document_diagnostic =
  | DocumentChecked : pending:nat -> obligations:list unmet_obligation -> document_diagnostic
  | DocumentRejected : stage:diagnostic_stage -> index:option nat ->
                       source:option expr -> document_diagnostic

noeq
type entries_diagnostic =
  | EntriesChecked : cache:index_tree checked_fact -> pending:nat ->
                     obligations:list unmet_obligation -> entries_diagnostic
  | EntriesRejected : reason:document_diagnostic -> entries_diagnostic

let rec diagnose_entries_using (check:entry_checker) (skolems:list SK.definition)
                               (bound:bool) (defs:list D.definition)
                               (inputs:list judgment) (contains:judgment -> bool)
                         (cache:index_tree checked_fact) (next pending:nat)
                         (unmet:list unmet_obligation) (entries:list entry)
  : Tot entries_diagnostic (decreases entries) =
  match entries with
  | [] -> EntriesChecked cache pending (L.rev unmet)
  | e :: rest ->
    match check skolems true bound defs inputs contains cache e with
    | None -> EntriesRejected (DocumentRejected ProofEntry (Some next) (Some e.formula))
    | Some (fact, local) ->
      let cache' = index_put cache next fact in
      if local = 0 then diagnose_entries_using check skolems bound defs inputs contains cache' (next + 1) pending unmet rest
      else
        match opt_map (index_find cache) e.premise_ids with
        | None -> EntriesRejected (DocumentRejected MissingPremise (Some next) (Some e.formula))
        | Some premises ->
          let obligation = {
            obligation_index = next; obligation_rule = e.rule;
            obligation_conclusion = fact.conclusion;
            obligation_premises = premise_judgments premises;
            obligation_source = e.formula; obligation_count = local;
          } in
          diagnose_entries_using check skolems bound defs inputs contains cache' (next + 1) (pending + local)
                           (obligation :: unmet) rest

let diagnose_entries_with_lookup (skolems:list SK.definition)
                         (bound:bool) (defs:list D.definition)
                         (inputs:list judgment) (contains:judgment -> bool)
                         (cache:index_tree checked_fact) (next pending:nat)
                         (unmet:list unmet_obligation) (entries:list entry) : entries_diagnostic =
  diagnose_entries_using (checker_using D.linear_expander) skolems bound defs inputs contains
    cache next pending unmet entries

let diagnose_entries (skolems:list SK.definition) (bound:bool) (defs:list D.definition) (inputs:list judgment)
                     (cache:index_tree checked_fact) (next pending:nat)
                     (unmet:list unmet_obligation) (entries:list entry) : entries_diagnostic =
  diagnose_entries_with_lookup skolems bound defs inputs (linear_lookup inputs) cache next pending unmet entries

let diagnose_prepared_document_using (transform:D.expander) (lookup:input_lookup) (doc:document)
                                    (bound:bool) (defs:list D.definition)
                                    (inputs:list judgment) (skolems:list SK.definition) : document_diagnostic =
  match diagnose_entries_using (checker_using transform) skolems bound defs inputs
          (lookup inputs) Empty 0 0 [] doc.entries with
  | EntriesRejected reason -> reason
  | EntriesChecked cache pending unmet ->
    match index_find cache doc.root with
    | None -> DocumentRejected MissingRoot None None
    | Some node ->
      if not (false_judgment node.conclusion && node.hypotheses = [])
      then DocumentRejected OpenRoot None None
      else if not (D.check_fresh_inputs defs doc.assertions)
      then DocumentRejected DefinitionFreshness None None
      else DocumentChecked pending unmet

let diagnose_document_inputs_using (transform:D.expander) (lookup:input_lookup) (doc:document)
                                   (bound:bool) (defs:list D.definition) (expanded:list expr)
                                   (inputs:list judgment) : document_diagnostic =
  match collect_skolems_using transform defs [] doc.entries with
  | None -> DocumentRejected SkolemCollection None None
  | Some choices ->
    match SK.order_context (L.length choices) choices with
    | None -> DocumentRejected SkolemCycle None None
    | Some skolems ->
      if not (SK.fresh_inputs skolems doc.assertions && SK.fresh_inputs skolems expanded)
      then DocumentRejected SkolemFreshness None None
      else diagnose_prepared_document_using transform lookup doc bound defs inputs skolems

let diagnose_document_definitions_using (transform:D.expander) (lookup:input_lookup) (doc:document)
                                        (bound:bool) (defs:list D.definition) : document_diagnostic =
  if not (D.acyclic_using transform (L.length defs) defs defs)
  then DocumentRejected DefinitionCycle None None
  else
    match (if defs = [] then Some doc.assertions
           else D.expand_list_using transform (L.length defs) defs doc.assertions) with
    | None -> DocumentRejected DefinitionExpansion None None
    | Some expanded ->
      match opt_map classify_fact expanded with
      | None -> DocumentRejected InputClassification None None
      | Some inputs -> diagnose_document_inputs_using transform lookup doc bound defs expanded inputs

let diagnose_document_using (transform:D.expander) (lookup:input_lookup) (doc:document) : document_diagnostic =
  let bound = not (ground_exprs doc.expressions) in
  let reject stage = DocumentRejected stage None None in
  if not (logical_decls doc.declarations) then reject LogicalDeclarations
  else if bound && not (well_formed_exprs doc.expressions) then reject ExpressionWellFormedness
  else if not (ordinary_facts doc.assertions) then reject OriginalAssertions
  else if bound && not (scoped_assertions doc.assertions) then reject AssertionScope
  else
    match collect_definitions [] (axiom_branches doc.entries) doc.entries with
    | None -> reject DefinitionCollection
    | Some defs -> diagnose_document_definitions_using transform lookup doc bound defs

let diagnose_document_with_lookup (lookup:input_lookup) (doc:document) : document_diagnostic =
  diagnose_document_using D.linear_expander lookup doc

let diagnose_document (doc:document) : document_diagnostic =
  diagnose_document_with_lookup linear_lookup doc

let diagnose_document_indexed (hash:judgment -> nat) (doc:document) : document_diagnostic =
  diagnose_document_using (D.memoized_expander (fun (_, e) -> hash (Holds e)))
    (document_lookup hash doc) doc
