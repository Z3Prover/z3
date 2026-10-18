module Z3ProofDocument

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3UnifiedProof
open Z3ProofIndex
module D = Z3Definitions
module SK = Z3Skolemization
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

let rec axiom_branches (entries:list entry) : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    let branches = axiom_branches rest in
    if e.rule = DefAxiom && D.axiom_branch e.formula && not (D.tautology 128 e.formula)
    then e.formula :: branches else branches

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

let check_entry_with_context (skolems:list SK.definition)
                            (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                (prev:index_tree checked_fact) (e:entry)
  : option (checked_fact & nat) =
  if bound && not (D.scoped [] e.formula) then None else
  (if defs = [] then Some e.formula else D.expand (L.length defs) defs e.formula) >>= (fun formula ->
  if bound && not (D.scoped [] formula) then None else
  classify_fact formula >>= (fun concl ->
  opt_map (index_find prev) e.premise_ids >>= (fun premises ->
  expand_rule defs e.rule >>= (fun kind ->
  check_node_with_context skolems strict assertions
    { kind = kind; conclusion = concl; premises = premises }))))

let check_entry (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                (prev:index_tree checked_fact) (e:entry) : option (checked_fact & nat) =
  check_entry_with_context [] strict bound defs assertions prev e

let rec check_entries (skolems:list SK.definition)
                      (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                      (acc:index_tree checked_fact) (next trusted:nat) (entries:list entry)
  : Tot (option (index_tree checked_fact & nat)) (decreases entries) =
  match entries with
  | [] -> Some (acc, trusted)
  | e :: rest ->
    check_entry_with_context skolems strict bound defs assertions acc e >>= (fun nt ->
    check_entries skolems strict bound defs assertions (index_put acc next (fst nt))
                  (next + 1) (trusted + snd nt) rest)

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

let check_document (doc:document) : option nat =
  let bound = not (ground_exprs doc.expressions) in
  if not (logical_decls doc.declarations) ||
     (bound && not (well_formed_exprs doc.expressions)) ||
     not (ordinary_facts doc.assertions) ||
     (bound && not (scoped_assertions doc.assertions)) then None else
  collect_definitions [] (axiom_branches doc.entries) doc.entries >>= (fun defs ->
  if not (D.acyclic (L.length defs) defs defs) then None else
  (if defs = [] then Some doc.assertions else D.expand_args (L.length defs) defs doc.assertions) >>= (fun expanded ->
  opt_map classify_fact expanded >>= (fun inputs ->
  collect_skolems defs [] doc.entries >>= (fun choices ->
  SK.order_context (L.length choices) choices >>= (fun skolems ->
  if not (SK.fresh_inputs skolems doc.assertions && SK.fresh_inputs skolems expanded) then None else
  check_entries skolems true bound defs inputs Empty 0 0 doc.entries >>= (fun result ->
  index_find (fst result) doc.root >>= (fun node ->
  if false_judgment node.conclusion && node.hypotheses = [] &&
     D.check_fresh_inputs defs doc.assertions
  then Some (snd result) else None)))))))

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

let rec diagnose_entries (skolems:list SK.definition)
                         (bound:bool) (defs:list D.definition) (inputs:list judgment)
                         (cache:index_tree checked_fact) (next pending:nat)
                         (unmet:list unmet_obligation) (entries:list entry)
  : Tot entries_diagnostic (decreases entries) =
  match entries with
  | [] -> EntriesChecked cache pending (L.rev unmet)
  | e :: rest ->
    match check_entry_with_context skolems true bound defs inputs cache e with
    | None -> EntriesRejected (DocumentRejected ProofEntry (Some next) (Some e.formula))
    | Some (fact, local) ->
      let cache' = index_put cache next fact in
      if local = 0 then diagnose_entries skolems bound defs inputs cache' (next + 1) pending unmet rest
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
          diagnose_entries skolems bound defs inputs cache' (next + 1) (pending + local)
                           (obligation :: unmet) rest

let diagnose_document (doc:document) : document_diagnostic =
  let bound = not (ground_exprs doc.expressions) in
  let reject stage = DocumentRejected stage None None in
  if not (logical_decls doc.declarations) then reject LogicalDeclarations
  else if bound && not (well_formed_exprs doc.expressions) then reject ExpressionWellFormedness
  else if not (ordinary_facts doc.assertions) then reject OriginalAssertions
  else if bound && not (scoped_assertions doc.assertions) then reject AssertionScope
  else
    match collect_definitions [] (axiom_branches doc.entries) doc.entries with
    | None -> reject DefinitionCollection
    | Some defs ->
      if not (D.acyclic (L.length defs) defs defs) then reject DefinitionCycle
      else
        match (if defs = [] then Some doc.assertions
               else D.expand_args (L.length defs) defs doc.assertions) with
        | None -> reject DefinitionExpansion
        | Some expanded ->
          match opt_map classify_fact expanded with
          | None -> reject InputClassification
          | Some inputs ->
            match collect_skolems defs [] doc.entries with
            | None -> reject SkolemCollection
            | Some choices ->
              match SK.order_context (L.length choices) choices with
              | None -> reject SkolemCycle
              | Some skolems ->
                if not (SK.fresh_inputs skolems doc.assertions && SK.fresh_inputs skolems expanded)
                then reject SkolemFreshness
                else match diagnose_entries skolems bound defs inputs Empty 0 0 [] doc.entries with
                | EntriesRejected reason -> reason
                | EntriesChecked cache pending unmet ->
                  match index_find cache doc.root with
                  | None -> reject MissingRoot
                  | Some node ->
                    if not (false_judgment node.conclusion && node.hypotheses = []) then reject OpenRoot
                    else if not (D.check_fresh_inputs defs doc.assertions) then reject DefinitionFreshness
                    else DocumentChecked pending unmet
