module Z3DocumentSyntax

open Z3AstTheory
open Z3OperatorTags
open Z3ObservationalSyntax
open Z3UnifiedProofSyntax
module D = Z3DefinitionRecognition

type entry = {
  rule: rule;
  formula: expr;
  premise_ids: list int;
}

[@@FStar.Attributes.cherry_boxed]
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
  else if f.decl_name = "xor" then f = Z3BooleanSyntax.boolean_xor_decl
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

