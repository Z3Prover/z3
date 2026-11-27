module Z3DefinitionScope

open Z3AstTheory
open FStar.List.Tot
module Def = Z3DefinitionRecognition
module P = Z3DocumentPreparation
module U = Z3UnifiedProofSyntax
module BF = Z3BvFreshSyntax

include Z3BvFreshScope

let rec lemma_collect_constructed (defs result:list Def.definition)
                                  (branches:list expr) (entries:list P.entry)
  : Lemma (requires constructed_definitions defs /\
                    P.collect_definitions defs branches entries == Some result)
          (ensures constructed_definitions result)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    if e.P.rule <> U.DefinitionIntroduction && e.P.rule <> U.DefAxiom then
      lemma_collect_constructed defs result branches rest
    else if Cons? e.P.premise_ids || not (Def.scoped [] e.P.formula) then ()
    else (
      let candidate =
        if e.P.rule = U.DefinitionIntroduction then Def.definition_of e.P.formula
        else Def.axiom_definition e.P.formula branches in
      match candidate with
      | None -> if e.P.rule <> U.DefinitionIntroduction then
                  lemma_collect_constructed defs result branches rest
      | Some d ->
        if e.P.rule = U.DefinitionIntroduction then lemma_definition_constructed e.P.formula d
        else lemma_axiom_constructed e.P.formula branches d;
        (match Def.add_definition defs d with
         | Some next ->
           lemma_add_constructed defs d next;
           lemma_collect_constructed next result branches rest
         | None -> ()))

let rec lemma_add_definitions_constructed
    (defs more result:list Def.definition)
  : Lemma (requires constructed_definitions defs /\ constructed_definitions more /\
                    P.add_definitions defs more == Some result)
          (ensures constructed_definitions result)
          (decreases more) =
  match more with
  | [] -> ()
  | d :: rest ->
    (match Def.add_definition defs d with
     | None -> ()
     | Some next ->
       lemma_add_constructed defs d next;
       lemma_add_definitions_constructed next rest result)

let lemma_document_shape (doc:P.document) (collected:list Def.definition)
  : Lemma (requires P.collect_definitions [] (P.axiom_branches doc.P.entries) doc.P.entries == Some collected)
          (ensures P.document_definitions doc ==
            (let equations = P.reconstruction_equations doc.P.entries [] in
             let inputs = Z3List.append doc.P.assertions (Z3List.map (fun d -> d.Def.body) collected) in
             if equations == [] || not (Z3List.for_all (fun e -> Some? (expression_budget 65536 e)) inputs &&
                                       Z3List.for_all (fun e -> Some? (expression_budget 65536 e.P.formula)) doc.P.entries)
             then Some collected else
             match BF.check_context inputs equations with
             | None -> Some collected
             | Some rs ->
               match P.add_definitions collected (BF.projection_definitions rs) with
               | Some expanded -> Some expanded
               | None -> Some collected)) =
  ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_document_definitions (doc:P.document) (defs:list Def.definition)
  : Lemma (requires P.document_definitions doc == Some defs)
          (ensures constructed_definitions defs /\ definition_scopes defs) =
  let collected = Some?.v (P.collect_definitions [] (P.axiom_branches doc.P.entries) doc.P.entries) in
  lemma_document_shape doc collected;
  assert (constructed_definitions []);
  lemma_collect_constructed [] collected (P.axiom_branches doc.P.entries) doc.P.entries;
  let equations = P.reconstruction_equations doc.P.entries [] in
  let inputs = Z3List.append doc.P.assertions (Z3List.map (fun d -> d.Def.body) collected) in
  if equations <> [] && Z3List.for_all (fun e -> Some? (expression_budget 65536 e)) inputs &&
     Z3List.for_all (fun e -> Some? (expression_budget 65536 e.P.formula)) doc.P.entries then
    (match BF.check_context inputs equations with
     | Some rs ->
       lemma_projections_constructed rs;
       (match P.add_definitions collected (BF.projection_definitions rs) with
        | Some result ->
          assert (defs == result);
          lemma_add_definitions_constructed collected (BF.projection_definitions rs) result;
          lemma_constructed_scopes result
        | None ->
          assert (defs == collected);
          lemma_constructed_scopes collected)
     | None ->
       assert (defs == collected);
       lemma_constructed_scopes collected)
  else (
    assert (defs == collected);
    lemma_constructed_scopes collected)
#pop-options

