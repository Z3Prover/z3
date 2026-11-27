module Z3DocumentFactSemantics

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module P = Z3DocumentPreparation
module I = Z3ProofIndex
module IT = Z3IdTable
module D = Z3DefinitionRecognition

let table_holds (good:U.checked_fact -> prop) (table:IT.t U.checked_fact) : prop =
  forall (id:int) (fact:U.checked_fact). IT.find table id == Some fact ==> good fact

let rec facts_hold (good:U.checked_fact -> prop) (facts:list U.checked_fact)
  : Tot prop (decreases facts) =
  match facts with
  | [] -> True
  | fact :: rest -> good fact /\ facts_hold good rest

let lemma_empty (good:U.checked_fact -> prop)
  : Lemma (table_holds good IT.empty) =
  let at (id:int) (fact:U.checked_fact)
    : Lemma (IT.find IT.empty id == Some fact ==> good fact) =
    IT.lemma_find_empty #U.checked_fact id in
  FStar.Classical.forall_intro_2 at

let lemma_put (good:U.checked_fact -> prop) (table:IT.t U.checked_fact)
              (id:nat) (fact:U.checked_fact)
  : Lemma (requires table_holds good table /\ good fact)
          (ensures table_holds good (IT.put table id fact)) =
  let at (query:int) (found:U.checked_fact)
    : Lemma (IT.find (IT.put table id fact) query == Some found ==> good found) =
    IT.lemma_find_put table id fact query in
  FStar.Classical.forall_intro_2 at

let rec lemma_lookup (good:U.checked_fact -> prop) (table:IT.t U.checked_fact)
                     (ids:list int) (facts:list U.checked_fact)
  : Lemma (requires table_holds good table /\ I.opt_map (IT.find table) ids == Some facts)
          (ensures facts_hold good facts)
          (decreases ids) =
  match ids with
  | [] -> ()
  | id :: rest ->
    (match IT.find table id, I.opt_map (IT.find table) rest with
     | Some _, Some tail -> lemma_lookup good table rest tail
     | _, _ -> ())

let lemma_prepared (good:U.checked_fact -> prop) (transform:D.expander) (bound:bool)
                   (defs:list D.definition) (table:IT.t U.checked_fact)
                   (entry:P.entry) (node:U.proof_node)
  : Lemma (requires table_holds good table /\
                    P.prepare_entry_using transform bound defs table entry == Some node)
          (ensures facts_hold good node.U.premises) =
  I.lemma_opt_map_tail (IT.find table) entry.P.premise_ids;
  match I.opt_map (IT.find table) entry.P.premise_ids with
  | Some facts -> lemma_lookup good table entry.P.premise_ids facts
  | None -> ()
