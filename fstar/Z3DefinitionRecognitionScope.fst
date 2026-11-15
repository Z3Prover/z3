module Z3DefinitionRecognitionScope

open Z3AstTheory
module Def = Z3DefinitionRecognition
module A = Z3ArraySyntax
module AS = Z3ArraySyntax
module Bool = Z3BooleanRewriteSyntax
module L = FStar.List.Tot

include Z3DefinitionExpansionScope

let lemma_ite_constructed (scope:list sort) (c x t y u:expr) (d:Def.definition)
  : Lemma (requires Def.ite_definition scope c x t y u == Some d)
          (ensures constructed d) =
  lemma_make_constructed scope x (App (A.term_ite_decl (get_sort t)) [c; t; u]) d

let lemma_clause_constructed (scope:list sort) (a b:expr) (d:Def.definition)
  : Lemma (requires Def.clause_definition scope a b == Some d)
          (ensures constructed d) =
  match Def.ite_clauses a b with
  | Some (c, p, q) ->
    (match AS.equality_parts p, AS.equality_parts q with
     | Some (x, t), Some (y, u) ->
       if Some? (Def.ite_definition scope c x t y u) then
         lemma_ite_constructed scope c x t y u d
       else if Some? (Def.ite_definition scope c x t u y) then
         lemma_ite_constructed scope c x t u y d
       else if Some? (Def.ite_definition scope c t x y u) then
         lemma_ite_constructed scope c t x y u d
       else lemma_ite_constructed scope c t x u y d
     | _, _ -> ())
  | None -> ()

let lemma_boolean_constructed (scope:list sort) (e:expr) (d:Def.definition)
  : Lemma (requires Def.boolean_definition scope e == Some d)
          (ensures constructed d) =
  match Def.binary Bool.Disjunction e with
  | Some (a, b) ->
    (match Def.negation a with
     | Some n -> lemma_make_constructed scope n b d
     | None ->
       (match Def.negation b with
        | Some t -> lemma_make_constructed scope a t d
        | None -> ()))
  | None -> ()

let lemma_definition_constructed (e:expr) (d:Def.definition)
  : Lemma (requires Def.definition_of e == Some d)
          (ensures constructed d) =
  let scope, b = Def.strip_forall [] e in
  match AS.equality_parts b with
  | Some (a, n) ->
    if Some? (Def.make_definition scope n a) then lemma_make_constructed scope n a d
    else lemma_make_constructed scope a n d
  | None ->
    (match Def.binary Bool.Conjunction b with
     | Some (a, c) ->
       let sa, a' = Def.strip_forall scope a in
       let sc, c' = Def.strip_forall scope c in
       if sa = sc then (
         if Some? (Def.clause_definition sa a' c') then
           lemma_clause_constructed sa a' c' d
         else if Some? (Def.clause_definition sa c' a') then
           lemma_clause_constructed sa c' a' d
         else if Some? (Def.boolean_definition sa a') then
           lemma_boolean_constructed sa a' d
         else lemma_boolean_constructed sa c' d)
     | None -> lemma_boolean_constructed scope b d)

let rec lemma_paired_constructed (e:expr) (axioms:list expr) (d:Def.definition)
  : Lemma (requires Def.paired_definition e axioms == Some d)
          (ensures constructed d)
          (decreases axioms) =
  match axioms with
  | [] -> ()
  | a :: rest ->
    let se, e' = Def.strip_forall [] e in
    let sa, a' = Def.strip_forall [] a in
    if se = sa && Some? (Def.clause_definition se e' a') then
      lemma_clause_constructed se e' a' d
    else if se = sa && Some? (Def.clause_definition se a' e') then
      lemma_clause_constructed se a' e' d
    else lemma_paired_constructed e rest d

let lemma_axiom_constructed (e:expr) (branches:list expr) (d:Def.definition)
  : Lemma (requires Def.axiom_definition e branches == Some d)
          (ensures constructed d) =
  let _, b = Def.strip_forall [] e in
  if Some? (AS.equality_parts b) || Some? (Def.binary Bool.Conjunction b) then
    lemma_definition_constructed e d
  else lemma_paired_constructed e branches d

let lemma_add_constructed (defs:list Def.definition) (d:Def.definition) (result:list Def.definition)
  : Lemma (requires constructed_definitions defs /\ constructed d /\
                    Def.add_definition defs d == Some result)
          (ensures constructed_definitions result) =
  let at (e:Def.definition) : Lemma (L.mem e result ==> constructed e) =
    if L.mem e result then () in
  FStar.Classical.forall_intro at

