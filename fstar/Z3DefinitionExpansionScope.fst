module Z3DefinitionExpansionScope

open Z3AstTheory
open FStar.List.Tot
module D = Z3ExprScope
module Def = Z3DefinitionSyntax
module Inst = Z3SortedInstantiation
module Sub = Z3Substitution
module V = Z3DatatypeValue
module L = FStar.List.Tot

let definition_scopes (defs:list Def.definition) : prop =
  forall (d:Def.definition) (scope:list sort) (args:list expr).
    L.mem d defs /\ D.scoped_args scope args /\ sorts_match args d.Def.symbol.domain ==>
      (exists (left:list sort).
        D.scoped left d.Def.body /\ get_sort d.Def.body == d.Def.symbol.range /\
        Inst.instance_scopes left scope d.Def.variables args)

let rec lemma_variable_argument (left right:list sort) (templates actual:list expr)
                                (variables:list nat) (domain:list sort)
                                (n:nat{n < L.length left}) (e:expr)
  : Lemma (requires Def.variables_of templates == Some variables /\
                    D.scoped_args left templates /\ sorts_match templates domain /\
                    D.scoped_args right actual /\ sorts_match actual domain /\
                    Sub.argument n variables actual == Some e)
          (ensures D.scoped right e /\ get_sort e == L.index left n)
          (decreases templates) =
  match templates, actual, variables, domain with
  | Var j s :: rest, a :: tail, _ :: vs, t :: ss ->
    if n <> j then lemma_variable_argument left right rest tail vs ss n e
    else (
      V.lemma_sort_eq s t;
      V.lemma_sort_eq (get_sort a) t)
  | _, _, _, _ -> ()

let lemma_variable_instance_scopes (left right:list sort) (templates actual:list expr)
                                   (variables:list nat) (domain:list sort)
  : Lemma (requires Def.variables_of templates == Some variables /\
                    D.scoped_args left templates /\ sorts_match templates domain /\
                    D.scoped_args right actual /\ sorts_match actual domain)
          (ensures Inst.instance_scopes left right variables actual) =
  let indices (n:nat{n < L.length left})
    : Lemma (match Sub.argument n variables actual with
             | Some e -> D.scoped right e /\ get_sort e == L.index left n
             | None -> True) =
    match Sub.argument n variables actual with
    | Some e -> lemma_variable_argument left right templates actual variables domain n e
    | None -> () in
  FStar.Classical.forall_intro indices

let lemma_constructed_instance (left right:list sort) (templates actual:list expr)
                               (f:func_decl) (body:expr) (d:Def.definition)
  : Lemma (requires Def.make_definition left (App f templates) body == Some d /\
                    D.scoped_args right actual /\ sorts_match actual d.Def.symbol.domain)
          (ensures D.scoped left d.Def.body /\ get_sort d.Def.body == d.Def.symbol.range /\
                   Inst.instance_scopes left right d.Def.variables actual) =
  lemma_variable_instance_scopes left right templates actual d.Def.variables f.domain

let constructed (d:Def.definition) : prop =
  exists (origin:(list sort & list expr)).
    Def.make_definition (fst origin) (App d.Def.symbol (snd origin)) d.Def.body == Some d

let lemma_make_constructed (scope:list sort) (name body:expr) (d:Def.definition)
  : Lemma (requires Def.make_definition scope name body == Some d)
          (ensures constructed d) =
  match name with
  | App _ args ->
    FStar.Classical.exists_intro
      (fun origin -> Def.make_definition (fst origin) (App d.Def.symbol (snd origin)) d.Def.body == Some d)
      (scope, args)
  | _ -> ()

let constructed_definitions (defs:list Def.definition) : prop =
  forall (d:Def.definition). L.mem d defs ==> constructed d

let lemma_constructed_scopes (defs:list Def.definition)
  : Lemma (requires constructed_definitions defs)
          (ensures definition_scopes defs) =
  let at (d:Def.definition) (scope:list sort) (args:list expr)
    : Lemma (
        L.mem d defs /\ D.scoped_args scope args /\ sorts_match args d.Def.symbol.domain ==>
          (exists (left:list sort).
            D.scoped left d.Def.body /\ get_sort d.Def.body == d.Def.symbol.range /\
            Inst.instance_scopes left scope d.Def.variables args)) =
    if L.mem d defs && D.scoped_args scope args && sorts_match args d.Def.symbol.domain then (
      FStar.Classical.exists_elim
        (exists (left:list sort).
          D.scoped left d.Def.body /\ get_sort d.Def.body == d.Def.symbol.range /\
          Inst.instance_scopes left scope d.Def.variables args)
        #(list sort & list expr)
        #(fun origin -> Def.make_definition (fst origin)
          (App d.Def.symbol (snd origin)) d.Def.body == Some d) ()
        (fun origin ->
          let left, templates = origin in
          lemma_constructed_instance left scope templates args d.Def.symbol d.Def.body d;
          FStar.Classical.exists_intro
            (fun left -> D.scoped left d.Def.body /\ get_sort d.Def.body == d.Def.symbol.range /\
                         Inst.instance_scopes left scope d.Def.variables args) left))
  in
  FStar.Classical.forall_intro_3 at

let rec lemma_lookup (defs:list Def.definition) (f:func_decl) (d:Def.definition)
  : Lemma (requires Def.lookup defs f == Some d)
          (ensures L.mem d defs /\ d.Def.symbol == f)
          (decreases defs) =
  match defs with
  | [] -> ()
  | x :: rest -> if x.Def.symbol <> f then lemma_lookup rest f d

let rec lemma_expand_scope (fuel:nat) (defs:list Def.definition) (scope:list sort)
                           (e result:expr)
  : Lemma (requires definition_scopes defs /\ D.scoped scope e /\
                    Def.expand fuel defs e == Some result)
          (ensures D.scoped scope result /\ get_sort result == get_sort e)
          (decreases %[fuel; e]) =
  if defs = [] then ()
  else match e with
  | Var _ _ -> ()
  | Quantifier _ bs _ body ->
    let b = Some?.v (Def.expand fuel defs body) in
    lemma_expand_scope fuel defs (L.rev bs @ scope) body b
  | App f args ->
    let expanded = Some?.v (Def.expand_args fuel defs args) in
    lemma_expand_args_scope fuel defs scope args expanded f.domain;
    (match Def.lookup defs f with
     | None -> ()
     | Some d ->
       if fuel = 0 then ()
       else (
         lemma_lookup defs f d;
         let body = Some?.v (Def.instantiate 0 d.Def.variables expanded d.Def.body) in
         let scoped_body (left:list sort)
           : Lemma (requires D.scoped left d.Def.body /\
                             get_sort d.Def.body == d.Def.symbol.range /\
                             Inst.instance_scopes left scope d.Def.variables expanded)
                   (ensures D.scoped scope body /\ get_sort body == f.range) =
           Inst.lemma_instantiate_scope [] left scope d.Def.variables expanded d.Def.body body in
         FStar.Classical.exists_elim (D.scoped scope body /\ get_sort body == f.range)
           #(list sort)
           #(fun left -> D.scoped left d.Def.body /\
                         get_sort d.Def.body == d.Def.symbol.range /\
                         Inst.instance_scopes left scope d.Def.variables expanded)
           () (fun left -> scoped_body left);
         lemma_expand_scope (fuel - 1) defs scope body result))

and lemma_expand_args_scope (fuel:nat) (defs:list Def.definition) (scope:list sort)
                            (args results:list expr) (ss:list sort)
  : Lemma (requires definition_scopes defs /\ D.scoped_args scope args /\
                    sorts_match args ss /\ Def.expand_args fuel defs args == Some results)
          (ensures D.scoped_args scope results /\ sorts_match results ss)
          (decreases %[fuel; args]) =
  match args, results, ss with
  | [], [], [] -> ()
  | e :: rest, r :: tail, _ :: remaining ->
    lemma_expand_scope fuel defs scope e r;
    lemma_expand_args_scope fuel defs scope rest tail remaining
  | _, _, _ -> ()
