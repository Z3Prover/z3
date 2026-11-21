module Z3DefinitionSyntax

open Z3AstTheory
open FStar.List.Tot
module L = FStar.List.Tot
module Scope = Z3ExprScope
module Binding = Z3ExprBinding
module Substitution = Z3Substitution

type definition = {
  symbol: func_decl;
  variables: list nat;
  body: expr;
}

let scoped (scope:list sort) (e:expr) : bool = Scope.scoped scope e
let scoped_args (scope:list sort) (args:list expr) : bool = Scope.scoped_args scope args

let rec lookup (defs:list definition) (f:func_decl)
  : Tot (option definition) (decreases defs) =
  match defs with
  | [] -> None
  | d :: rest -> if d.symbol = f then Some d else lookup rest f

let rec fresh (defs:list definition) (e:expr) : Tot bool (decreases e) =
  if defs = [] then true
  else match e with
  | Var _ _ -> true
  | App f args -> lookup defs f = None && fresh_args defs args
  | Quantifier _ _ _ b -> fresh defs b

and fresh_args (defs:list definition) (args:list expr)
  : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> fresh defs a && fresh_args defs rest

let lift (amount cutoff:nat) (e:expr) : expr = Binding.lift amount cutoff e

let lift_args (amount cutoff:nat) (args:list expr) : list expr =
  Binding.lift_args amount cutoff args

let argument (n:nat) (variables:list nat) (args:list expr) : option expr =
  Substitution.argument n variables args

let instantiate (depth:nat) (variables:list nat) (args:list expr) (e:expr) : option expr =
  Substitution.instantiate depth variables args e

let instantiate_args (depth:nat) (variables:list nat) (args es:list expr) : option (list expr) =
  Substitution.instantiate_args depth variables args es

let rec expand (fuel:nat) (defs:list definition) (e:expr)
  : Tot (option expr) (decreases %[fuel; e]) =
  if defs = [] then Some e
  else match e with
  | Var _ _ -> Some e
  | Quantifier k bs s b ->
    (match expand fuel defs b with
     | Some b' -> Some (Quantifier k bs s b') | None -> None)
  | App f args ->
    (match expand_args fuel defs args with
     | None -> None
     | Some args' ->
       (match lookup defs f with
        | None -> Some (App f args')
        | Some d ->
          if fuel = 0 then None
          else match instantiate 0 d.variables args' d.body with
               | Some b -> expand (fuel - 1) defs b
               | None -> None))

and expand_args (fuel:nat) (defs:list definition) (args:list expr)
  : Tot (option (list expr)) (decreases %[fuel; args]) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match expand fuel defs a, expand_args fuel defs rest with
     | Some a', Some rest' -> Some (a' :: rest') | _, _ -> None)

let rec lemma_fresh_expansion (fuel:nat) (defs:list definition) (e:expr)
  : Lemma (requires fresh defs e)
          (ensures expand fuel defs e == Some e)
          (decreases e) =
  if defs = [] then ()
  else match e with
  | Var _ _ -> ()
  | App _ args -> lemma_fresh_args_expansion fuel defs args
  | Quantifier _ _ _ b -> lemma_fresh_expansion fuel defs b

and lemma_fresh_args_expansion (fuel:nat) (defs:list definition) (args:list expr)
  : Lemma (requires fresh_args defs args)
          (ensures expand_args fuel defs args == Some args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_fresh_expansion fuel defs a;
    lemma_fresh_args_expansion fuel defs rest

type expansion_value (fuel:nat) (defs:list definition) (source:expr) =
  result:(option expr & bool){
    fst result == expand fuel defs source /\
    (snd result ==> fst result == Some source)}

noeq
type expansion_entry (defs:list definition) = {
  expansion_fuel: nat;
  expansion_source: expr;
  expansion_value: expansion_value expansion_fuel defs expansion_source;
}

type expansion_cache (defs:list definition) =
  Z3ProofIndex.index_tree (list (expansion_entry defs))

let rec find_expansion (#defs:list definition) (fuel:nat) (e:expr)
                       (bucket:list (expansion_entry defs))
  : Tot (option (expansion_value fuel defs e))
        (decreases bucket) =
  match bucket with
  | [] -> None
  | entry :: rest ->
    if entry.expansion_fuel = fuel && entry.expansion_source = e
    then Some entry.expansion_value
    else find_expansion fuel e rest

let rec expand_cached (hash:(nat & expr) -> nat) (fuel:nat) (defs:list definition)
                      (e:expr) (cache:expansion_cache defs)
  : Tot (expansion_value fuel defs e & expansion_cache defs)
        (decreases %[fuel; e]) =
  let key = hash (fuel, e) % 65521 in
  let bucket = match Z3ProofIndex.index_get cache key with Some xs -> xs | None -> [] in
  match find_expansion fuel e bucket with
  | Some value -> value, cache
  | None ->
    let value, cache =
      if defs = [] then (Some e, true), cache
      else match e with
      | Var _ _ -> (Some e, true), cache
      | Quantifier k bs s b ->
        let (body, unchanged), cache = expand_cached hash fuel defs b cache in
        (match body with
         | Some b' -> (Some (if unchanged then e else Quantifier k bs s b'), unchanged), cache
         | None -> (None, false), cache)
      | App f args ->
        let (expanded, unchanged), cache = expand_args_cached hash fuel defs args cache in
        (match expanded with
         | None -> (None, false), cache
         | Some args' ->
           (match lookup defs f with
            | None -> (Some (if unchanged then e else App f args'), unchanged), cache
            | Some d ->
              if fuel = 0 then (None, false), cache
              else match instantiate 0 d.variables args' d.body with
                   | Some b ->
                     let (body, _), cache = expand_cached hash (fuel - 1) defs b cache in
                     (body, false), cache
                   | None -> (None, false), cache))
    in
    let entry = {
      expansion_fuel = fuel; expansion_source = e; expansion_value = value;
    } in
    let bucket = match Z3ProofIndex.index_get cache key with Some xs -> xs | None -> [] in
    value, Z3ProofIndex.index_put cache key (entry :: bucket)

and expand_args_cached (hash:(nat & expr) -> nat) (fuel:nat) (defs:list definition)
                       (args:list expr) (cache:expansion_cache defs)
  : Tot (result:((option (list expr) & bool) & expansion_cache defs){
      fst (fst result) == expand_args fuel defs args /\
      (snd (fst result) ==> fst (fst result) == Some args)})
        (decreases %[fuel; args]) =
  match args with
  | [] -> (Some [], true), cache
  | a :: rest ->
    let (value, unchanged), cache = expand_cached hash fuel defs a cache in
    let (values, rest_unchanged), cache = expand_args_cached hash fuel defs rest cache in
    (match value, values with
     | Some a', Some rest' ->
       let unchanged = unchanged && rest_unchanged in
       (Some (if unchanged then args else a' :: rest'), unchanged), cache
     | _, _ -> (None, false), cache)

let memoized_expand (hash:(nat & expr) -> nat) (fuel:nat) (defs:list definition) (e:expr)
  : result:option expr{result == expand fuel defs e} =
  fst (fst (expand_cached hash fuel defs e Z3ProofIndex.Empty))

type expander =
  fuel:nat -> defs:list definition -> e:expr ->
  Tot (result:option expr{result == expand fuel defs e})

let linear_expander : expander = fun fuel defs e -> expand fuel defs e

let memoized_expander (hash:(nat & expr) -> nat) : expander =
  fun fuel defs e -> memoized_expand hash fuel defs e

let rec lemma_expand_list_using (transform:expander) (fuel:nat) (defs:list definition) (args:list expr)
  : Lemma (ensures Z3ProofIndex.opt_map (transform fuel defs) args == expand_args fuel defs args)
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> lemma_expand_list_using transform fuel defs rest

(* Assertion lists grow with the input, so this uses the tail-recursive opt_map. *)
let expand_list_using (transform:expander) (fuel:nat) (defs:list definition) (args:list expr)
  : result:option (list expr){result == expand_args fuel defs args} =
  lemma_expand_list_using transform fuel defs args;
  Z3ProofIndex.opt_map_tail (transform fuel defs) args

let check_fresh_inputs (defs:list definition) (assertions:list expr)
  : b:bool{b ==> fresh_args defs assertions /\
                 expand_args (L.length defs) defs assertions == Some assertions} =
  if fresh_args defs assertions then (
    lemma_fresh_args_expansion (L.length defs) defs assertions;
    true)
  else false

let rec variables_of (args:list expr) : Tot (option (list nat)) (decreases args) =
  match args with
  | [] -> Some []
  | Var n _ :: rest ->
    (match variables_of rest with
     | Some ns -> if L.mem n ns then None else Some (n :: ns)
     | None -> None)
  | _ -> None

let make_definition (scope:list sort) (name body:expr) : option definition =
  match name with
  | App f args ->
    if f.interp <> None || f.int_params <> [] ||
       get_sort body <> f.range || not (scoped scope name && scoped scope body) ||
       L.length args <> L.length scope then None
    else (match variables_of args with
    | Some ns -> Some { symbol = f; variables = ns; body = body }
    | None -> None)
  | _ -> None

let rec strip_forall (scope:list sort) (e:expr)
  : Tot (list sort & expr) (decreases e) =
  match e with
  | Quantifier Forall_k bs _ b -> strip_forall (L.rev bs @ scope) b
  | _ -> (scope, e)

