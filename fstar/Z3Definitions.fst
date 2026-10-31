module Z3Definitions

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3BooleanRewrite
open Z3ArrayLemma
module A = Z3ArrayRewrite
module E = Z3DistinctEmbed
module L = FStar.List.Tot
open FStar.List.Tot

type definition = {
  symbol: func_decl;
  variables: list nat;
  body: expr;
}

let rec scoped (scope:list sort) (e:expr) : Tot bool (decreases e) =
  match e with
  | Var n s -> n < L.length scope && L.index scope n = s
  | App f args -> sorts_match args f.domain && scoped_args scope args
  | Quantifier k bs s b ->
    s = quant_sort k bs (get_sort b) &&
    (k = Lambda_k || get_sort b = bool_sort) &&
    scoped (L.rev bs @ scope) b

and scoped_args (scope:list sort) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> scoped scope a && scoped_args scope rest

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

let rec lift (amount cutoff:nat) (e:expr) : Tot expr (decreases e) =
  match e with
  | Var n s -> Var (if n < cutoff then n else n + amount) s
  | App f args -> App f (lift_args amount cutoff args)
  | Quantifier k bs s b -> Quantifier k bs s (lift amount (cutoff + L.length bs) b)

and lift_args (amount cutoff:nat) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> lift amount cutoff a :: lift_args amount cutoff rest

let rec argument (n:nat) (variables:list nat) (args:list expr)
  : Tot (option expr) (decreases variables) =
  match variables, args with
  | v :: vs, a :: rest -> if n = v then Some a else argument n vs rest
  | _, _ -> None

let rec instantiate (depth:nat) (variables:list nat) (args:list expr) (e:expr)
  : Tot (option expr) (decreases e) =
  match e with
  | Var n s ->
    if n < depth then Some e
    else (match argument (n - depth) variables args with
         | Some a -> Some (lift depth 0 a)
         | None -> None)
  | App f es ->
    (match instantiate_args depth variables args es with
     | Some es' -> Some (App f es') | None -> None)
  | Quantifier k bs s b ->
    (match instantiate (depth + L.length bs) variables args b with
     | Some b' -> Some (Quantifier k bs s b') | None -> None)

and instantiate_args (depth:nat) (variables:list nat) (args es:list expr)
  : Tot (option (list expr)) (decreases es) =
  match es with
  | [] -> Some []
  | e :: rest ->
    (match instantiate depth variables args e, instantiate_args depth variables args rest with
     | Some e', Some rest' -> Some (e' :: rest') | _, _ -> None)

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

let binary (op:connective) (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] -> if connective_app op f [a; b] then Some (a, b) else None
  | _ -> None

let negation (e:expr) : option expr =
  match e with
  | App f [a] -> if native_bool_op f [a] = Z3BoundedBoolEquiv.BNot then Some a else None
  | _ -> None

let ite_clauses (a b:expr) : option (expr & expr & expr) =
  match binary Disjunction a, binary Disjunction b with
  | Some (nc, p), Some (c, q) ->
    if negation nc = Some c then Some (c, p, q) else None
  | _, _ -> None

let ite_definition (scope:list sort) (c x t y u:expr) : option definition =
  if x = y && get_sort t = get_sort u && get_sort c = bool_sort
  then make_definition scope x (App (A.term_ite_decl (get_sort t)) [c; t; u])
  else None

let clause_definition (scope:list sort) (a b:expr) : option definition =
  match ite_clauses a b with
  | Some (c, p, q) ->
    (match equality_parts p, equality_parts q with
     | Some (x, t), Some (y, u) ->
       (match ite_definition scope c x t y u with
        | Some d -> Some d
        | None ->
          (match ite_definition scope c x t u y with
           | Some d -> Some d
           | None ->
             (match ite_definition scope c t x y u with
              | Some d -> Some d | None -> ite_definition scope c t x u y)))
     | _, _ -> None)
  | None -> None

let boolean_definition (scope:list sort) (e:expr) : option definition =
  match binary Disjunction e with
  | Some (a, b) ->
    (match negation a with
     | Some n -> make_definition scope n b
     | None ->
       (match negation b with Some t -> make_definition scope a t | None -> None))
  | None -> None

let definition_of (e:expr) : option definition =
  let scope, b = strip_forall [] e in
  match equality_parts b with
  | Some (a, n) ->
    (match make_definition scope n a with
     | Some d -> Some d | None -> make_definition scope a n)
  | None ->
    (match binary Conjunction b with
     | Some (a, c) ->
       let sa, a' = strip_forall scope a in
       let sc, c' = strip_forall scope c in
       if sa <> sc then None
       else
         (match clause_definition sa a' c' with
          | Some d -> Some d
          | None ->
            (match clause_definition sa c' a' with
             | Some d -> Some d
             | None ->
               (match boolean_definition sa a' with
                | Some d -> Some d | None -> boolean_definition sa c')))
     | None -> boolean_definition scope b)

let add_definition (defs:list definition) (d:definition) : option (list definition) =
  match lookup defs d.symbol with
  | None -> Some (d :: defs)
  | Some old -> if old = d then Some defs else None

let rec acyclic (fuel:nat) (all defs:list definition) : Tot bool (decreases defs) =
  match defs with
  | [] -> true
  | d :: rest -> Some? (expand fuel all d.body) && acyclic fuel all rest

let rec acyclic_using (transform:expander) (fuel:nat) (all defs:list definition)
  : Tot (result:bool{result == acyclic fuel all defs}) (decreases defs) =
  match defs with
  | [] -> true
  | d :: rest ->
    Some? (transform fuel all d.body) && acyclic_using transform fuel all rest

let branch_equation (c a b:expr) (positive:bool) : bool =
  match A.ite_parts a with
  | Some (guard, t, u) -> c = guard && b = (if positive then t else u)
  | None -> false

let branch_axiom (e:expr) : bool =
  match binary Disjunction e with
  | Some (guard, equation) ->
    let c, positive =
      match negation guard with Some c -> c, true | None -> guard, false in
    (match equality_parts equation with
     | Some (a, b) -> branch_equation c a b positive || branch_equation c b a positive
     | None -> false)
  | None -> false

let forall_sound (i:interpretation value) : prop =
  forall (bs:list sort) (b:expr) (rho:env value).
    {:pattern (eval i (Quantifier Forall_k bs bool_sort b) rho)}
    (forall (vs:list value). L.length vs == L.length bs ==>
       lit_true i (shift vs rho) b) ==>
    lit_true i rho (Quantifier Forall_k bs bool_sort b)

let definition_model (i:interpretation value) : prop =
  boolean_rewrite_model i /\ A.term_ite_sound i /\ forall_sound i /\ E.distinct_sound i

#push-options "--fuel 4 --ifuel 2"

let lemma_binary (i:interpretation value) (rho:env value)
                 (op:connective) (e a b:expr)
  : Lemma (requires and_sound i /\ or_sound i /\ binary op e == Some (a, b))
          (ensures lit_true i rho e <==> connective_holds op i rho [a; b])
  = match e with
    | App _ [_; _] -> (match op with Conjunction | Disjunction -> ())
    | _ -> ()

let lemma_branch_equation (i:interpretation value) (rho:env value)
                          (c a b:expr) (positive:bool)
  : Lemma (requires definition_model i /\ branch_equation c a b positive)
          (ensures get_sort c == bool_sort /\
                   ((lit_true i rho c <==> positive) ==> eval i a rho == eval i b rho))
  = match A.ite_parts a with
    | Some (guard, t, u) ->
      A.lemma_ite_parts i rho a guard t u;
      (match eval i c rho with VBool _ -> () | _ -> ())
    | None -> ()

let lemma_branch_axiom (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires definition_model i /\ branch_axiom e)
          (ensures lit_true i rho e)
  = match binary Disjunction e with
    | Some (guard, equation) ->
      lemma_binary i rho Disjunction e guard equation;
      let c, positive =
        match negation guard with Some c -> c, true | None -> guard, false in
      (match equality_parts equation with
       | Some (a, b) ->
         lemma_equality_parts i rho equation a b;
         (if branch_equation c a b positive then lemma_branch_equation i rho c a b positive
          else lemma_branch_equation i rho c b a positive);
         (match negation guard with
          | Some c' ->
            (match guard with App f [_] -> lemma_not_relates i rho f c' | _ -> ())
          | None -> ());
         (match eval i c rho with VBool _ -> () | _ -> ())
       | None -> ())
    | None -> ()

#pop-options

(* One extra level fully unfolds literal connectives omitted from the
   frontier, avoiding a boundary entry for every literal of a wide gate. *)
let propositional_tautology (e:expr) : bool =
  get_sort e = bool_sort &&
  Z3BooleanNormalForm.clause_tautology (boolean_cut (boolean_frontier 3 e) 4 e)

let lemma_propositional_tautology_sound (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires definition_model i /\ propositional_tautology e)
          (ensures lit_true i rho e) =
  let s = boolean_cut (boolean_frontier 3 e) 4 e in
  Z3BoundedBoolEquiv.lemma_freeze (valuation i rho) (Z3BoundedBoolEquiv.support s) s;
  Z3BooleanNormalForm.lemma_clause_tautology_sound
    (Z3BoundedBoolEquiv.freeze (valuation i rho) (Z3BoundedBoolEquiv.support s)) s;
  lemma_boolean_cut_sound (boolean_frontier 3 e) 4 i rho e;
  match eval i e rho with VBool _ -> () | _ -> ()

let rec boolean_budget (fuel:nat) (e:expr) : Tot (option nat) (decreases e) =
  if fuel = 0 then None
  else match e with
  | App f args ->
    if native_bool_op f args = Z3BoundedBoolEquiv.Opaque then Some (fuel - 1)
    else boolean_args_budget (fuel - 1) args
  | _ -> Some (fuel - 1)

and boolean_args_budget (fuel:nat) (args:list expr)
  : Tot (option nat) (decreases args) =
  match args with
  | [] -> Some fuel
  | a :: rest ->
    (match boolean_budget fuel a with
     | Some remaining -> boolean_args_budget remaining rest
     | None -> None)

let bounded_tautology (e:expr) : bool =
  Some? (boolean_budget 128 e) && boolean_equiv 8 10 e true_expr

let rec tautology (fuel:nat) (e:expr) : Tot bool (decreases %[fuel; 0]) =
  if fuel = 0 then false
  else match e with
  | Quantifier Forall_k bs s b -> s = bool_sort && tautology (fuel - 1) b
  | App f args ->
    if E.distinct_axiom e || branch_axiom e || propositional_tautology e then true
    else if connective_app Conjunction f args then tautologies (fuel - 1) args
    else bounded_tautology e
  | _ -> bounded_tautology e

and tautologies (fuel:nat) (args:list expr)
  : Tot bool (decreases %[fuel; L.length args + 1]) =
  match args with
  | [] -> true
  | a :: rest -> tautology fuel a && tautologies fuel rest

let axiom_branch (e:expr) : bool =
  let _, b = strip_forall [] e in
  match binary Disjunction b with
  | Some (_, eq) -> Some? (equality_parts eq)
  | None -> false

let rec paired_definition (e:expr) (axioms:list expr)
  : Tot (option definition) (decreases axioms) =
  match axioms with
  | [] -> None
  | a :: rest ->
    let se, e' = strip_forall [] e in
    let sa, a' = strip_forall [] a in
    let candidate =
      if se <> sa then None
      else match clause_definition se e' a' with
           | Some d -> Some d
           | None -> clause_definition se a' e' in
    (match candidate with
     | Some d -> Some d
     | None -> paired_definition e rest)

let axiom_definition (e:expr) (branches:list expr) : option definition =
  let _, b = strip_forall [] e in
  let direct = Some? (equality_parts b) || Some? (binary Conjunction b) in
  if not (direct || axiom_branch e) || tautology 128 e then None
  else
    if direct then definition_of e
    else if axiom_branch e then paired_definition e branches
    else None

let rec lemma_tautology_sound (fuel:nat) (i:interpretation value)
                             (rho:env value) (e:expr)
  : Lemma (requires definition_model i /\ tautology fuel e)
          (ensures lit_true i rho e)
          (decreases %[fuel; 0]) =
  if fuel = 0 then ()
  else match e with
  | Quantifier Forall_k bs s b ->
    let aux (vs:list value)
      : Lemma (lit_true i (shift vs rho) b)
      = lemma_tautology_sound (fuel - 1) i (shift vs rho) b
    in FStar.Classical.forall_intro aux
  | App f args ->
    if E.distinct_axiom e then E.lemma_distinct_axiom_sound i rho e
    else if branch_axiom e then lemma_branch_axiom i rho e
    else if propositional_tautology e then lemma_propositional_tautology_sound i rho e
    else if connective_app Conjunction f args then lemma_tautologies_sound (fuel - 1) i rho args
    else lemma_boolean_equiv_sound 8 10 i rho e true_expr
  | _ -> lemma_boolean_equiv_sound 8 10 i rho e true_expr

and lemma_tautologies_sound (fuel:nat) (i:interpretation value)
                            (rho:env value) (args:list expr)
  : Lemma (requires definition_model i /\ tautologies fuel args)
          (ensures conj_holds i rho args)
          (decreases %[fuel; L.length args + 1]) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_tautology_sound fuel i rho a;
    lemma_tautologies_sound fuel i rho rest
