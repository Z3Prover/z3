module Z3BooleanRewriteSyntax

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
open FStar.List.Tot
module B = Z3BoundedBoolEquiv
module N = Z3BooleanNormalForm
module C = Z3CanonicalOps
module Syntax = Z3ClauseSyntax
module BS = Z3BooleanSyntax

type connective =
  | Conjunction
  | Disjunction

let boolean_domain (args:list expr) : list sort = Syntax.boolean_domain args

let boolean_args (args:list expr) : bool = BS.boolean_args args

let connective_decl (op:connective) (args:list expr) : func_decl =
  if op = Conjunction then Syntax.and_decl args else Syntax.or_decl args

let rec lemma_boolean_domain (args:list expr)
  : Lemma (ensures C.boolean_sorts (boolean_domain args)) (decreases args)
  = match args with
    | [] -> ()
    | _ :: rest -> lemma_boolean_domain rest

(* The connective declarations built here are the canonical `and`/`or`. *)
let lemma_connective_decl (op:connective) (args:list expr)
  : Lemma (ensures (op = Conjunction ==> C.canonical_and (connective_decl op args)) /\
                   (op = Disjunction ==> C.canonical_or (connective_decl op args)))
          [SMTPat (connective_decl op args)]
  = lemma_boolean_domain args

let connective_app (op:connective) (f:func_decl) (args:list expr) : bool =
  f = connective_decl op args && boolean_args args

let lemma_connective_app (op:connective) (f:func_decl) (args:list expr)
  : Lemma (requires connective_app op f args)
          (ensures (op = Conjunction ==> C.canonical_and f) /\ (op = Disjunction ==> C.canonical_or f))
          [SMTPat (connective_app op f args)]
  = lemma_boolean_domain args

let rec flatten_expr (op:connective) (e:expr)
  : Tot (list expr) (decreases e) =
  match e with
  | App f args ->
    if connective_app op f args then flatten_args op args else [e]
  | _ -> [e]

and flatten_args (op:connective) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> flatten_expr op a @ flatten_args op rest

let flatten_rewrite (e:expr) : option expr =
  match e with
  | App f args ->
    let op = if f.decl_name = "and" then Conjunction else Disjunction in
    if connective_app op f args then
      let flat = flatten_args op args in
      Some (App (connective_decl op flat) flat)
    else None
  | _ -> None

let boolean_ite_decl : func_decl = BS.boolean_ite_decl

let boolean_xor_decl : func_decl = BS.boolean_xor_decl

let native_bool_op (f:func_decl) (args:list expr) : B.bool_op =
  BS.native_bool_op f args

(* The declarations `native_bool_op` recognizes are the canonical connectives. *)
let lemma_native_bool_op (f:func_decl) (args:list expr)
  : Lemma (match native_bool_op f args with
           | B.BNary B.And -> C.canonical_and f
           | B.BNary B.Or -> C.canonical_or f
           | B.BNot -> C.canonical_not f
           | B.BImplies -> C.canonical_implies f
           | B.BEq -> C.canonical_eq f
           | B.BTrue -> C.canonical_true f
           | B.BFalse -> C.canonical_false f
           | _ -> True)
  = lemma_boolean_domain args

let reflexive_equality (e:expr) : bool =
  match e with
  | App f [a; b] -> f = eq_decl (get_sort a) && a = b
  | _ -> false

let boolean_nodes (depth:nat) (e:expr) : list expr = BS.boolean_nodes depth e

let boolean_nodes_args (depth:nat) (args:list expr) : list expr =
  BS.boolean_nodes_args depth args

let boolean_leaf (e:expr) : bool =
  match e with
  | App f args ->
    (match native_bool_op f args with B.BTrue | B.BFalse | B.Opaque -> true | _ -> false)
  | _ -> true

let rec boolean_leaves (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> boolean_leaf a && boolean_leaves rest

let rec boolean_frontier (depth:nat) (e:expr) : Tot (list expr) (decreases e) =
  match e with
  | App f args ->
    (match native_bool_op f args with
     | B.BTrue | B.BFalse | B.Opaque -> []
     | _ -> if depth = 0 then (if boolean_leaves args then [] else [e])
            else boolean_args_frontier (depth - 1) args)
  | _ -> []

and boolean_args_frontier (depth:nat) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> boolean_frontier depth a @ boolean_args_frontier depth rest

let rec boolean_cut (boundaries:list expr) (depth:nat) (e:expr)
  : Tot B.skeleton (decreases e) =
  if reflexive_equality e then B.Bool true
  else if mem e boundaries then B.Atom e
  else match e with
  | App f args ->
    (match native_bool_op f args with
     | B.BTrue -> B.Bool true
     | B.BFalse -> B.Bool false
     | B.BNary op ->
       if depth = 0 then B.Atom e
       else B.Nary op (boolean_cut_args boundaries (depth - 1) args)
     | B.BNot ->
       (match args with
        | [a] -> if depth = 0 then B.Atom e
                 else B.Not (boolean_cut boundaries (depth - 1) a)
        | _ -> B.Atom e)
     | B.BImplies ->
       (match args with
        | [a; b] -> if depth = 0 then B.Atom e
                    else B.Implies (boolean_cut boundaries (depth - 1) a)
                                   (boolean_cut boundaries (depth - 1) b)
        | _ -> B.Atom e)
     | B.BEq ->
       (match args with
        | [a; b] -> if depth = 0 then B.Atom e
                    else B.Eq (boolean_cut boundaries (depth - 1) a)
                              (boolean_cut boundaries (depth - 1) b)
        | _ -> B.Atom e)
     | B.BIte ->
       (match args with
        | [c; t; f] -> if depth = 0 then B.Atom e
                       else B.boolean_ite (boolean_cut boundaries (depth - 1) c)
                                          (boolean_cut boundaries (depth - 1) t)
                                          (boolean_cut boundaries (depth - 1) f)
        | _ -> B.Atom e)
     | _ -> B.Atom e)
  | _ -> B.Atom e

and boolean_cut_args (boundaries:list expr) (depth:nat) (args:list expr)
  : Tot (list B.skeleton) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> boolean_cut boundaries depth a :: boolean_cut_args boundaries depth rest

let rec boolean_height (e:expr) : Tot nat (decreases e) =
  match e with
  | App f args -> if native_bool_op f args = B.Opaque then 0
                  else 1 + boolean_args_height args
  | _ -> 0

and boolean_args_height (args:list expr) : Tot nat (decreases args) =
  match args with
  | [] -> 0
  | a :: rest ->
    let x = boolean_height a in
    let y = boolean_args_height rest in
    if x > y then x else y

let structural_boolean_equiv (s t:expr) : bool =
  N.equivalent (boolean_cut [] (boolean_height s) s)
               (boolean_cut [] (boolean_height t) t)

let boolean_equiv (depth width:nat) (s t:expr) : bool =
  if get_sort s <> bool_sort || get_sort t <> bool_sort then false
  else if structural_boolean_equiv s t then true
  else
    let boundaries = B.unique (B.intersect (boolean_nodes depth s) (boolean_nodes depth t)) in
    let cs = boolean_cut boundaries depth s in
    let ct = boolean_cut boundaries depth t in
    let atoms = B.unique (B.support cs @ B.support ct) in
    N.equivalent cs ct ||
    (length atoms <= width && B.check_rows atoms (fun _ -> false) cs ct)

let boolean_search (s t:expr) : bool =
  get_sort s = bool_sort && get_sort t = bool_sort &&
  N.shannon 7 (N.normalize_context 2 (boolean_cut [] (boolean_height s) s))
              (N.normalize_context 2 (boolean_cut [] (boolean_height t) t))

