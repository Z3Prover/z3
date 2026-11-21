module Z3DistinctAst

(* Native declarations use Z3OperatorTags' namespace, not the older
   basic-family decl_kind_of numbering in Z3BasicExprTheory. *)
open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
open Z3BooleanRewriteSyntax
open FStar.List.Tot
module L = FStar.List.Tot

let rec repeat_sort (s:sort) (n:nat) : Tot (list sort) (decreases n) =
  if n = 0 then [] else s :: repeat_sort s (n - 1)

let distinct_decl (s:sort) (arity:nat) : func_decl =
  { decl_name = "distinct"; domain = repeat_sort s arity; range = bool_sort;
    interp = Some op_distinct; int_params = [] }

let mk_distinct_expr (s:sort) (args:list expr) : expr =
  App (distinct_decl s (L.length args)) args

let rec same_sort (s:sort) (dom:list sort) : Tot bool (decreases dom) =
  match dom with [] -> true | t :: rest -> s = t && same_sort s rest

let distinct_declaration (f:func_decl) : bool =
  f.decl_name = "distinct" && f.range = bool_sort &&
  f.interp = Some op_distinct && f.int_params = [] &&
  (match f.domain with [] -> true | s :: rest -> same_sort s rest)

let distinct_app (f:func_decl) (args:list expr) : bool =
  distinct_declaration f && sorts_match args f.domain

let distinct_parts (e:expr) : option (list expr) =
  match e with
  | App f args -> if distinct_app f args then Some args else None
  | _ -> None

let rec has_duplicate (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> false
  | a :: rest -> L.mem a rest || has_duplicate rest

let duplicate_rewrite (a b:expr) : bool =
  b = false_expr &&
  (match distinct_parts a with Some args -> has_duplicate args | None -> false)

let rec disequalities_from (a:expr) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | b :: rest -> mk_not_expr (mk_eq_expr a b) :: disequalities_from a rest

let rec disequalities (args:list expr) : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> disequalities_from a rest @ disequalities rest

(* Match ast_manager::mk_distinct_expanded, including the small arities. *)
let expanded (args:list expr) : expr =
  match args with
  | [] | [_] -> true_expr
  | [a; b] -> mk_not_expr (mk_eq_expr a b)
  | _ ->
    let pairs = disequalities args in
    App (and_decl pairs) pairs

let lemma_expanded_sort (args:list expr) : Lemma (get_sort (expanded args) == bool_sort) =
  match args with [] | [_] | [_; _] -> () | _ -> ()

let apply_lemma_distinct (e:expr) : option expr =
  match distinct_parts e with
  | Some args -> Some (expanded args)
  | None -> None

let expansion_rewrite (a b:expr) : bool =
  apply_lemma_distinct a = Some b || apply_lemma_distinct b = Some a

let negation (e:expr) : option expr =
  match e with
  | App f [a] -> if f = not_decl && get_sort a = bool_sort then Some a else None
  | _ -> None

let distinct_clause (a b:expr) : bool =
  (match negation a with
   | Some d -> apply_lemma_distinct d = Some b
   | None -> false) ||
  (match apply_lemma_distinct a with
   | Some p -> negation b = Some p || negation p = Some b
   | None -> false)

let distinct_axiom (e:expr) : bool =
  match e with
  | App f [a; b] ->
    connective_app Disjunction f [a; b] &&
    (distinct_clause a b || distinct_clause b a)
  | _ -> false
