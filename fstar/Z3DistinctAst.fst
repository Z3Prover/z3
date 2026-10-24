module Z3DistinctAst

(* Native declarations use Z3ValueTheory's tag namespace, not the older
   basic-family decl_kind_of numbering in Z3BasicExprTheory. *)
open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3BooleanRewrite
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
    App (connective_decl Conjunction pairs) pairs

let lemma_expanded_sort (args:list expr) : Lemma (get_sort (expanded args) == bool_sort) =
  match args with [] | [_] | [_; _] -> () | _ -> ()
