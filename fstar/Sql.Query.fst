module Sql.Query

open Sql.Core

(* Higher-order scalar/predicate fields are the elaborated expression language.
   The environment explicitly supplies correlated outer rows. *)
type expression = database -> row -> row -> Tot value
type condition = database -> row -> row -> Tot truth
noeq type query =
  | Table : nat -> query
  | Literal : relation -> query
  | Where : condition -> query -> query
  | Select : list expression -> query -> query
  | Distinct : query -> query
  | UnionAll : query -> query -> query
  | Union : query -> query -> query
  | Intersect : query -> query -> query
  | Except : query -> query -> query
  | IntersectAll : query -> query -> query
  | ExceptAll : query -> query -> query
  | Join : condition -> query -> query -> query
  | LeftJoin : nat -> condition -> query -> query -> query
  | GroupBy : list scalar -> list aggregate -> query -> query
  | Aggregate : list aggregate -> query -> query
  | OrderBy : list sort_key -> query -> query
  | Slice : nat -> nat -> query -> query

let rec eval (db:database) (outer:row) (q:query) : Tot relation =
  match q with
  | Table n -> db n
  | Literal rs -> rs
  | Where p s -> select (p db outer) (eval db outer s)
  | Select es s -> project (fields (FStar.List.Tot.map (fun e -> e db outer) es)) (eval db outer s)
  | Distinct s -> distinct (eval db outer s)
  | UnionAll a b -> append (eval db outer a) (eval db outer b)
  | Union a b -> union (eval db outer a) (eval db outer b)
  | Intersect a b -> intersect (eval db outer a) (eval db outer b)
  | Except a b -> except (eval db outer a) (eval db outer b)
  | IntersectAll a b -> intersect_all (eval db outer a) (eval db outer b)
  | ExceptAll a b -> except_all (eval db outer a) (eval db outer b)
  | Join p a b -> inner_join (p db outer) (eval db outer a) (eval db outer b)
  | LeftJoin n p a b -> left_join n (p db outer) (eval db outer a) (eval db outer b)
  | GroupBy es aa s -> grouped es aa (eval db outer s)
  | Aggregate aa s -> global_aggregate aa (eval db outer s)
  | OrderBy ks s -> order_by ks (eval db outer s)
  | Slice offset count s -> take count (drop offset (eval db outer s))

let col (n:nat) : expression = fun _ _ r -> column n r
let outer_col (n:nat) : expression = fun _ outer _ -> column n outer
let lit (v:value) : expression = fun _ _ _ -> v
let equal (a b:expression) : condition =
  fun db outer r -> sql_eq (a db outer r) (b db outer r)
let conjunction (a b:condition) : condition =
  fun db outer r -> sql_and (a db outer r) (b db outer r)
let negation (p:condition) : condition = fun db outer r -> sql_not (p db outer r)
let exists_query (q:query) : condition =
  fun db _ r -> exists_rows (eval db r q)
let in_query (e:expression) (q:query) : condition =
  fun db outer r -> in_values (e db outer r) (values (column 0) (eval db r q))
let scalar_query (q:query) (db:database) (r:row) : option value =
  scalar_subquery (eval db r q)
let query_equivalent (a b:query) : prop =
  forall (db:database). bag_equal (eval db [] a) (eval db [] b)
let query_ordered_equivalent (a b:query) : prop =
  forall (db:database). ordered_equal (eval db [] a) (eval db [] b)
