module Sql.Core

module L = FStar.List.Tot

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10"

type truth = | Yes | No | Unknown
type value =
  | Null
  | Number : numerator:int -> denominator:pos -> value
  | Text : string -> value
type row = list value
type relation = list row
type database = nat -> Tot relation
type scalar = row -> Tot value
type predicate = row -> Tot truth

let num (n:int) : value = Number n 1
let is_null (v:value) : bool = match v with Null -> true | _ -> false
let passes (t:truth) : bool = t = Yes
let sql_not (t:truth) : truth =
  match t with Yes -> No | No -> Yes | Unknown -> Unknown
let sql_and (a b:truth) : truth =
  match a, b with
  | No, _ | _, No -> No
  | Yes, Yes -> Yes
  | _ -> Unknown
let sql_or (a b:truth) : truth =
  match a, b with
  | Yes, _ | _, Yes -> Yes
  | No, No -> No
  | _ -> Unknown
let of_bool (b:bool) : truth = if b then Yes else No

(* SQL grouping/set equality, unlike SQL =, identifies two NULLs. *)
let same_value (a b:value) : bool =
  match a, b with
  | Null, Null -> true
  | Number n d, Number m e -> n * e = m * d
  | Text s, Text t -> s = t
  | _ -> false
let sql_eq (a b:value) : truth =
  if is_null a || is_null b then Unknown else of_bool (same_value a b)
let sql_le (a b:value) : truth =
  match a, b with
  | Null, _ | _, Null -> Unknown
  | Number n d, Number m e -> of_bool (n * e <= m * d)
  | Text s, Text t -> of_bool (FStar.String.compare s t <= 0)
  | _ -> Unknown
let sql_lt (a b:value) : truth =
  sql_and (sql_le a b) (sql_not (sql_eq a b))
let sql_between (x lo hi:value) : truth =
  sql_and (sql_le lo x) (sql_le x hi)
let sql_add (a b:value) : value =
  match a, b with
  | Number n d, Number m e -> Number (n * e + m * d) (d * e)
  | _ -> Null
let sql_mul (a b:value) : value =
  match a, b with
  | Number n d, Number m e -> Number (n * m) (d * e)
  | _ -> Null
let sql_sub (a b:value) : value =
  match b with Number n d -> sql_add a (Number (-n) d) | _ -> Null
let sql_div (a b:value) : value =
  match a, b with
  | Number n d, Number m e ->
    if m > 0 then Number (n * e) (d * m)
    else if m < 0 then Number (-n * e) (d * (-m))
    else Null
  | _ -> Null
let sql_case (p:truth) (a b:value) : value = if passes p then a else b
let coalesce (a b:value) : value = if is_null a then b else a
let nullif (a b:value) : value = if passes (sql_eq a b) then Null else a

(* Patterns are elaborated first, so escaping is unambiguous. *)
type like_token = | LiteralChar : FStar.Char.char -> like_token | AnyChar | AnyString
let rec like_chars (pattern:list like_token) (text:list FStar.Char.char)
  : Tot bool (decreases (L.length pattern + L.length text)) =
  match pattern with
  | [] -> text = []
  | AnyString::rest ->
    like_chars rest text ||
    (match text with [] -> false | _::xs -> like_chars pattern xs)
  | AnyChar::rest ->
    (match text with [] -> false | _::xs -> like_chars rest xs)
  | LiteralChar c::rest ->
    (match text with [] -> false | x::xs -> c = x && like_chars rest xs)
let sql_like (v:value) (pattern:list like_token) : truth =
  match v with
  | Text s -> of_bool (like_chars pattern (FStar.String.list_of_string s))
  | _ -> Unknown

let rec column (i:nat) (r:row) : Tot value =
  match r with
  | [] -> Null
  | x::xs -> if i = 0 then x else column (i - 1) xs
let rec same_row (a b:row) : Tot bool =
  match a, b with
  | [], [] -> true
  | x::xs, y::ys -> same_value x y && same_row xs ys
  | _ -> false
let rec append (#a:Type) (xs ys:list a) : Tot (list a) =
  match xs with [] -> ys | x::rest -> x::append rest ys
let rec select (p:predicate) (rs:relation) : Tot relation =
  match rs with
  | [] -> []
  | r::rest -> if passes (p r) then r::select p rest else select p rest
let rec project (f:row -> Tot row) (rs:relation) : Tot relation =
  match rs with [] -> [] | r::rest -> f r::project f rest
let rec fields (es:list scalar) (r:row) : Tot row =
  match es with [] -> [] | e::rest -> e r::fields rest r
let rec member (r:row) (rs:relation) : Tot bool =
  match rs with [] -> false | x::xs -> same_row r x || member r xs
let rec distinct (rs:relation) : Tot relation =
  match rs with
  | [] -> []
  | r::rest -> if member r rest then distinct rest else r::distinct rest
let rec multiplicity (r:row) (rs:relation) : Tot nat =
  match rs with
  | [] -> 0
  | x::xs -> (if same_row r x then 1 else 0) + multiplicity r xs
let bag_equal (a b:relation) : prop =
  forall (r:row). multiplicity r a == multiplicity r b
let rec same_sequence (a b:relation) : Tot bool =
  match a, b with
  | [], [] -> true
  | x::xs, y::ys -> same_row x y && same_sequence xs ys
  | _ -> false
let ordered_equal (a b:relation) : prop = same_sequence a b
let equivalent (a b:database -> Tot relation) : prop =
  forall (db:database). bag_equal (a db) (b db)
let equivalent_under (invariant:database -> prop)
                     (a b:database -> Tot relation) : prop =
  forall (db:database). invariant db ==> bag_equal (a db) (b db)
let rec remove_one (r:row) (rs:relation) : Tot relation =
  match rs with
  | [] -> []
  | x::xs -> if same_row r x then xs else x::remove_one r xs
let rec except_all (a b:relation) : Tot relation (decreases b) =
  match b with [] -> a | x::xs -> except_all (remove_one x a) xs
let rec intersect_all (a b:relation) : Tot relation (decreases a) =
  match a with
  | [] -> []
  | x::xs ->
    if member x b then x::intersect_all xs (remove_one x b)
    else intersect_all xs b
let union (a b:relation) : relation = distinct (append a b)
let intersect (a b:relation) : relation =
  distinct (select (fun r -> of_bool (member r b)) a)
let except (a b:relation) : relation =
  distinct (select (fun r -> of_bool (not (member r b))) a)

let rec matches (p:predicate) (left:row) (right:relation) : Tot relation =
  match right with
  | [] -> []
  | r::rest ->
    let joined = append left r in
    if passes (p joined) then joined::matches p left rest
    else matches p left rest
let rec inner_join (p:predicate) (a b:relation) : Tot relation =
  match a with
  | [] -> []
  | r::rest -> append (matches p r b) (inner_join p rest b)
let rec nulls (width:nat) : Tot row =
  if width = 0 then [] else Null::nulls (width - 1)
let rec left_join (width:nat) (p:predicate) (a b:relation) : Tot relation =
  match a with
  | [] -> []
  | r::rest ->
    let found = matches p r b in
    append (if found = [] then [append r (nulls width)] else found)
           (left_join width p rest b)
let exists_rows (rs:relation) : truth = of_bool (rs <> [])
let rec in_values (v:value) (vs:list value) : Tot truth =
  match vs with [] -> No | x::xs -> sql_or (sql_eq v x) (in_values v xs)
let scalar_subquery (rs:relation) : option value =
  match rs with
  | [] -> Some Null
  | [r] -> (match r with [v] -> Some v | _ -> None)
  | _ -> None

noeq type aggregate =
  | CountStar
  | Count : bool -> scalar -> aggregate
  | Sum : bool -> scalar -> aggregate
  | Avg : bool -> scalar -> aggregate
  | Min : scalar -> aggregate
  | Max : scalar -> aggregate

let rec nonnull (vs:list value) : Tot (list value) =
  match vs with
  | [] -> []
  | v::rest -> if is_null v then nonnull rest else v::nonnull rest
let rec values (e:scalar) (rs:relation) : Tot (list value) =
  match rs with [] -> [] | r::rest -> e r::values e rest
let rec unique_values (vs:list value) : Tot (list value) =
  match vs with
  | [] -> []
  | v::rest ->
    if L.existsb (same_value v) rest then unique_values rest
    else v::unique_values rest
let aggregate_values (dedup:bool) (e:scalar) (rs:relation) : list value =
  let vs = nonnull (values e rs) in if dedup then unique_values vs else vs
let rec sum_zero (vs:list value) : Tot value =
  match vs with [] -> num 0 | v::rest -> sql_add v (sum_zero rest)
let sum_values (vs:list value) : value =
  if vs = [] then Null else sum_zero vs
let rec extreme (least:bool) (v:value) (vs:list value) : Tot value (decreases vs) =
  match vs with
  | [] -> v
  | x::xs ->
    extreme least
      (if passes (if least then sql_lt x v else sql_lt v x) then x else v) xs
let eval_aggregate (a:aggregate) (rs:relation) : value =
  match a with
  | CountStar -> num (L.length rs)
  | Count d e -> num (L.length (aggregate_values d e rs))
  | Sum d e -> sum_values (aggregate_values d e rs)
  | Avg d e ->
    let vs = aggregate_values d e rs in
    sql_div (sum_values vs) (num (L.length vs))
  | Min e ->
    (match aggregate_values false e rs with [] -> Null | x::xs -> extreme true x xs)
  | Max e ->
    (match aggregate_values false e rs with [] -> Null | x::xs -> extreme false x xs)
let rec aggregates (aa:list aggregate) (rs:relation) : Tot row =
  match aa with [] -> [] | a::rest -> eval_aggregate a rs::aggregates rest rs
let keys (es:list scalar) (rs:relation) : relation =
  distinct (project (fields es) rs)
let group_members (es:list scalar) (k:row) (rs:relation) : relation =
  select (fun r -> of_bool (same_row (fields es r) k)) rs
let grouped (es:list scalar) (aa:list aggregate) (rs:relation) : relation =
  project (fun k -> append k (aggregates aa (group_members es k rs))) (keys es rs)
let global_aggregate (aa:list aggregate) (rs:relation) : relation =
  [aggregates aa rs]

noeq type sort_key = { expression:scalar; ascending:bool; nulls_first:bool }
let key_compare (k:sort_key) (a b:row) : int =
  let x = k.expression a in
  let y = k.expression b in
  if same_value x y then 0
  else if is_null x then (if k.nulls_first then -1 else 1)
  else if is_null y then (if k.nulls_first then 1 else -1)
  else if passes (sql_lt x y) then (if k.ascending then -1 else 1)
  else (if k.ascending then 1 else -1)
let rec compare_rows (ks:list sort_key) (a b:row) : Tot int =
  match ks with
  | [] -> 0
  | k::rest -> let c = key_compare k a b in if c = 0 then compare_rows rest a b else c
let rec insert (ks:list sort_key) (r:row) (rs:relation) : Tot relation =
  match rs with
  | [] -> [r]
  | x::xs -> if compare_rows ks r x <= 0 then r::rs else x::insert ks r xs
let rec order_by (ks:list sort_key) (rs:relation) : Tot relation =
  match rs with [] -> [] | r::rest -> insert ks r (order_by ks rest)
let rec take (n:nat) (rs:relation) : Tot relation =
  match rs with [] -> [] | x::xs -> if n = 0 then [] else x::take (n - 1) xs
let rec drop (n:nat) (rs:relation) : Tot relation =
  match rs with [] -> [] | _::xs -> if n = 0 then rs else drop (n - 1) xs
