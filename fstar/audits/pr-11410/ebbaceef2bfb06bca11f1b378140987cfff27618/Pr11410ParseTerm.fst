module Pr11410ParseTerm
(* Model of seq::monadic::parse_term, base (recursive) vs head (get_concat worklist). *)
open FStar.List.Tot
open FStar.List.Tot.Properties

type atom = | AConst : int -> atom | AVar : int -> atom
type leaf = | Empty | Str : list int -> leaf | UnitV : int -> leaf | UnitNV | Var : int -> leaf | Other
type tree = | Concat : tree -> tree -> tree | L : leaf -> tree

(* per-leaf result: (accepted, atoms pushed) ; mirrors is_string / is_unit&&is_value / is_var / reject *)
let leaf_res (l:leaf) : bool & list atom =
  match l with
  | Empty -> (true, [])
  | Str cs -> (true, map AConst cs)
  | UnitV c -> (true, [AConst c])
  | Var v -> (true, [AVar v])
  | UnitNV -> (false, [])
  | Other -> (false, [])

(* BASE: recursive parse_term with all_of short-circuit; atoms pushed before failure persist *)
let rec old_parse (t:tree) : bool & list atom =
  match t with
  | L l -> leaf_res l
  | Concat a b ->
    let (ba, xa) = old_parse a in
    if ba then (let (bb, xb) = old_parse b in (bb, xa @ xb)) else (false, xa)

(* HEAD: get_concat worklist (push e2 then e1; skip empty) *)
let rec size (t:tree) : nat = match t with L _ -> 1 | Concat a b -> 1 + size a + size b
let rec tsize (l:list tree) : nat = match l with [] -> 0 | x::r -> size x + tsize r

let rec flat (todo:list tree) (acc:list leaf) : Tot (list leaf) (decreases (tsize todo)) =
  match todo with
  | [] -> rev acc
  | Concat a b :: r -> flat (a :: b :: r) acc
  | L Empty :: r -> flat r acc
  | L l :: r -> flat r (l :: acc)

let rec proc (ls:list leaf) : bool & list atom =
  match ls with
  | [] -> (true, [])
  | l :: r ->
    let (b, xs) = leaf_res l in
    if b then (let (b2, ys) = proc r in (b2, xs @ ys)) else (false, xs)

let new_parse (t:tree) : bool & list atom = proc (flat [t] [])

(* reference spec of flatten *)
let rec fl (t:tree) : list leaf =
  match t with
  | L Empty -> [] | L l -> [l] | Concat a b -> fl a @ fl b
let rec fls (l:list tree) : list leaf = match l with [] -> [] | x::r -> fl x @ fls r

(* Obligation 1: worklist equals ordered leaf flattening, no Concat, no Empty retained *)
let rec flat_spec (todo:list tree) (acc:list leaf)
  : Lemma (ensures flat todo acc == rev acc @ fls todo) (decreases (tsize todo)) =
  match todo with
  | [] -> ()
  | Concat a b :: r -> flat_spec (a :: b :: r) acc; append_assoc (fl a) (fl b) (fls r)
  | L Empty :: r -> flat_spec r acc
  | L l :: r -> flat_spec r (l :: acc); rev_append [l] acc; rev_append acc [l]; append_assoc (rev acc) [l] (fls r)

(* proc distributes over concatenation of leaf lists, including short-circuit on failure *)
let rec proc_append (xs ys:list leaf)
  : Lemma (ensures proc (xs @ ys) ==
      (let (b, a) = proc xs in
       if b then (let (b2, c) = proc ys in (b2, a @ c)) else (false, a)))
  = match xs with
  | [] -> ()
  | l :: r -> proc_append r ys;
    let (b, _) = leaf_res l in
    if b then (let (_, p) = leaf_res l in
               let (b1, q) = proc r in
               append_assoc p q (snd (proc ys)))
    else ()

(* Obligation 2: old recursive parse == proc over ordered leaf flattening *)
let rec old_eq_proc (t:tree) : Lemma (ensures old_parse t == proc (fl t)) =
  match t with
  | L Empty -> ()
  | L l -> ()
  | Concat a b ->
    old_eq_proc a; old_eq_proc b; proc_append (fl a) (fl b);
    let (ba, xa) = proc (fl a) in
    if ba then () else ()

(* Obligation 3 (main): head behavior == base behavior (result and atoms, order, failure) *)
let parse_equiv (t:tree) : Lemma (ensures new_parse t == old_parse t) =
  flat_spec [t] []; old_eq_proc t
