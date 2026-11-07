module Pr11551Head56f8
open FStar.List.Tot
module L = FStar.Math.Lemmas

(* Model of smt2_printer::process_app concat branch (ast_smt2_pp.cpp, guard
   is_app_of(t,bv_family_id,OP_CONCAT) && num_args > 2):
   prints (concat (concat a0 a1) a2) ... i.e. a left fold of binary concat. *)
type bv = { v: nat; w: nat }
let wf (x:bv) = x.v < pow2 x.w
let cat (a b:bv) : bv = { v = a.v * pow2 b.w + b.v; w = a.w + b.w }

(* O1: binary concat preserves well-formedness (printed binary nodes are valid BV values) *)
let cat_wf (a b:bv) : Lemma (requires wf a /\ wf b) (ensures wf (cat a b)) =
  L.pow2_plus a.w b.w;
  assert (a.v * pow2 b.w + b.v < pow2 a.w * pow2 b.w)

let cat_assoc (a b c:bv) : Lemma (cat (cat a b) c == cat a (cat b c)) =
  L.pow2_plus b.w c.w;
  L.distributivity_add_left (a.v * pow2 b.w) b.v (pow2 c.w);
  L.paren_mul_right a.v (pow2 b.w) (pow2 c.w)

let rec foldl_cat (acc:bv) (l:list bv) : Tot bv (decreases l) =
  match l with [] -> acc | x::t -> foldl_cat (cat acc x) t

(* reference n-ary semantics: right-nested concat *)
let rec nary (x:bv) (l:list bv) : Tot bv (decreases l) =
  match l with [] -> x | y::t -> cat x (nary y t)

let rec cat_nary (a x:bv) (l:list bv)
  : Lemma (ensures cat a (nary x l) == nary (cat a x) l) (decreases l) =
  match l with [] -> () | y::t -> cat_assoc a x (nary y t)

(* O2: the printed left fold denotes the n-ary concat (value and width) *)
let rec fold_correct (acc:bv) (l:list bv)
  : Lemma (ensures foldl_cat acc l == nary acc l) (decreases l) =
  match l with [] -> () | y::t -> fold_correct (cat acc y) t; cat_nary acc y t

(* O3: argument order and multiplicity preserved; the two initial *it++ reads
   are safe under num_args > 2 *)
type tree = | Leaf : nat -> tree | Cat : tree -> tree -> tree
let rec leaves (t:tree) : list nat = match t with Leaf n -> [n] | Cat a b -> leaves a @ leaves b
let rec foldl_tree (acc:tree) (xs:list nat) : Tot tree (decreases xs) =
  match xs with [] -> acc | x::t -> foldl_tree (Cat acc (Leaf x)) t
let rec leaves_fold (acc:tree) (xs:list nat)
  : Lemma (ensures leaves (foldl_tree acc xs) == leaves acc @ xs) (decreases xs) =
  match xs with
  | [] -> FStar.List.Tot.Properties.append_l_nil (leaves acc)
  | x::t -> leaves_fold (Cat acc (Leaf x)) t;
            FStar.List.Tot.Properties.append_assoc (leaves acc) [x] t
let arity_ok (#a:Type) (l:list a) : Lemma (requires length l > 2) (ensures Cons? l /\ Cons? (Cons?.tl l)) = ()
