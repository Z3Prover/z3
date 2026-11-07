module Pr11551Concat
open FStar.List.Tot

(* Model of ast_smt2_pp.cpp concat branch: for n>2 args the printer emits
   (concat (concat a0 a1) a2) ... i.e. a left fold; n-ary concat denotes
   big-endian positional composition. Values are nat, args carry (value,width). *)
let cat (a:nat) (b:nat) (wb:nat) : nat = a * pow2 wb + b

let rec foldl_cat (acc:nat) (xs: list (nat & nat)) : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | (v,w)::t -> foldl_cat (cat acc v w) t

(* positional semantics: value of args a::xs is a * 2^(width xs) + rest *)
let rec total_w (xs: list (nat & nat)) : nat =
  match xs with [] -> 0 | (_,w)::t -> w + total_w t

let rec nary (xs: list (nat & nat)) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | (v,w)::t -> v * pow2 (total_w t) + nary t

(* Obligation A: printed left-nested binary form == n-ary semantics, for any prefix acc *)
let rec fold_correct (acc:nat) (xs: list (nat & nat))
  : Lemma (ensures foldl_cat acc xs == acc * pow2 (total_w xs) + nary xs) (decreases xs)
  = match xs with
    | [] -> ()
    | (v,w)::t ->
      fold_correct (cat acc v w) t;
      Math.Lemmas.pow2_plus w (total_w t);
      assert ((acc * pow2 w + v) * pow2 (total_w t) == acc * (pow2 w * pow2 (total_w t)) + v * pow2 (total_w t))

(* Obligation B: argument order/multiplicity preserved: printed leaves in order *)
type tree =
  | Leaf : nat -> tree
  | Cat : tree -> tree -> tree
let rec foldl_tree (acc:tree) (xs:list nat) : Tot tree (decreases xs) =
  match xs with [] -> acc | x::t -> foldl_tree (Cat acc (Leaf x)) t
let rec leaves (t:tree) : list nat =
  match t with Leaf n -> [n] | Cat a b -> leaves a @ leaves b
let rec leaves_fold (acc:tree) (xs:list nat)
  : Lemma (ensures leaves (foldl_tree acc xs) == leaves acc @ xs) (decreases xs)
  = match xs with
    | [] -> FStar.List.Tot.Properties.append_l_nil (leaves acc)
    | x::t -> leaves_fold (Cat acc (Leaf x)) t;
      FStar.List.Tot.Properties.append_assoc (leaves acc) [x] t

(* Obligation C: renamed internal div ops map injectively to distinct SMT-LIB names *)
type op = | Bsdiv | Budiv | Bsrem | Burem | Bsmod
let name_of (o:op) : string = match o with
  | Bsdiv -> "bvsdiv" | Budiv -> "bvudiv" | Bsrem -> "bvsrem"
  | Burem -> "bvurem" | Bsmod -> "bvsmod"
let name_inj (a b:op) : Lemma (name_of a = name_of b ==> a == b) = ()
