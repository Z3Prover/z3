module Pr11551ConcatFold
open FStar.List.Tot
module L = FStar.Math.Lemmas

(* bit-vector value of width w *)
type bv = { v: nat; w: nat }
let wf (x:bv) = x.v < pow2 x.w

(* binary concat: high operand first *)
let cat (a b:bv) : bv = { v = a.v * pow2 b.w + b.v; w = a.w + b.w }

let cat_wf (a b:bv) : Lemma (requires wf a /\ wf b) (ensures wf (cat a b)) =
  L.pow2_plus a.w b.w;
  assert (a.v * pow2 b.w + b.v < pow2 a.w * pow2 b.w)

let cat_assoc (a b c:bv) : Lemma (cat (cat a b) c == cat a (cat b c)) =
  L.pow2_plus b.w c.w;
  L.distributivity_add_left (a.v * pow2 b.w) b.v (pow2 c.w);
  L.paren_mul_right a.v (pow2 b.w) (pow2 c.w)

(* C++ patch: ((x0 x1) x2) ... left fold *)
let rec foldl_cat (acc:bv) (l:list bv) : Tot bv (decreases l) =
  match l with [] -> acc | x::t -> foldl_cat (cat acc x) t

(* n-ary reference semantics: right-nested concat *)
let rec nary (x:bv) (l:list bv) : Tot bv (decreases l) =
  match l with [] -> x | y::t -> cat x (nary y t)

let rec cat_nary (a x:bv) (l:list bv)
  : Lemma (ensures cat a (nary x l) == nary (cat a x) l) (decreases l) =
  match l with
  | [] -> ()
  | y::t -> cat_assoc a x (nary y t)

let rec fold_correct (acc:bv) (l:list bv)
  : Lemma (ensures foldl_cat acc l == nary acc l) (decreases l) =
  match l with
  | [] -> ()
  | y::t ->
    fold_correct (cat acc y) t;
    cat_nary acc y t

let rec nary_wf (x:bv) (l:list bv)
  : Lemma (requires wf x /\ (forall y. memP y l ==> wf y)) (ensures wf (nary x l)) (decreases l) =
  match l with
  | [] -> ()
  | y::t -> nary_wf y t; cat_wf x (nary y t)

(* the patch applies only when num_args > 2: the two initial args consumed are safe *)
let patch_arity_ok (l:list bv) : Lemma (requires length l > 2) (ensures Cons? l /\ Cons? (Cons?.tl l)) = ()
