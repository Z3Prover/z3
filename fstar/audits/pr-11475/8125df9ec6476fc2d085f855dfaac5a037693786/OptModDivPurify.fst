module OptModDivPurify
open FStar.Classical

(* Semantic model of mod_div_purifier: (div t k)/(mod t k), k <> 0, are replaced by
   fresh q,r constrained by D: t = k*q + r /\ 0 <= r < |k|. SMT-LIB div/mod are the
   Euclidean ones, which F* int / and % also implement (checked in T.fst). *)

let absz (k:int) : int = if k < 0 then -k else k
let defs (t k q r:int) : prop = t == k * q + r /\ 0 <= r /\ r < absz k

(* O1: the definitions hold for q = t/k, r = t%k *)
let existence (t:int) (k:int{k <> 0}) : Lemma (defs t k (t / k) (t % k)) = ()

(* O2: the definitions determine q and r uniquely *)
let uniqueness (t:int) (k:int{k <> 0}) (q r:int)
  : Lemma (requires defs t k q r) (ensures q == t / k /\ r == t % k)
  = let q' = t / k in let r' = t % k in
    FStar.Math.Lemmas.euclidean_division_definition t k;
    // k*(q-q') = r'-r with |r'-r| < |k|
    let d = q - q' in
    assert (k * d == r' - r);
    if d > 0 then (FStar.Math.Lemmas.lemma_mult_le_left (absz k) 1 d;
                   assert (absz k * d >= absz k);
                   assert (absz k * d == (if k < 0 then -(k*d) else k*d)))
    else if d < 0 then (FStar.Math.Lemmas.lemma_mult_le_left (absz k) 1 (-d);
                   assert (absz k * (-d) >= absz k);
                   assert (absz k * (-d) == (if k < 0 then k*d else -(k*d))))
    else ()

let uniq_all (t:int) (k:int{k <> 0})
  : Lemma (forall q r. defs t k q r ==> (q == t / k /\ r == t % k))
  = introduce forall q r. defs t k q r ==> (q == t / k /\ r == t % k)
    with (move_requires (uniqueness t k q) r)

(* O3: quantifier translation for body b over the original variable x. *)
let exists_equiv (#a:Type) (t:a -> int) (k:int{k <> 0}) (b:a -> int -> int -> prop) (x:a)
  : Lemma ((exists q r. defs (t x) k q r /\ b x q r) <==> b x (t x / k) (t x % k))
  = existence (t x) k; uniq_all (t x) k

let forall_equiv (#a:Type) (t:a -> int) (k:int{k <> 0}) (b:a -> int -> int -> prop) (x:a)
  : Lemma ((forall q r. defs (t x) k q r ==> b x q r) <==> b x (t x / k) (t x % k))
  = existence (t x) k; uniq_all (t x) k
