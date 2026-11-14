module ArithCharge
(* Model of imp::arithmetic_checkpoint (PR 11700 head 0dd4af3, polynomial.cpp ~2578-2585).
   Mathematical integers; unsigned wrap of bitsize is not modeled (see report). *)
let uint_max : int = 4294967295

let words (bits:int{bits >= 1}) : int = 1 + (bits - 1) / 32
let cost (ba:int{ba>=1}) (bb:int{bb>=1}) : int = words ba * words bb
let clamp (c:int) : int = if c < uint_max then c else uint_max
let charge (ba:int{ba>=1}) (bb:int{bb>=1}) : int = clamp (cost ba bb)

(* O1: no unsigned underflow in (bitsize-1) and words >= 1 *)
let o1 (b:int{b>=1}) : Lemma (words b >= 1 /\ (b-1) >= 0) = ()

(* O2: charged cost always fits in unsigned and is >= 1 (every guarded coefficient op costs something) *)
let o2 (ba:int{ba>=1}) (bb:int{bb>=1}) : Lemma (charge ba bb >= 1 /\ charge ba bb <= uint_max) = ()

(* O3: monotone in operand size; 4096-bit coefficients (the PR test) cost 129*129 units, vs 1 for small *)
let o3 (ba:int{ba>=1}) (bb:int{bb>=1}) (ba2:int{ba2>=ba}) : Lemma (charge ba bb <= charge ba2 bb) =
  FStar.Math.Lemmas.lemma_div_le (ba-1) (ba2-1) 32;
  FStar.Math.Lemmas.lemma_mult_le_right (words bb) (words ba) (words ba2)
let _ = assert (charge 1 1 == 1)
let _ = assert (charge 4097 4097 == 129*129)
