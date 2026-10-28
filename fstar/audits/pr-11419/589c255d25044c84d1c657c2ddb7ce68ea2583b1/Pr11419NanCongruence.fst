module Pr11419NanCongruence
(* Model of fp(sgn,exp,sig) for Float16 (eb=5, sb=11): sgn in {0,1}, exp in [0,31], sig in [0,1023].
   Models the lemma added in theory_fpa::relevant_eh: isNaN_bits(n) ==> n = NaN. *)
type fpv = | NaN | Inf : bool -> fpv | Fin : bool -> int -> int -> fpv

let is_nan_bits (e s:int) : bool = e = 31 && s <> 0

(* SMT-LIB semantics of the fp constructor on raw bits *)
let mk_fp (sg:bool) (e s:int) : fpv =
  if is_nan_bits e s then NaN
  else if e = 31 then Inf sg
  else Fin sg e s

(* O1: the asserted implication is sound: guard => fp(...) = NaN *)
let o1 (sg:bool) (e s:int) : Lemma (is_nan_bits e s ==> mk_fp sg e s == NaN) = ()

(* O2: congruence: any two NaN-bit patterns (any sign/payload) denote equal values *)
let o2 (sg1 sg2:bool) (e1 s1 e2 s2:int)
  : Lemma (requires is_nan_bits e1 s1 /\ is_nan_bits e2 s2)
          (ensures mk_fp sg1 e1 s1 == mk_fp sg2 e2 s2) = ()

(* O3: guard is exact: the lemma does not fire on non-NaN bits, so those stay distinct *)
let o3 (sg:bool) (e s:int) : Lemma (requires ~(is_nan_bits e s)) (ensures mk_fp sg e s =!= NaN) = ()

(* Regression witnesses: 0xffff, 0x7e02, 0x7c01, 0xfe00 are NaN; 0x3c00, 0x4000 are not *)
let dec (b:nat{b < 65536}) : fpv = mk_fp (b / 32768 = 1) ((b / 1024) % 32) (b % 1024)
let w1 () : Lemma (dec 0xffff == NaN /\ dec 0x7e02 == NaN /\ dec 0x7c01 == NaN /\ dec 0xfe00 == NaN) = ()
let w2 () : Lemma (dec 0x3c00 =!= NaN /\ dec 0x4000 =!= NaN /\ dec 0x3c00 =!= dec 0x4000) = ()
