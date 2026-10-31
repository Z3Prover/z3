module Pr11421ToFpReal
(* Semantic audit of the bit-based ULP/magnitude encoding in
   fpa2bv_converter::mk_to_fp_real (symbolic real branch), PR 11421 head
   4f554c5f6edcc22cca056032c3cb6377b656d572. Self-contained; no admits. *)
module L = FStar.Math.Lemmas

let bit (x:nat) (i:nat) : nat = (x / pow2 i) % 2

(* sum_{i(n} bit_i(x) * 2^i : the C++ loops' conditional weights *)
let rec bsum (n:nat) (x:nat) : nat =
  if n = 0 then 0 else bsum (n-1) x + bit x (n-1) * pow2 (n-1)

let lem_step (n:pos) (x:nat)
  : Lemma (x % pow2 n == x % pow2 (n-1) + bit x (n-1) * pow2 (n-1))
  = L.pow2_plus (n-1) 1;
    L.modulo_division_lemma x (pow2 (n-1)) 2;
    L.euclidean_division_definition (x % pow2 n) (pow2 (n-1));
    L.modulo_modulo_lemma x (pow2 (n-1)) 2

let rec bsum_is_mod (n:nat) (x:nat) : Lemma (ensures bsum n x == x % pow2 n) (decreases n)
  = if n = 0 then ()
    else (bsum_is_mod (n-1) x; lem_step n x)

(* O1: with e < 2^n, the sum equals e (exponent field / significand field decode). *)
let o1_bits_decode (n:nat) (x:nat{x < pow2 n}) : Lemma (bsum n x == x)
  = bsum_is_mod n x; L.small_mod x (pow2 n)

(* The ULP loop multiplies by 2^(2^i) for each set bit i, so the exponent of the
   resulting power of two is bsum n e. *)
let rec ulp_exp (n:nat) (e:nat) : nat =
  if n = 0 then 0 else ulp_exp (n-1) e + (if bit e (n-1) = 1 then pow2 (n-1) else 0)

let rec ulp_exp_is_bsum (n:nat) (e:nat) : Lemma (ensures ulp_exp n e == bsum n e) (decreases n)
  = if n = 0 then () else ulp_exp_is_bsum (n-1) e

let bit01 (x:nat) (i:nat) : Lemma (bit x i = 0 \/ bit x i = 1) = ()

let o1_ulp_exponent (n:nat) (e:nat{e < pow2 n}) : Lemma (ulp_exp n e == e)
  = ulp_exp_is_bsum n e; o1_bits_decode n e

(* Units: half of the minimum subnormal (the C++ initial gap_up = min_subnormal/2).
   ulp(e) = 1 for e = 0 is replaced by min_subnormal = 2 units;
   for e )= 1, ulp(e) = 2^e units (= min_subnormal * 2^(e-1)). *)
let ulp (e:nat) : pos = if e = 0 then 2 else pow2 e

(* Magnitude in half-min-subnormal units, as built by the C++ encoding:
   base + (sum of set fraction-bit weights) * gap_up, base = 2^(sbits-1)*gap_up (normal) or 0. *)
let value (p:nat) (e:nat) (s:nat) : nat =
  let base = if e = 0 then 0 else pow2 p * ulp e in
  base + bsum p s * ulp e

(* Intended IEEE value: subnormal s*ms ; normal (2^p + s) * 2^(e-1) * ms *)
let ieee (p:nat) (e:nat) (s:nat) : nat =
  if e = 0 then s * 2 else (pow2 p + s) * pow2 e

(* O2: the encoded magnitude equals the IEEE magnitude, and lies within the
   asserted bounds base <= abs_r <= base + (2^p-1)*gap_up. *)
let o2_value_decode (p:nat) (e:nat) (s:nat{s < pow2 p})
  : Lemma (value p e s == ieee p e s /\
           value p e s >= (if e = 0 then 0 else pow2 p * ulp e) /\
           value p e s <= (if e = 0 then 0 else pow2 p * ulp e) + (pow2 p - 1) * ulp e)
  = o1_bits_decode p s

(* O3: spacing. gap_down as chosen by the C++ guard
   (exp==0 || exp==1 || sig!=0 ? gap_up : gap_up/2) is the distance to the
   predecessor float. Half units are used, so gap_up/2 is exact for e >= 2
   (ulp e = 2^e is even); gap_down for e<=1 is ulp(e) (not halved). *)
let gap_down (p:nat) (e:nat) (s:nat) : nat =
  if e = 0 || e = 1 || s <> 0 then ulp e else ulp e / 2

let pred_ieee (p:pos) (e:pos) (s:nat{s < pow2 p}) : nat =
  if s > 0 then ieee p e (s-1)
  else ieee p (e-1) (pow2 p - 1)

let o3_predecessor_gap (p:pos) (e:pos) (s:nat{s < pow2 p})
  : Lemma (ieee p e s - gap_down p e s == pred_ieee p e s)
  = if s > 0 then ()
    else if e = 1 then ()
    else begin
      L.pow2_plus 1 (e-1);
      assert (pow2 e == 2 * pow2 (e-1));
      assert (pow2 (e-1) == 2 * pow2 (e-2));
      assert (ulp e / 2 == pow2 (e-1));
      assert (ieee p e 0 == pow2 p * pow2 e);
      assert (ieee p (e-1) (pow2 p - 1) == (pow2 p + pow2 p - 1) * pow2 (e-1))
    end
