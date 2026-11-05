module Pr11421Head7303
(* Model of the linear Real->FP rounding encoding in
   fpa2bv_converter::mk_to_fp_real (head 7303aad4, fpa2bv_converter.cpp lines
   ~3008-3114). Quantities are integers in units of min_subnormal; bit fields are
   functions nat -> bool (bit i of r_exp / r_sig). k = sbits-1 >= 1. *)

let rec pow2 (n:nat) : Tot pos = if n = 0 then 1 else 2 * pow2 (n-1)

let rec pow2_add (a b:nat) : Lemma (ensures pow2 (a+b) == pow2 a * pow2 b) (decreases a) =
  if a = 0 then () else pow2_add (a-1) b

let rec pow2_mono (a b:nat) : Lemma (requires a <= b) (ensures pow2 a <= pow2 b) (decreases b) =
  if a = b then () else pow2_mono a (b-1)

type bits = nat -> bool
let b2n (b:bool) : nat = if b then 1 else 0

(* value of the low n bits: sum bit_i * 2^i *)
let rec fval (f:bits) (n:nat) : nat =
  if n = 0 then 0 else fval f (n-1) + b2n (f (n-1)) * pow2 (n-1)

let rec fval_bound (f:bits) (n:nat) : Lemma (ensures fval f n <= pow2 n - 1) (decreases n) =
  if n = 0 then () else fval_bound f (n-1)

(* C++ loop: gap = gap or gap*2^(2^i) when bit i set, scale squared each step.
   Result in units of min_sub/2 (initial gap_up = min_subnormal/2). *)
let rec scale (e:bits) (n:nat) : pos =
  if n = 0 then 1 else scale e (n-1) * (if e (n-1) then pow2 (pow2 (n-1)) else 1)

(* O1: the bit-conditioned multiplications compute exactly 2^(exponent field) *)
let rec scale_correct (e:bits) (n:nat)
  : Lemma (ensures scale e n == pow2 (fval e n)) (decreases n) =
  if n = 0 then () else begin
    scale_correct e (n-1);
    if e (n-1) then pow2_add (fval e (n-1)) (pow2 (n-1)) else ()
  end

(* O1': intermediate loop assertion gap_up >= min_gap holds (factor >= 1) *)
let rec scale_ge1 (e:bits) (n:nat) : Lemma (ensures scale e n >= 1) (decreases n) =
  if n = 0 then () else scale_ge1 e (n-1)

(* ulp in units of min_sub; C++: ite(exp=0, min_sub, min_sub/2 * scale).
   Doubled to stay integral: 2*ulp. *)
let twice_gap_up (ev:nat) (sc:pos) : pos = if ev = 0 then 2 else sc
let ulp (ev:nat) : pos = if ev = 0 then 1 else pow2 (ev-1)

let gap_up_is_ulp (e:bits) (n:nat) : Lemma (ensures
    twice_gap_up (fval e n) (scale e n) == 2 * ulp (fval e n)) =
  scale_correct e n

(* O2: abs_r = base + sum bit_i * 2^i * gap equals the IEEE decoding *)
let rec acc (f:bits) (n:nat) (g:nat) : nat =
  if n = 0 then 0 else acc f (n-1) g + (if f (n-1) then pow2 (n-1) * g else 0)

let rec acc_correct (f:bits) (n:nat) (g:nat)
  : Lemma (ensures acc f n g == fval f n * g) (decreases n) =
  if n = 0 then () else acc_correct f (n-1) g

let ieee_value (k:nat) (ev fv:nat) : nat = if ev = 0 then fv else (pow2 k + fv) * ulp ev
let abs_r (k:nat) (ev:nat) (f:bits) : nat =
  let g = ulp ev in (if ev = 0 then 0 else pow2 k * g) + acc f k g

let abs_r_correct (k:nat) (ev:nat) (f:bits)
  : Lemma (ensures abs_r k ev f == ieee_value k ev (fval f k)) = acc_correct f k (ulp ev)

(* O2b: exposed range assertions base <= abs_r <= base + (2^k-1)*gap are valid *)
let range_ok (k:nat) (ev:nat) (f:bits) : Lemma (ensures
    (let g = ulp ev in let base = (if ev = 0 then 0 else pow2 k * g) in
     base <= abs_r k ev f /\ abs_r k ev f <= base + (pow2 k - 1) * g)) =
  acc_correct f k (ulp ev); fval_bound f k

(* O3: gap_down is the true distance to the predecessor, gap_up to the successor
   (k>=1, f is a valid non-max finite field for the successor claim). *)
let gap_down (ev fv:nat) : nat =
  if ev = 0 || ev = 1 || fv <> 0 then ulp ev else (if ev >= 2 then pow2 (ev-2) else 0)

let value (k:nat) (ev fv:nat) : nat = ieee_value k ev fv

let pred_dist (k:nat{k >= 1}) (ev:nat) (fv:nat{fv < pow2 k /\ ~(ev = 0 /\ fv = 0)})
  : Lemma (ensures
    (if fv > 0 then value k ev fv - value k ev (fv-1) == gap_down ev fv
     else value k ev fv - value k (ev-1) (pow2 k - 1) == gap_down ev fv)) =
  if fv > 0 then ()
  else begin
    pow2_add k (ev-1);
    if ev = 1 then () else (pow2_add (ev-2) 1; pow2_add (ev-2) k)
  end

let succ_dist (k:nat{k >= 1}) (ev:nat) (fv:nat{fv < pow2 k})
  : Lemma (ensures
    (if fv + 1 < pow2 k then value k ev (fv+1) - value k ev fv == ulp ev
     else value k (ev+1) 0 - value k ev fv == ulp ev)) =
  if fv + 1 < pow2 k then ()
  else begin
    pow2_add k ev;
    if ev = 0 then () else pow2_add k (ev-1)
  end

(* O3b: extra assertion gap_down <= gap_up *)
let gd_le_gu (ev fv:nat) : Lemma (ensures gap_down ev fv <= ulp ev) =
  if ev >= 2 then pow2_mono (ev-2) (ev-1) else ()
