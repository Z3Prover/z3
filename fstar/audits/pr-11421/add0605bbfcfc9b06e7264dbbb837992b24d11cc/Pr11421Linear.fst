module Pr11421Linear
(* Model of the linear encoding in fpa2bv_converter::mk_to_fp_real (head add0605b).
   All quantities are integers in units of min_subnormal. Bit fields are modeled as
   functions nat -> bool (bit i), as the C++ extracts bit i of r_exp / r_sig. *)

let rec pow2 (n:nat) : Tot pos = if n = 0 then 1 else 2 * pow2 (n-1)

let rec pow2_add (a b:nat) : Lemma (ensures pow2 (a+b) == pow2 a * pow2 b) (decreases a) =
  if a = 0 then () else pow2_add (a-1) b

let rec pow2_mono (a b:nat) : Lemma (requires a <= b) (ensures pow2 a <= pow2 b) (decreases b) =
  if a = b then () else pow2_mono a (b-1)

type bits = nat -> bool
let b2n (b:bool) : nat = if b then 1 else 0

(* field value: sum_{i(n} bit_i * 2^i  (loop "weight *= 2" in C++) *)
let rec fval (f:bits) (n:nat) : nat = if n = 0 then 0 else fval f (n-1) + b2n (f (n-1)) * pow2 (n-1)

(* O1a: field value is within [0, 2^n - 1]  (max_coefficient = weight-1 bound) *)
let rec fval_bound (f:bits) (n:nat) : Lemma (ensures fval f n <= pow2 n - 1) (decreases n) =
  if n = 0 then () else fval_bound f (n-1)

(* exponent-scaling loop: factor_i = 2^(2^i) multiplied iff bit i is set *)
let rec scale (e:bits) (n:nat) : pos = if n = 0 then 1 else scale e (n-1) * (if e (n-1) then pow2 (pow2 (n-1)) else 1)

(* O1b: the conditional constant multiplications compute exactly 2^(exponent field value) *)
let rec scale_correct (e:bits) (n:nat) : Lemma (ensures scale e n == pow2 (fval e n)) (decreases n) =
  if n = 0 then () else begin
    scale_correct e (n-1);
    if e (n-1) then pow2_add (fval e (n-1)) (pow2 (n-1)) else ()
  end

(* ulp(e) = min_sub * 2^(e-1) for e)=1, min_sub for e=0; C++: gap_up starts at min_sub/2,
   multiplied by scale, then ite(e=0, min_sub, .). Use 2*ulp to stay integral. *)
let twice_gap_up (ev:nat) : pos = if ev = 0 then 2 else pow2 ev   (* = 2*ulp(ev) *)
let ulp (ev:nat) : pos = if ev = 0 then 1 else pow2 (ev-1)

let gap_up_matches (e:bits) (n:nat) : Lemma (ensures
   (let ev = fval e n in
    (if ev = 0 then 2 else scale e n) == twice_gap_up ev /\ twice_gap_up ev == 2 * ulp ev)) =
  scale_correct e n

(* O2: magnitude abs_r = base + sum bit_i * 2^i * gap_up, base = ite(e=0, 0, 2^k * gap_up).
   Equals (hidden + F)*ulp for normals and F*ulp for subnormals, i.e. IEEE decoding. *)
let value (k:nat) (ev fv:nat) : nat = if ev = 0 then fv else (pow2 k + fv) * ulp ev

let rec acc (f:bits) (n:nat) (g:nat) : nat =
  if n = 0 then 0 else acc f (n-1) g + (if f (n-1) then pow2 (n-1) * g else 0)

let rec acc_correct (f:bits) (n:nat) (g:nat) : Lemma (ensures acc f n g == fval f n * g) (decreases n) =
  if n = 0 then () else acc_correct f (n-1) g

let abs_r (k:nat) (ev:nat) (f:bits) : nat =
  let g = ulp ev in
  (if ev = 0 then 0 else pow2 k * g) + acc f k g

let abs_r_correct (k:nat) (ev:nat) (f:bits) : Lemma (ensures abs_r k ev f == value k ev (fval f k)) =
  acc_correct f k (ulp ev)

(* O2b: exposed range assertions base <= abs_r <= base + (2^k-1)*gap_up hold *)
let range_ok (k:nat) (ev:nat) (f:bits) : Lemma (ensures
  (let g = ulp ev in let base = (if ev = 0 then 0 else pow2 k * g) in
   base <= abs_r k ev f /\ abs_r k ev f <= base + (pow2 k - 1) * g)) =
  acc_correct f k (ulp ev); fval_bound f k

(* O3: gap_down / gap_up are the true distances to neighbours (k = sbits-1 >= 1).
   gap_down = ite(e=0 \/ e=1 \/ f<>0, ulp, ulp/2); check predecessor and successor. *)
let gap_down (ev fv:nat) : nat = if ev = 0 || ev = 1 || fv <> 0 then ulp ev else (if ev >= 2 then pow2 (ev-2) else 0)

let pred_dist (k:nat{k >= 1}) (ev:nat) (fv:nat{fv < pow2 k /\ ~(ev = 0 /\ fv = 0)}) :
  Lemma (ensures
    (if fv > 0 then value k ev fv - value k ev (fv-1) == gap_down ev fv
     else value k ev fv - value k (ev-1) (pow2 k - 1) == gap_down ev fv)) =
  if fv > 0 then ()
  else begin
    pow2_add k (ev-1);
    if ev = 1 then () else begin
      pow2_add (ev-2) 1; pow2_add (ev-2) k
    end
  end

let succ_dist (k:nat{k >= 1}) (ev:nat) (fv:nat{fv < pow2 k}) :
  Lemma (ensures
    (if fv + 1 < pow2 k then value k ev (fv+1) - value k ev fv == ulp ev
     else value k (ev+1) 0 - value k ev fv == ulp ev)) =
  if fv + 1 < pow2 k then () else begin
    pow2_add k ev;
    if ev = 0 then () else pow2_add k (ev-1)
  end

(* gap_down <= gap_up (the extra assertion) *)
let gd_le_gu (ev fv:nat) : Lemma (ensures gap_down ev fv <= ulp ev) =
  if ev >= 2 then pow2_mono (ev-2) (ev-1) else ()
