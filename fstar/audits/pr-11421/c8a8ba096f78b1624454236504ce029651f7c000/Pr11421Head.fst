module Pr11421Head
open FStar.Math.Lemmas

(* Units: one unit = min_subnormal/2. *)
let bit (x:nat) (k:nat) : nat = (x / pow2 k) % 2

(* Source loop: gap = 1 unit; for bit i of exp, gap *= 2^(2^i). Prefix of k bits. *)
let rec gap_loop (e:nat) (k:nat) : Tot pos (decreases k) =
  if k = 0 then 1
  else let g = gap_loop e (k-1) in
       if bit e (k-1) = 1 then pow2 (pow2 (k-1)) * g else g

(* Source loop: abs_r fraction sum  sum_i bit_i(sig) * 2^i (coefficient weight), prefix k *)
let rec frac_loop (s:nat) (k:nat) : Tot nat (decreases k) =
  if k = 0 then 0
  else frac_loop s (k-1) + (if bit s (k-1) = 1 then pow2 (k-1) else 0)

let bit_split (x:nat) (k:nat)
  : Lemma (x % pow2 (k+1) = x % pow2 k + bit x k * pow2 k) =
  pow2_plus k 1;
  lemma_div_mod x (pow2 k);
  modulo_modulo_lemma x (pow2 k) 2;
  assert (pow2 (k+1) = pow2 k * 2);
  modulo_division_lemma x (pow2 k) 2;
  euclidean_division_definition (x % pow2 (k+1)) (pow2 k);
  small_modulo_lemma_1 (x % pow2 k) (pow2 k);
  modulo_modulo_lemma x (pow2 k) 2

(* O1: the bit-conditioned constant scaling computes 2^(e mod 2^k) *)
let rec o1_gap (e:nat) (k:nat) : Lemma (ensures gap_loop e k = pow2 (e % pow2 k)) (decreases k) =
  if k = 0 then ()
  else begin
    o1_gap e (k-1);
    bit_split e (k-1);
    pow2_plus (e % pow2 (k-1)) (bit e (k-1) * pow2 (k-1));
    if bit e (k-1) = 1 then () else ()
  end

(* O2a: the conditional linear sum recovers the significand field *)
let rec o2_frac (s:nat) (k:nat) : Lemma (ensures frac_loop s k = s % pow2 k) (decreases k) =
  if k = 0 then ()
  else begin o2_frac s (k-1); bit_split s (k-1) end

(* Units of min_subnormal/2. Source: gap_up = (e=0 ? 2 : gap_loop e ebits),
   base = (e=0 ? 0 : 2^(sbits-1)*gap_up), abs_r = base + frac_loop s (sbits-1) * gap_up. *)
let gap_up (eb:pos) (e:nat{e < pow2 eb}) : pos = if e = 0 then 2 else gap_loop e eb
let base (eb:pos) (sb:pos) (e:nat{e < pow2 eb}) : nat = if e = 0 then 0 else pow2 (sb-1) * gap_up eb e
let abs_r (eb:pos) (sb:pos) (e:nat{e < pow2 eb}) (s:nat) : nat = base eb sb e + frac_loop s (sb-1) * gap_up eb e

(* IEEE magnitude in units of min_subnormal: subnormal f; normal (2^(sb-1)+f)*2^(e-1). *)
let ieee_mag (sb:pos) (e:nat) (f:nat) : nat = if e = 0 then f else (pow2 (sb-1) + f) * pow2 (e-1)

(* O1': gap_up = 2 * ulp in half-units, ulp = 2^(max(e,1)-1) min_subnormals *)
let o1_ulp (eb:pos) (e:nat{e < pow2 eb})
  : Lemma (gap_up eb e = (if e = 0 then 2 else 2 * pow2 (e-1))) =
  if e = 0 then () else begin
    o1_gap e eb; small_modulo_lemma_1 e (pow2 eb); pow2_plus 1 (e-1) end

(* O2: the encoded magnitude equals the IEEE magnitude (x2 for half-units) for every fraction field *)
let o2_value (eb:pos) (sb:pos{sb >= 2}) (e:nat{e < pow2 eb}) (s:nat{s < pow2 (sb-1)})
  : Lemma (abs_r eb sb e s = 2 * ieee_mag sb e s) =
  o1_ulp eb e; o2_frac s (sb-1); small_modulo_lemma_1 s (pow2 (sb-1))

(* O3: asserted bounds are valid: base <= abs_r <= base + (2^(sb-1)-1)*gap, gap_up >= min_gap(=1) *)
let o3_bounds (eb:pos) (sb:pos{sb >= 2}) (e:nat{e < pow2 eb}) (s:nat{s < pow2 (sb-1)})
  : Lemma (base eb sb e <= abs_r eb sb e s /\
           abs_r eb sb e s <= base eb sb e + (pow2 (sb-1) - 1) * gap_up eb e /\
           gap_up eb e >= 1) =
  o2_frac s (sb-1); small_modulo_lemma_1 s (pow2 (sb-1));
  FStar.Math.Lemmas.lemma_mult_le_right (gap_up eb e) s (pow2 (sb-1) - 1)

(* Concrete sanity instances *)
let _ = assert_norm (ieee_mag 24 1 0 = pow2 23 /\ ieee_mag 24 0 5 = 5)
