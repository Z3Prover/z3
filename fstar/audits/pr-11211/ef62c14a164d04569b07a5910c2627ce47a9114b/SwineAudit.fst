module SwineAudit
module L = FStar.Math.Lemmas

(* Integer power on a natural exponent; mirrors compute_power for y >= 0. *)
let rec pow (b:int) (e:nat) : Tot int (decreases e) =
  if e = 0 then 1 else b * pow b (e - 1)

let rec pow_pos (b:int{b >= 1}) (e:nat) : Lemma (ensures pow b e >= 1) (decreases e) =
  if e = 0 then () else (pow_pos b (e-1); assert (b * pow b (e-1) >= 1 * 1))

let pow_succ_gt (b:int{b > 1}) (e:nat) : Lemma (pow b (e+1) > pow b e) =
  pow_pos b e; assert (b * pow b e >= 2 * pow b e)

let rec pow_mono_exp (b:int{b > 1}) (e1:nat) (e2:nat{e1 < e2})
  : Lemma (ensures pow b e1 < pow b e2) (decreases e2) =
  pow_succ_gt b (e2-1);
  if e1 = e2 - 1 then () else pow_mono_exp b e1 (e2-1)

(* 0 <= b1 <= b2 ==> pow b1 e <= pow b2 e ; strict if b1 < b2 and e > 0 *)
let rec pow_mono_base (b1:int{b1 >= 1}) (b2:int{b2 >= b1}) (e:nat{e > 0})
  : Lemma (ensures pow b1 e <= pow b2 e /\ (b1 < b2 ==> pow b1 e < pow b2 e)) (decreases e) =
  if e = 1 then ()
  else begin
    pow_mono_base b1 b2 (e-1);
    pow_pos b1 (e-1); pow_pos b2 (e-1);
    L.lemma_mult_le_left b1 (pow b1 (e-1)) (pow b2 (e-1));
    L.lemma_mult_le_right (pow b2 (e-1)) b1 b2;
    if b1 < b2 then begin
      assert (b1 * pow b1 (e-1) <= b1 * pow b2 (e-1));
      assert (b1 * pow b2 (e-1) < b2 * pow b2 (e-1))
    end
  end

(* Obligation M (monotonicity lemma, arith_swine::monotonicity):
   base_p > 1, exp_p > 0, base_q >= base_p, exp_q >= exp_p, and one strict
   ==> pow_q > pow_p. *)
let monotonicity_valid (bp:int) (ep:nat) (bq:int) (eq:nat)
  : Lemma (requires bp > 1 /\ ep > 0 /\ bq >= bp /\ eq >= ep /\ (bq > bp \/ eq > ep))
          (ensures pow bq eq > pow bp ep) =
  pow_mono_base bp bq ep;
  if eq > ep then begin
    pow_mono_exp bq ep eq;
    pow_mono_base bp bq ep
  end
  // eq = ep, bq > bp: strict base lemma applies directly

(* Obligation B (bounding, last case): b>1, e>1, b+e>4 ==> b^e > b*e+1 *)
let rec pow_lb (x:int{x >= 2}) (y:nat{y >= 2 /\ x + y > 4})
  : Lemma (ensures pow x y >= x * y + 2) (decreases y) =
  if y = 2 then begin
    assert (pow x 2 == x * (x * 1));
    assert (x * x >= 3 * x)
  end else if x = 2 && y = 3 then ()
  else begin
    pow_lb x (y-1);
    assert (pow x y == x * pow x (y-1));
    L.lemma_mult_le_left x (x * (y-1) + 2) (pow x (y-1));
    assert (x * (x * (y-1) + 2) >= 2 * (x * (y-1)) + 2 * x);
    assert (2 * (x*(y-1)) + 2 * x >= x * y + 2)
  end

let bounding_valid (b:int) (e:nat)
  : Lemma (requires b > 1 /\ e > 1 /\ b + e > 4) (ensures pow b e > b * e + 1) =
  pow_lb b e

(* Obligation P (prime lemma, arith_swine::prime). d is assumed prime in the
   Euclid sense; primality of the found witness is reviewed manually. *)
let euclid (d:int) =
  d >= 2 /\ (forall (a b:int). (a * b) % d = 0 ==> (a % d = 0 \/ b % d = 0))

let rec prime_valid (d:int) (b:int) (e:nat)
  : Lemma (requires euclid d)
          (ensures (pow b e % d = 0) <==> (b % d = 0 /\ e <> 0)) (decreases e) =
  if e = 0 then ()
  else begin
    L.lemma_mod_mul_distr_l b (pow b (e-1)) d;
    if e > 1 then prime_valid d b (e-1)
  end
