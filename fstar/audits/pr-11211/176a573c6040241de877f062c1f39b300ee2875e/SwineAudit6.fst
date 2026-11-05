module SwineAudit6
(* PR 11211 head 176a573c: arith_swine.cpp real_power_axioms (12-57),
   check_real_power (59-99), check_model/compute_power (111-156).
   Integers model the ordered field where only order/injectivity is needed. *)

let rec pow (b:int) (e:nat) : int = if e = 0 then 1 else b * pow b (e-1)

let rec pow_nonneg (a:nat) (n:nat) : Lemma (ensures pow a n >= 0) (decreases n) =
  if n = 0 then () else (pow_nonneg a (n-1); FStar.Math.Lemmas.nat_times_nat_is_nat a (pow a (n-1)))
let rec pow_pos (a:pos) (n:nat) : Lemma (ensures pow a n > 0) (decreases n) =
  if n = 0 then () else (pow_pos a (n-1); FStar.Math.Lemmas.pos_times_pos_is_pos a (pow a (n-1)))
let rec mono (a b:nat) (n:pos) : Lemma (requires a < b) (ensures pow a n < pow b n) (decreases n) =
  if n = 1 then ()
  else begin
    mono a b (n-1); pow_nonneg a (n-1); pow_pos b (n-1);
    FStar.Math.Lemmas.lemma_mult_le_right (pow a (n-1)) a b;
    FStar.Math.Lemmas.lemma_mult_lt_left b (pow a (n-1)) (pow b (n-1))
  end
let inj_nonneg (a b:nat) (n:pos) : Lemma (requires pow a n = pow b n) (ensures a = b) =
  if a < b then mono a b n else if b < a then mono b a n else ()
let rec pow_neg (a:nat) (n:nat) : Lemma (ensures pow (-a) n = (if n % 2 = 0 then pow a n else - (pow a n))) (decreases n) =
  if n = 0 then () else pow_neg a (n-1)

(* ---- Obligation A1: scalar axioms never force conflicting values (0<->p=0, 1, p>0, p=0 for negative base).
   Value classes of p: PZero, POne, PPos. Each axiom is a constraint set on p. *)
type sgn =
  | SNeg
  | SZero
  | SPos
let forced_zero (xs:sgn) (y_zero:bool) (x_is_one:bool) (neg_undef:bool) (zero_exp:bool) : bool =
  (xs = SZero && not y_zero) || (xs = SNeg && neg_undef)
let forced_one (xs:sgn) (y_zero:bool) (x_is_one:bool) : bool = y_zero || (x_is_one && xs = SPos)
let forced_pos (xs:sgn) : bool = (xs = SPos)
(* x=1 implies Pos; exactly the axiom premises. No input forces two incompatible classes. *)
let a1 (xs:sgn) (y_zero x_is_one neg_undef:bool)
  : Lemma (requires (x_is_one ==> xs = SPos) /\ (neg_undef ==> not y_zero))
          (ensures ~(forced_zero xs y_zero x_is_one neg_undef false /\ forced_one xs y_zero x_is_one)
                /\ ~(forced_zero xs y_zero x_is_one neg_undef false /\ forced_pos xs))
  = ()
(* 0^0 = 1 is the only overlap of premises (x=0,y=0): zero-base axiom requires y<>0, so it is excluded. *)

(* ---- Obligation A2: root graph x^(m/n), n>=2 uniquely determines p
   even n: (x>=0 -> p^n = x^m /\ p>=0) unique; odd n: p^n = X unique over all integers. *)
let even_unique (k1 k2:nat) (n:pos) : Lemma (requires pow k1 n = pow k2 n) (ensures k1 = k2) = inj_nonneg k1 k2 n
let odd_unique (k1 k2:int) (n:pos{n % 2 = 1})
  : Lemma (requires pow k1 n = pow k2 n) (ensures k1 = k2)
  = if k1 >= 0 && k2 >= 0 then inj_nonneg k1 k2 n
    else if k1 < 0 && k2 < 0 then begin
      pow_neg (-k1) n; pow_neg (-k2) n; inj_nonneg (-k1) (-k2) n end
    else if k1 < 0 then begin pow_neg (-k1) n; pow_nonneg k2 n; pow_pos (-k1) n end
    else begin pow_neg (-k2) n; pow_nonneg k1 n; pow_pos (-k2) n end

(* ---- Obligation A3: check_real_power weakened guard (x<0 instead of x=x0) is sound
   given the axiom x<0 /\ (even denominator or irrational y) => p=0 (lines 35-38).
   f models the axiomatized term value as a function of (x,y). *)
let weakened_sound (f:int -> int -> int) (x0 x y:int) (even_den:bool)
  : Lemma (requires (forall (a b:int). (a < 0 /\ even_den) ==> f a b = 0) /\ x0 < 0 /\ x < 0 /\ even_den)
          (ensures f x y = 0) = ()

(* ---- Obligation B1: compute_power square-and-multiply loop (lines 126-137) computes x^y. *)
let rec pow_add (b:int) (m n:nat) : Lemma (ensures pow b (m+n) = pow b m * pow b n) (decreases m) =
  if m = 0 then () else (pow_add b (m-1) n; FStar.Math.Lemmas.paren_mul_right b (pow b (m-1)) (pow b n))
let pow_square (b:int) (e:nat) : Lemma (pow (b*b) e = pow b (2*e)) =
  let rec aux (e:nat) : Lemma (ensures pow (b*b) e = pow b (2*e)) (decreases e) =
    if e = 0 then () else begin
      aux (e-1);
      pow_add b (2*(e-1)) 2
    end in aux e
let rec loop (result base:int) (e:nat) : Tot int (decreases e) =
  if e = 0 then result
  else
    let r = if e % 2 = 1 then result * base else result in
    let e' = e / 2 in
    if e' > 0 then loop r (base * base) e' else r
let rec loop_inv (result base:int) (e:nat)
  : Lemma (ensures loop result base e = result * pow base e) (decreases e) =
  if e = 0 then ()
  else begin
    let e' = e / 2 in
    let r = if e % 2 = 1 then result * base else result in
    if e' > 0 then begin
      loop_inv r (base*base) e'; pow_square base e';
      pow_add base (2*e') (e % 2)
    end else ()
  end

(* ---- Obligation B2: check_model early rejection (line 148) is sound.
   |x|>=2, y>=0, |value| < 2^bits, y > bits+1 implies value <> x^y. *)
let rec pow2 (n:nat) : pos = if n = 0 then 1 else 2 * pow2 (n-1)
let rec ge_pow2 (a:int{a >= 2}) (n:nat) : Lemma (ensures pow a n >= pow2 n) (decreases n) =
  if n = 0 then () else begin ge_pow2 a (n-1); pow_nonneg a (n-1) end
let early_reject (x:int{x >= 2}) (y:nat) (bits:nat) (value:int)
  : Lemma (requires y > bits + 1 /\ value < pow2 bits /\ value > - (pow2 bits))
          (ensures value <> pow x y /\ value <> - (pow x y))
  = ge_pow2 x y;
    let rec mono2 (a b:nat) : Lemma (requires a <= b) (ensures pow2 a <= pow2 b) (decreases b) =
      if a = b then () else mono2 a (b-1) in
    mono2 (bits+1) y
