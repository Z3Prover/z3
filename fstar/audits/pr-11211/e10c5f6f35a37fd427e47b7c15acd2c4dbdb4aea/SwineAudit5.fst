module SwineAudit5
(* purify_arith_tactic.cpp process_power at head e10c5f6f, lines 436-486.
   Integers model the ordered field for the root-defining constraints. *)

let rec pow (b:int) (e:nat) : int = if e = 0 then 1 else b * pow b (e-1)

(* O1: guard. rational y = num/den, den >= 1 normalized, y <> 0, not integer, numerator one *)
let accepted (num:int) (den:pos) : bool = not (num = 0) && not (den = 1) && num = 1
let o1 (num:int) (den:pos) : Lemma (accepted num den ==> (den >= 2 /\ num = 1)) = ()
let o1_rejects (num:int) (den:pos) : Lemma (num <> 1 ==> not (accepted num den)) = ()

let rec pow_nonneg (a:nat) (n:nat) : Lemma (ensures pow a n >= 0) (decreases n) =
  if n = 0 then () else (pow_nonneg a (n-1); FStar.Math.Lemmas.nat_times_nat_is_nat a (pow a (n-1)))

let rec pow_pos (a:pos) (n:nat) : Lemma (ensures pow a n > 0) (decreases n) =
  if n = 0 then () else (pow_pos a (n-1); FStar.Math.Lemmas.pos_times_pos_is_pos a (pow a (n-1)))

let rec mono (a b:nat) (n:pos) : Lemma (requires a < b) (ensures pow a n < pow b n) (decreases n) =
  if n = 1 then ()
  else begin
    mono a b (n-1);
    pow_nonneg a (n-1);
    pow_pos b (n-1);
    FStar.Math.Lemmas.lemma_mult_le_right (pow a (n-1)) a b;
    FStar.Math.Lemmas.lemma_mult_lt_left b (pow a (n-1)) (pow b (n-1))
  end

(* p-th power is injective on nonnegatives *)
let inj_nonneg (a b:nat) (n:pos) : Lemma (requires pow a n = pow b n) (ensures a = b) =
  if a < b then mono a b n else if b < a then mono b a n else ()

(* O2 (even n): the two emitted constraints determine k uniquely, with no branch conflict *)
let even_ok (x:int) (k1 k2:int) (n:pos) (nr:int)
  : Lemma
    (requires ((x < 0 \/ (x = pow k1 n /\ k1 >= 0)) /\ (x >= 0 \/ k1 = nr)) /\
              ((x < 0 \/ (x = pow k2 n /\ k2 >= 0)) /\ (x >= 0 \/ k2 = nr)))
    (ensures k1 = k2)
  = if x >= 0 then inj_nonneg k1 k2 n else ()

let rec pow_neg (a:nat) (n:nat) : Lemma (ensures pow (-a) n = (if n % 2 = 0 then pow a n else - (pow a n))) (decreases n) =
  if n = 0 then () else pow_neg a (n-1)

(* O3 (odd n): x = k^n has at most one solution, so the fresh k is uniquely defined *)
let odd_unique (k1 k2:int) (n:pos{n % 2 = 1})
  : Lemma (requires pow k1 n = pow k2 n) (ensures k1 = k2)
  = if k1 >= 0 && k2 >= 0 then inj_nonneg k1 k2 n
    else if k1 < 0 && k2 < 0 then begin
      pow_neg (-k1) n; pow_neg (-k2) n; inj_nonneg (-k1) (-k2) n
    end
    else if k1 < 0 then begin
      pow_neg (-k1) n; pow_pos (-k1) n; pow_nonneg k2 n
    end
    else begin
      pow_neg (-k2) n; pow_pos (-k2) n; pow_nonneg k1 n
    end
