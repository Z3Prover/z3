module SwineAudit3
module L = FStar.Math.Lemmas

(* Model of compute_power / Z3 integer power on non-negative exponents. *)
let rec pow (b:int) (e:nat) : Tot int (decreases e) =
  if e = 0 then 1 else b * pow b (e - 1)

(* Z3 integer semantics for any integer exponent: negative exponents truncate to 0
   except at base +/-1 (mirrors arith_rewriter::mk_power_core, Int branch). *)
let zpow (b:int) (e:int) : int =
  if e >= 0 then pow b e
  else if b = 1 then 1
  else if b = -1 then (if e % 2 = 0 then 1 else -1)
  else 0

let rec pow_add (b:int) (e:nat) (d:nat) : Lemma (ensures pow b (e + d) == pow b e * pow b d) (decreases e) =
  if e = 0 then () else pow_add b (e - 1) d

let rec pow_mul (b:int) (y:nat) (z:nat) : Lemma (ensures pow b (y * z) == pow (pow b y) z) (decreases z) =
  if z = 0 then ()
  else begin
    pow_mul b y (z - 1);
    assert (y * z == y * (z - 1) + y);
    pow_add b (y * (z - 1)) y
  end

let rec pow_one (n:nat) : Lemma (ensures pow 1 n == 1) (decreases n) =
  if n = 0 then () else pow_one (n - 1)

let rec pow_zero (n:nat{n > 0}) : Lemma (ensures pow 0 n == 0) (decreases n) =
  if n = 1 then () else pow_zero (n - 1)

let rec pow_m1 (n:nat) : Lemma (ensures pow (-1) n == (if n % 2 = 0 then 1 else -1)) (decreases n) =
  if n = 0 then () else pow_m1 (n - 1)

let rec pow_big (b:int{b >= 2 \/ b <= -2}) (n:nat{n > 0})
  : Lemma (ensures pow b n >= 2 \/ pow b n <= -2) (decreases n) =
  if n = 1 then ()
  else begin
    pow_big b (n - 1);
    let p = pow b (n - 1) in
    assert (pow b n == b * p);
    if p >= 2 then (if b >= 2 then assert (b * p >= 4) else assert (b * p <= -4))
    else (if b >= 2 then assert (b * p <= -4) else assert (b * p >= 4))
  end

let parity_mul (y z:int) : Lemma ((y * z) % 2 = 0 <==> (y % 2 = 0 \/ z % 2 = 0)) =
  let a = y / 2 in
  let b = z / 2 in
  assert (y == 2 * a + y % 2);
  assert (z == 2 * b + z % 2);
  assert (y * z == 2 * (2*a*b + a * (z % 2) + b * (y % 2)) + (y % 2) * (z % 2));
  L.lemma_mod_plus ((y % 2) * (z % 2)) (2*a*b + a * (z % 2) + b * (y % 2)) 2

(* Obligation N: arith_rewriter nested case.
   (b**y)**z = b**(y*z), with y*z negated when both exponents are negative. *)
let nested_valid (b:int) (y:int) (z:int)
  : Lemma (zpow (zpow b y) z == zpow b (if y < 0 && z < 0 then - (y * z) else y * z))
  = parity_mul y z;
    if y >= 0 && z >= 0 then pow_mul b y z
    else if y >= 0 then begin
      if y = 0 then ()
      else if b = 1 then pow_one y
      else if b = -1 then (pow_m1 y; if z >= 0 then (pow_one z; pow_m1 z) else ())
      else if b = 0 then pow_zero y
      else pow_big b y
    end else begin
      if b = 1 then (if z >= 0 then pow_one z else ())
      else if b = -1 then (if z >= 0 then (pow_one z; pow_m1 z) else ())
      else if b = 0 then (if z > 0 then pow_zero z else ())
      else ()
    end
