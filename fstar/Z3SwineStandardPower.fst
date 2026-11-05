module Z3SwineStandardPower

module P = Z3SwinePower
module R = Z3SwineRefinements
module Prime = Z3SwinePrime
module I = Z3SwineInterpolation

#set-options "--fuel 2 --ifuel 0 --z3rlimit 10 --smtencoding.nl_arith_repr native"

(* The original modules retain their absolute-exponent model. This bridge
   reuses its natural-power kernel for the SMT-LIB integer operation. *)
let exp (x y:int) : int =
  if y < 0 && x <> 1 && x <> -1 then 0 else P.exp x y

let nonnegative (x:int) (y:nat)
  : Lemma (exp x y == P.power x y /\ exp x y == P.exp x y) = ()

let negative (x:int) (y:int{y < 0})
  : Lemma (exp x y ==
      (if x = 1 then 1 else if x = -1 then (if y%2 = 0 then 1 else -1) else 0)) =
  if x = 1 then P.rewrite_one_base y
  else if x = -1 then P.rewrite_minus_one_base y

let zero_exponent (x:int) : Lemma (exp x 0 == 1) = ()
let one_exponent (x:int) : Lemma (exp x 1 == x) = ()
let one_base (y:int) : Lemma (exp 1 y == 1) = P.rewrite_one_base y
let minus_one_base (y:int)
  : Lemma (exp (-1) y == (if y%2 = 0 then 1 else -1)) =
  P.rewrite_minus_one_base y
let zero_base (y:int)
  : Lemma (exp 0 y == (if y = 0 then 1 else 0)) =
  if y >= 0 then P.rewrite_zero_base y

let base_sign (x y:int)
  : Lemma (exp (-x) y == (if y%2 = 0 then exp x y else -exp x y)) =
  P.magnitude_parity y;
  P.power_sign x (P.magnitude y)

let nonunit_power (x:int{x <> 1 /\ x <> -1}) (n:pos)
  : Lemma (P.power x n <> 1 /\ P.power x n <> -1) =
  if x = 0 then P.power_zero_base n
  else if x > 1 then begin
    P.exponent_monotone x 1 n;
    P.power_succ x 0
  end
  else begin
    P.exponent_monotone (-x) 1 n;
    P.power_succ (-x) 0;
    P.power_sign (-x) n
  end

let nested (x y z:int)
  : Lemma (exp (exp x y) z ==
      exp x (if y < 0 && z < 0 then -(y*z) else y*z)) =
  if x = 1 then begin
    P.rewrite_one_base y;
    P.rewrite_one_base z;
    P.rewrite_one_base (y*z);
    P.rewrite_one_base (-(y*z))
  end
  else if x = -1 then begin
    P.rewrite_minus_one_base y;
    P.rewrite_nested x y z;
    P.rewrite_neg_exponent x (y*z)
  end
  else if y < 0 then begin
    zero_base z;
    if z = 0 then zero_exponent x
  end
  else if y = 0 then one_base z
  else if z < 0 then nonunit_power x y
  else P.power_merge x y z

let common_base (x y z:int)
  : Lemma (exp x y * exp x z ==
      (if x <> 1 && x <> -1 && (y < 0 || z < 0) then 0 else exp x (y+z))) =
  if x = 1 then begin
    one_base y; one_base z; one_base (y+z)
  end
  else if x = -1 then begin
    minus_one_base y; minus_one_base z; minus_one_base (y+z)
  end
  else if y >= 0 && z >= 0 then P.power_add x y z

let common_exponent (x z y:int)
  : Lemma (exp x y * exp z y == exp (x*z) y) =
  if y >= 0 then P.power_product x z y
  else if (x = 1 || x = -1) && (z = 1 || z = -1) then begin
    negative x y; negative z y; negative (x*z) y
  end
  else begin
    assert (x*z <> 1 /\ x*z <> -1);
    negative (x*z) y
  end

let bounding (x y:int)
  : Lemma (
      (y = 0 ==> exp x y == 1) /\
      (y = 1 ==> exp x y == x) /\
      (x = 1 ==> exp x y == 1) /\
      (y >= 0 ==> ((x = 0 /\ y <> 0) <==> exp x y = 0)) /\
      (x > 0 /\ y >= 0 ==> exp x y >= 1) /\
      (x > 1 /\ y > 1 /\ x+y > 4 ==> exp x y > x*y+1)) =
  if x = 1 then one_base y;
  if y >= 0 then R.bounding_sound x y

let monotonicity (x y z w:int)
  : Lemma ((x > 1 /\ y > 0 /\ z >= x /\ w >= y /\ (z > x \/ w > y)) ==>
      exp z w > exp x y) =
  if y > 0 && w >= y then R.monotonicity_sound x y z w

let prime (d:int{FStar.Math.Euclid.is_prime d}) (x y:int)
  : Lemma (y >= 0 ==> ((exp x y % d = 0) <==> (x % d = 0 /\ y <> 0))) =
  if y >= 0 then Prime.prime_clause_sound d x y

let induction (x y z w:int) (delta:pos)
  : Lemma ((x = z /\ y >= 0 /\ w-y = delta) ==>
      exp z w == exp x y * P.power x delta) =
  if y >= 0 && w-y = delta then R.induction_sound x y z w delta

let interpolation_upper (x y:int) (a b c d:pos)
  : Lemma (requires a <= b /\ c <= d)
      (ensures (a <= x /\ x <= b /\ c <= y /\ y <= d) ==>
        I.width a b * I.width c d * exp x y <= I.numerator x y a b c d) =
  if a <= x && x <= b && c <= y && y <= d then I.upper_sound x y a b c d

let interpolation_lower (x y:int) (a c:pos)
  : Lemma ((x >= 1 /\ y >= c) ==>
      exp x y >= I.numerator x y a (a+1) c (c+1)) =
  if x >= 1 && y >= c then I.lower_sound x y a c

let candidate (budget:nat) (x y value:int)
  : Lemma (requires
      (if y < 0 then
         value == (if x = 1 then 1 else if x = -1 then (if y%2 = 0 then 1 else -1) else 0)
       else P.square_budget budget x y == Some value))
      (ensures value == exp x y) =
  if y < 0 then negative x y
  else P.checked_acceptance x y value budget

let old_nested_rule_is_invalid ()
  : Lemma (exp (exp 2 (-1)) (-1) <> exp 2 ((-1)*(-1))) = ()

let old_common_base_rule_is_invalid ()
  : Lemma (exp 2 (-1) * exp 2 1 <> exp 2 ((-1)+1)) = ()
