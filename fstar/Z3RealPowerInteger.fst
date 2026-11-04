module Z3RealPowerInteger

open FStar.Real
module R = Z3RealPower
module N = Z3ArithRewriterPower
module K = Z3SwinePower

#set-options "--fuel 2 --ifuel 0 --z3rlimit 10 --smtencoding.nl_arith_repr native"

(* This lean model depends only on the existing natural-power kernel.
   The body is the defining equation of Z3SwineStandardPower.exp, without
   importing that module's interpolation/prime/refinement dependencies.
   [standard_power_contract] below is the explicit equality obligation
   required when instantiating the bridge with an external operation such
   as Z3SwineStandardPower.exp. No equality to an uninterpreted external
   operation is assumed globally. *)
let integer_exp (x y:int) : int =
  if y < 0 && x <> 1 && x <> -1 then 0 else K.exp x y

let standard_power_contract (op:int -> int -> Tot int) : prop =
  forall (x y:int).
    op x y == (if y < 0 && x <> 1 && x <> -1 then 0 else K.exp x y)

let local_contract () : Lemma (standard_power_contract integer_exp) = ()

let integer_nonnegative (x:int) (n:nat)
  : Lemma (integer_exp x n == K.power x n) =
  assert (K.magnitude n == n);
  assert (K.exp x n == K.power x n)

let integer_negative (x:int) (y:int{y < 0})
  : Lemma (integer_exp x y ==
      (if x == 1 then 1
       else if x == -1 then (if y%2 == 0 then 1 else -1)
       else 0)) =
  if x == 1 then K.rewrite_one_base y
  else if x == -1 then K.rewrite_minus_one_base y

let rec natural_cast (x:int) (n:nat)
  : Lemma (ensures N.ipow (of_int x) n == of_int (K.power x n))
          (decreases n) =
  if n > 0 then begin
    natural_cast x (n-1);
    R.integer_product_cast x (K.power x (n-1));
    assert (K.power x n == x * K.power x (n-1));
    assert (N.ipow (of_int x) n ==
            of_int x *. N.ipow (of_int x) (n-1))
  end

let nonnegative_agreement (c:R.classifier) (x:int) (n:nat)
  : Lemma (R.power c (of_int x) (of_int n) == of_int (integer_exp x n)) =
  R.natural_bridge c (of_int x) n;
  natural_cast x n;
  integer_nonnegative x n

let linked_nonnegative_agreement (c:R.classifier)
    (op:int -> int -> Tot int) (x:int) (n:nat)
  : Lemma (requires standard_power_contract op)
          (ensures R.power c (of_int x) (of_int n) == of_int (op x n)) =
  nonnegative_agreement c x n;
  assert (op x n == integer_exp x n)

let real_negative_integer (c:R.classifier) (x:int) (n:pos)
  : Lemma (R.power c (of_int x) (zero -. of_int n) ==
           R.inverse (of_int (K.power x n))) =
  R.negative_integer c (of_int x) n;
  natural_cast x n

let integer_real_are_distinct (c:R.classifier)
  : Lemma (integer_exp 2 (-1) == 0 /\
           R.power c 2.0R (zero -. one) == 0.5R /\
           R.power c 2.0R (zero -. one) =!= of_int (integer_exp 2 (-1))) =
  integer_negative 2 (-1);
  R.one_exponent c 2.0R;
  R.guarded_reciprocal c 2.0R one

let linked_integer_real_are_distinct (c:R.classifier)
    (op:int -> int -> Tot int)
  : Lemma (requires standard_power_contract op)
          (ensures op 2 (-1) == 0 /\
             R.power c 2.0R (zero -. one) == 0.5R /\
             R.power c 2.0R (zero -. one) =!= of_int (op 2 (-1))) =
  integer_real_are_distinct c;
  assert (op 2 (-1) == integer_exp 2 (-1))
