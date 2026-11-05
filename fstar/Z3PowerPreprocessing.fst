module Z3PowerPreprocessing

open FStar.Real
module N = Z3ArithRewriterPower
module P = FStar.Math.Pow

#set-options "--fuel 1 --ifuel 0 --z3rlimit 20"

(* Value-level audit of arith_rewriter::mk_power_core and reduce_power.
   Positive real powers use the library's constructive power, not Exp's
   admitted axioms. Integer-power identities also cover negative bases.
   Zero to a nonzero exponent is Z3's zero-totalization; 0^0 stays opaque. *)

let zero_base_value (zero_zero y:real) : real =
  if y == zero then zero_zero else zero

let zero_exponent_value (zero_zero x:real) : real =
  if x == zero then zero_zero else one

let nonnegative_power (zero_zero:real) (x:real{x >=. zero}) (y:real) : real =
  if x == zero then zero_base_value zero_zero y else P.pow x y

let rewrite_zero_nonzero_exponent (zero_zero y:real)
  : Lemma (requires y =!= zero)
          (ensures zero_base_value zero_zero y == zero) = ()

let preserve_zero_zero (zero_zero:real)
  : Lemma (zero_base_value zero_zero zero == zero_zero /\
           zero_exponent_value zero_zero zero == zero_zero) = ()

let rec integer_positive (x:real) (n:nat)
  : Lemma (requires x >. zero) (ensures N.ipow x n >. zero)
          (decreases n) =
  if n > 0 then integer_positive x (n - 1)

let rec integer_nonzero (x:real) (n:nat)
  : Lemma (requires x =!= zero) (ensures N.ipow x n =!= zero)
          (decreases n) =
  if n > 0 then integer_nonzero x (n - 1)

let rec integer_nonnegative (x:real) (n:nat)
  : Lemma (requires x >=. zero) (ensures N.ipow x n >=. zero)
          (decreases n) =
  if n > 0 then integer_nonnegative x (n - 1)

[@@"opaque_to_smt"]
let nonzero_power (x:real{x =!= zero}) (n:nat)
  : r:real{r =!= zero /\ r == N.ipow x n} =
  integer_nonzero x n;
  N.ipow x n

let rec integer_base_mono (x z:real) (n:nat)
  : Lemma (requires zero <=. x /\ x <=. z)
          (ensures N.ipow x n <=. N.ipow z n)
          (decreases n) =
  if n > 0 then begin
    integer_base_mono x z (n - 1);
    integer_nonnegative x (n - 1);
    integer_nonnegative z (n - 1);
    assert (x *. N.ipow x (n - 1) <=. z *. N.ipow x (n - 1))
  end

let rec integer_bridge (x:P.rpos) (n:nat)
  : Lemma (P.pow x (of_int n) == N.ipow x n)
          (decreases n) =
  if n = 0 then P.pow_zero x
  else begin
    integer_bridge x (n - 1);
    P.pow_succ x (n - 1)
  end

let rewrite_base_one (y:real) : Lemma (P.pow one y == one) =
  P.pow_one_base y

let rewrite_exponent_one (x:P.rpos) : Lemma (P.pow x one == x) =
  P.pow_one x

let rewrite_exponent_zero (x:P.rpos) : Lemma (P.pow x zero == one) =
  P.pow_zero x

let rewrite_zero_natural (n:pos) : Lemma (N.ipow zero n == zero) =
  N.power_zero_base n

let rewrite_natural_expansion (x:P.rpos) (n:nat)
  : Lemma (P.pow x (of_int n) == N.ipow x n) =
  integer_bridge x n

let rec reciprocal_integer (x:real{x =!= zero}) (n:nat)
  : Lemma (N.ipow (one /. x) n *. N.ipow x n == one)
          (decreases n) =
  integer_nonzero x n;
  if n > 0 then begin
    integer_nonzero x (n - 1);
    reciprocal_integer x (n - 1);
    assert ((one /. x *. N.ipow (one /. x) (n - 1)) *.
             (x *. N.ipow x (n - 1)) ==
             (one /. x *. x) *.
             (N.ipow (one /. x) (n - 1) *. N.ipow x (n - 1)))
  end

(* The nonzero branch of numeral folding at exponent -n. The C++ zero
   branch is selected first and returns zero, never division by zero. *)
let rewrite_negative_integer (x:P.rpos) (n:pos)
  : Lemma (P.pow x (zero -. of_int n) == N.ipow (one /. x) n) =
  P.pow_neg x (of_int n);
  integer_bridge x n;
  reciprocal_integer x n

let rewrite_negative_real (x:P.rpos) (y:real)
  : Lemma (P.pow x (zero -. y) == P.pow (one /. x) y) =
  P.pow_neg x y;
  P.pow_inverse_base x y

let rewrite_nested_positive (x:P.rpos) (y z:real)
  : Lemma (P.pow (P.pow x y) z == P.pow x (y *. z)) =
  P.pow_pow x y z

let rewrite_nested_natural (x:real) (m n:nat)
  : Lemma (N.ipow (N.ipow x m) n == N.ipow x (m * n)) =
  N.power_merge x m n

let rewrite_nested_negative_integer (x:real{x =!= zero}) (m n:pos)
  : Lemma (one /. nonzero_power (nonzero_power x m) n ==
           one /. nonzero_power x (m * n)) =
  integer_nonzero x m;
  integer_nonzero (N.ipow x m) n;
  integer_nonzero x (m * n);
  N.power_merge x m n

let rewrite_fractional_split (x:P.rpos) (m:nat) (d:pos)
  : Lemma (P.pow x (of_int m /. of_int d) ==
           P.pow (P.pow x (one /. of_int d)) (of_int m)) =
  P.pow_pow x (one /. of_int d) (of_int m)

let rational_root_equation (x:P.rpos) (m:nat) (d:pos)
  : Lemma (N.ipow (P.pow x (of_int m /. of_int d)) d == N.ipow x m) =
  P.pow_rational x m d;
  integer_bridge (P.pow x (of_int m /. of_int d)) d;
  integer_bridge x m

let rational_root_unique (x:P.rpos) (m:nat) (d:pos) (r:P.rpos)
  : Lemma (requires N.ipow r d == N.ipow x m)
          (ensures P.pow x (of_int m /. of_int d) == r) =
  integer_bridge r d;
  integer_bridge x m;
  P.pow_rational_unique x m d r

(* The root axioms in theory_lra::mk_power_axiom and the SAT backend's
   arith_axioms.cpp also admit base zero, but only positive numerators. *)
let nonnegative_root_axiom (zero_zero:real) (x:real{x >=. zero}) (m d:pos)
  : Lemma (N.ipow (nonnegative_power zero_zero x (of_int m /. of_int d)) d ==
           N.ipow x m) =
  if x == zero then begin
    N.power_zero_base m;
    N.power_zero_base d
  end
  else rational_root_equation x m d

(* reduce_power is used only in comparisons with zero. This context
   coefficient stands for all the other factors of a product. *)
let reduce_zero_equality (c x:real) (n:pos)
  : Lemma ((c *. N.ipow x n == zero) <==> (c *. x == zero)) =
  if x == zero then N.power_zero_base n
  else integer_nonzero x n

let rec reduce_zero_order (c x:real) (n:pos)
  : Lemma ((c *. N.ipow x n >=. zero) <==>
           (c *. N.ipow x (if n % 2 = 0 then 2 else 1) >=. zero))
          (decreases n) =
  if n > 2 then begin
    reduce_zero_order c x (n - 2);
    N.power_one x;
    N.power_add x 1 1;
    N.power_add x 2 (n - 2);
    if x == zero then begin
      N.power_zero_base n;
      N.power_zero_base (n - 2)
    end
    else assert (x *. x >. zero)
  end

(* Exact rational/algebraic folding: the positive candidate must satisfy
   the root equation. This does not verify the C++ root implementation. *)
#push-options "--fuel 3"
let fold_half_square ()
  : Lemma (P.pow 0.5R 2.0R == 0.25R) =
  integer_bridge 0.5R 2

let fold_quarter_root ()
  : Lemma (P.pow 0.25R 0.5R == 0.5R) =
  rational_root_unique 0.25R 1 2 0.5R
#pop-options
