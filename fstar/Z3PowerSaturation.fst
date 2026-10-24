module Z3PowerSaturation

open FStar.Real
module N = Z3ArithRewriterPower
module P = FStar.Math.Pow
module R = Z3PowerPreprocessing

(* Literal-for-literal clauses from powers::check, before and after the
   correction. x0 and n are model constants; x, y and r remain universally
   quantified. A concrete model value never fixes the exponent in a clause. *)
let lower_old (x y r x0:real) (n:nat) : prop =
  x <. x0 \/ y <. of_int n \/ r >=. N.ipow x0 n

let upper_old (x y r x0:real) (n:nat) : prop =
  x <=. zero \/ x >. x0 \/ y >. of_int n \/ r <=. N.ipow x0 n

let lower_fixed (x y r x0:real) (n:nat) : prop =
  if x0 >=. one then lower_old x y r x0 n
  else x <. x0 \/ y >. of_int n \/ y <. zero \/ r >=. N.ipow x0 n

let upper_fixed (x y r x0:real) (n:nat) : prop =
  if x0 >=. one then
    x <=. zero \/ x >. x0 \/ y >. of_int n \/ y <. zero \/ r <=. N.ipow x0 n
  else x <=. zero \/ x >. x0 \/ y <. of_int n \/ r <=. N.ipow x0 n

let integer_one (n:nat) : Lemma (N.ipow one n == one) =
  R.integer_bridge one n;
  P.pow_one_base (of_int n)

let integer_ge_one (x:real) (n:nat)
  : Lemma (requires x >=. one) (ensures N.ipow x n >=. one) =
  integer_one n;
  R.integer_base_mono one x n

let integer_le_one (x:real) (n:nat)
  : Lemma (requires zero <. x /\ x <=. one)
          (ensures N.ipow x n <=. one) =
  integer_one n;
  R.integer_base_mono x one n

let lower_fixed_sound (x:P.rpos) (y r:real) (x0:P.rpos) (n:nat)
  : Lemma (requires r == P.pow x y)
          (ensures lower_fixed x y r x0 n) =
  if x0 >=. one then begin
    if x >=. x0 /\ y >=. of_int n then begin
      P.pow_mono x (of_int n) y;
      R.integer_bridge x n;
      R.integer_base_mono x0 x n
    end
  end
  else if x >=. x0 /\ zero <=. y /\ y <=. of_int n then begin
    if x >=. one then begin
      P.pow_mono x zero y;
      P.pow_zero x;
      integer_le_one x0 n
    end
    else begin
      P.pow_antitone x y (of_int n);
      R.integer_bridge x n;
      R.integer_base_mono x0 x n
    end
  end

let upper_fixed_sound (x:P.rpos) (y r:real) (x0:P.rpos) (n:nat)
  : Lemma (requires r == P.pow x y)
          (ensures upper_fixed x y r x0 n) =
  if x0 >=. one then begin
    if x <=. x0 /\ zero <=. y /\ y <=. of_int n then begin
      if x >=. one then begin
        P.pow_mono x y (of_int n);
        R.integer_bridge x n;
        R.integer_base_mono x x0 n
      end
      else begin
        P.pow_antitone x zero y;
        P.pow_zero x;
        integer_ge_one x0 n
      end
    end
  end
  else if x <=. x0 /\ y >=. of_int n then begin
    P.pow_antitone x (of_int n) y;
    R.integer_bridge x n;
    R.integer_base_mono x x0 n
  end

let nonpositive_base_clauses (x y r:real) (x0:P.rpos) (n:nat)
  : Lemma (requires x <=. zero)
          (ensures lower_fixed x y r x0 n /\ upper_fixed x y r x0 n) = ()

(* These witnesses evaluate actual real powers. They are not assignments
   to an uninterpreted power function or to its result variable. *)
let old_lower_counterexample ()
  : Lemma (P.pow 0.5R 2.0R == 0.25R /\
           ~(lower_old 0.5R 2.0R (P.pow 0.5R 2.0R) 0.5R 1)) =
  R.fold_half_square ()

let old_upper_counterexample ()
  : Lemma (P.pow 0.25R 0.5R == 0.5R /\
           ~(upper_old 0.25R 0.5R (P.pow 0.25R 0.5R) 0.25R 1)) =
  R.fold_quarter_root ()

let reported_upper_counterexample ()
  : Lemma (P.pow 0.5R 0.5R >. 0.5R /\
           ~(upper_old 0.5R 0.5R (P.pow 0.5R 0.5R) 0.5R 1)) =
  let r = P.pow 0.5R 0.5R in
  R.rational_root_equation 0.5R 1 2;
  N.power_one r;
  N.power_add r 1 1;
  N.power_one 0.5R

let old_upper_negative_exponent_counterexample ()
  : Lemma (P.pow 0.25R (zero -. one) == 4.0R /\
           ~(upper_old 0.25R (zero -. one) (P.pow 0.25R (zero -. one)) 2.0R 1)) =
  P.pow_neg 0.25R one;
  P.pow_one 0.25R

(* Reversing the below-one exponent bound alone is insufficient: allowing
   a negative exponent while the live base crosses one is also unsound. *)
let reversed_lower_without_nonnegative_guard ()
  : Lemma (P.pow 2.0R (zero -. two) == 0.25R /\
           ~(2.0R <. 0.5R \/ (zero -. two) >. 1.0R \/
             P.pow 2.0R (zero -. two) >=. N.ipow 0.5R 1)) =
  R.rewrite_negative_integer 2.0R 2

let fixed_clauses_keep_counterexamples ()
  : Lemma (lower_fixed 0.5R 2.0R 0.25R 0.5R 1 /\
           upper_fixed 0.25R 0.5R 0.5R 0.25R 1 /\
           upper_fixed 0.25R (zero -. one) 4.0R 2.0R 1 /\
           lower_fixed 2.0R (zero -. two) 0.25R 0.5R 1) = ()

(* Other positive-base clauses emitted in both rational and algebraic
   model modes. The signs on these disjuncts match llc in nla_powers.cpp. *)
let zero_exponent_clause (x:P.rpos)
  : Lemma (x == zero \/ P.pow x zero == one) =
  P.pow_zero x

let general_zero_exponent_clause (zero_zero x:real)
  : Lemma (x == zero \/ R.zero_exponent_value zero_zero x == one) = ()

let zero_base_clause (zero_zero y:real)
  : Lemma (y == zero \/ R.zero_base_value zero_zero y == zero) = ()

let positive_result_clause (x:P.rpos) (y:real)
  : Lemma (x <=. zero \/ P.pow x y >. zero) =
  P.pow_positive x y

let negative_exponent_clause (x:P.rpos) (y:real)
  : Lemma (x <=. one \/ y >=. zero \/ P.pow x y <. one) =
  if x >. one /\ y <. zero then begin
    P.pow_mono x y zero;
    P.pow_zero x;
    if P.pow x y == one then begin
      P.pow_pow x y (one /. y);
      P.pow_one_base (one /. y);
      P.pow_one x
    end
  end

let positive_exponent_clause (x:P.rpos) (y:real)
  : Lemma (x <=. one \/ y <=. zero \/ P.pow x y >. one) =
  if x >. one /\ y >. zero then begin
    P.pow_mono x zero y;
    P.pow_zero x;
    if P.pow x y == one then begin
      P.pow_pow x y (one /. y);
      P.pow_one_base (one /. y);
      P.pow_one x
    end
  end

let exact_point_clause (x:P.rpos) (y r:real) (x0:P.rpos) (n:nat)
  : Lemma (requires r == P.pow x y)
          (ensures x =!= x0 \/ y =!= of_int n \/ r == N.ipow x0 n) =
  R.integer_bridge x0 n

let rational_acceptance (x:P.rpos) (m:pos) (d:pos) (r:P.rpos)
  : Lemma (requires N.ipow r d == N.ipow x m)
          (ensures r == P.pow x (of_int m /. of_int d)) =
  R.rational_root_unique x m d r

let natural_acceptance (x:P.rpos) (n:nat) (r:real)
  : Lemma (requires r == N.ipow x n)
          (ensures r == P.pow x (of_int n)) =
  R.integer_bridge x n

(* Isolated real-analysis boundary for x_ge_3, not used by either
   counterexample or by the corrected monotonicity proofs. These fields
   are mathematical prerequisites, not axioms installed in the module.
   In particular importing FStar.Math.Exp would hide admitted facts. *)
noeq type growth_analysis = {
  exponential: real -> real;
  logarithm: real -> real;
  representation: x:P.rpos -> y:real ->
    Lemma (P.pow x y == exponential (y *. logarithm x));
  tangent: t:real -> Lemma (exponential t >=. one +. t);
  log_monotone: x:P.rpos -> z:real{z >=. x} ->
    Lemma (logarithm x <=. logarithm z);
  log_three: unit -> Lemma (logarithm 3.0R >. one)
}

let growth_clause (a:growth_analysis) (x:P.rpos) (y:real)
  : Lemma (x <. 3.0R \/ y <=. zero \/ P.pow x y -. y >. one) =
  if x >=. 3.0R /\ y >. zero then begin
    a.log_monotone 3.0R x;
    a.log_three ();
    a.representation x y;
    a.tangent (y *. a.logarithm x)
  end
