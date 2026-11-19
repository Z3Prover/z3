module PR11557ZeroBase

open FStar.Real

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

(* Mirror of the zero-base and non-zero-exponent branches of Z3RealPower.power;
   the classifier is abstract, as in the base module. *)
type fraction = { numerator: int; denominator: pos }
type cls = | Rational : fraction -> cls | Irrational

let signed (p:int) (a:real) : real = if p % 2 = 0 then a else zero -. a

let power (x y:real) (a:real -> GTot real) : GTot real =
  if y == zero then one
  else if x == zero then zero
  else a y

let inverse (x:real) : GTot real = if x == zero then zero else one /. x

(* O1: the PR's helper lemma. *)
let negation_nonzero (y:real{y =!= zero})
  : Lemma (zero -. y =!= zero) = ()

let zero_base (a:real -> GTot real) (y:real)
  : Lemma (power zero y a == (if y == zero then one else zero)) = ()

(* O2: reciprocal at zero base using the helper, as in the PR head. *)
let reciprocal_at_zero_base (a:real -> GTot real) (y:real{y =!= zero})
  : Lemma (power zero (zero -. y) a == inverse (power zero y a)) =
  negation_nonzero y;
  zero_base a y;
  zero_base a (zero -. y)

(* O3: head-level equivalence with the old assert form (same obligation). *)
let reciprocal_at_zero_base_old (a:real -> GTot real) (y:real{y =!= zero})
  : Lemma (power zero (zero -. y) a == inverse (power zero y a)) =
  assert (zero -. y =!= zero);
  zero_base a y;
  zero_base a (zero -. y)
