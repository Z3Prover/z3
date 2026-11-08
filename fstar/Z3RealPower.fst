module Z3RealPower

open FStar.Real
module G = FStar.Rational.Gcd
module A = FStar.Math.Pow
module N = Z3ArithRewriterPower

#set-options "--fuel 2 --ifuel 0 --z3rlimit 10 --smtencoding.nl_arith_repr native"

(* A logical, non-extractable model, not an implementation of a real-number
   decision procedure. Positive-base analysis is FStar.Math.Pow. The OTHER
   dependency is explicit: a total, correct rational/irrational classifier.
   No inhabitant of [classifier] is postulated or constructed here.
   In particular this file does not prove that classification is computable.
   The record representation below contains a checked lowest-terms condition;
   "rational" must not mean an arbitrary unreduced numerator/denominator. *)

type fraction = {
  numerator: int;
  denominator: d:pos{G.reduced numerator d}
}

let value (r:fraction) : real =
  of_int r.numerator /. of_int r.denominator

let normalize (p:int) (q:pos) : fraction =
  G.reduce_ok p q;
  let g = G.gcd p q in
  { numerator = p / g; denominator = q / g }

let normalize_value (p:int) (q:pos)
  : Lemma (value (normalize p q) == of_int p /. of_int q) =
  G.reduce_ok p q

let fraction_unique (r s:fraction)
  : Lemma (requires value r == value s)
          (ensures r == s) =
  assert (r.numerator * s.denominator == s.numerator * r.denominator);
  G.den_eq r.numerator r.denominator s.numerator s.denominator;
  assert (r.numerator == s.numerator)

(* Keep cast normalization and field division separate from fraction/gcd
   normalization. In particular do not unfold [normalize] into this query. *)
#push-options "--fuel 0 --ifuel 0"
let integer_product_cast (a b:int)
  : Lemma (of_int (a*b) == of_int a *. of_int b) = ()

let field_fraction_equivalent
    (a:real) (b:real{b =!= zero}) (u:real) (v:real{v =!= zero})
  : Lemma (requires a *. v == u *. b)
          (ensures a /. b == u /. v) =
  assert ((a /. b) *. b == a);
  assert ((u /. v) *. v == u);
  assert (b *. v =!= zero);
  assert ((a /. b) *. (b *. v) == a *. v);
  assert ((u /. v) *. (b *. v) == u *. b)

let normalize_equivalent (p u:int) (q v:pos)
  : Lemma (requires p*v == u*q)
          (ensures normalize p q == normalize u v) =
  normalize_value p q;
  normalize_value u v;
  assert (of_int (p*v) == of_int (u*q));
  integer_product_cast p v;
  integer_product_cast u q;
  assert (of_int p *. of_int v == of_int u *. of_int q);
  field_fraction_equivalent (of_int p) (of_int q) (of_int u) (of_int v);
  assert (value (normalize p q) == value (normalize u v));
  fraction_unique (normalize p q) (normalize u v)
#pop-options

let integral (p:int) : fraction =
  G.reduced_den_one p;
  { numerator = p; denominator = 1 }

let integral_value (p:int) : Lemma (value (integral p) == of_int p) = ()

let integral_fields (p:int)
  : Lemma ((integral p).numerator == p /\ (integral p).denominator == 1) = ()

let reduced_unit (q:pos) : Lemma (G.reduced 1 q) =
  if q == 1 then G.reduced_den_one 1
  else begin
    assert (1 % q == 1);
    assert (q % 1 == 0);
    assert (G.gcd_nat 1 0 == 1);
    assert (G.gcd_nat q 1 == G.gcd_nat 1 0);
    assert (G.gcd_nat 1 q == G.gcd_nat q 1)
  end

let unit_fraction (q:pos) : fraction =
  reduced_unit q;
  { numerator = 1; denominator = q }

let unit_value (q:pos)
  : Lemma (value (unit_fraction q) == one /. of_int q) = ()

let reduced_neg (p:int) (q:pos)
  : Lemma (G.reduced (-p) q == G.reduced p q) =
  assert (G.iabs (-p) == G.iabs p);
  assert (G.gcd (-p) q == G.gcd p q)

let negate (r:fraction) : fraction =
  reduced_neg r.numerator r.denominator;
  { numerator = -r.numerator; denominator = r.denominator }

let negate_value (r:fraction)
  : Lemma (value (negate r) == zero -. value r) = ()

let negation_nonzero (y:real{y =!= zero})
  : Lemma (zero -. y =!= zero) = ()

(* Constructor exhaustiveness needs one layer of inductive inversion.
   Keep the preceding field/gcd proofs at ifuel 0; this is not an increase
   of the solver resource limit or recursive-definition fuel. *)
#set-options "--ifuel 1"

type classification =
  | Rational : fraction -> classification
  | Irrational : classification

let represents (c:classification) (y:real) : prop =
  match c with
  | Rational r -> value r == y
  | Irrational -> forall (r:fraction). value r =!= y

type classifier =
  c:(real -> GTot classification){forall (y:real). represents (c y) y}

let rational_value (c:classifier) (y:real) (r:fraction)
  : Lemma (requires c y == Rational r)
          (ensures value r == y) = ()

let negate_fields (r:fraction)
  : Lemma ((negate r).numerator == -r.numerator /\
           (negate r).denominator == r.denominator) = ()

let classify_rational (c:classifier) (r:fraction)
  : Lemma (c (value r) == Rational r) =
  match c (value r) with
  | Rational s -> fraction_unique s r
  | Irrational -> assert (value r =!= value r)

let classification_consistent (c d:classifier) (y:real)
  : Lemma (c y == d y) =
  match c y, d y with
  | Rational r, Rational s -> fraction_unique r s
  | Rational r, Irrational -> assert (value r =!= y)
  | Irrational, Rational s -> assert (value s =!= y)
  | Irrational, Irrational -> ()

let classify_neg (c:classifier) (y:real)
  : Lemma (c (zero -. y) ==
      (match c y with
       | Rational r -> Rational (negate r)
       | Irrational -> Irrational)) =
  match c y with
  | Rational r ->
    negate_value r;
    classify_rational c (negate r)
  | Irrational ->
    (match c (zero -. y) with
     | Irrational -> ()
     | Rational s ->
       negate_value s;
       assert (value (negate s) == y);
       assert (value (negate s) =!= y))

let signed (p:int) (a:real) : real =
  if p % 2 = 0 then a else zero -. a

let signed_even (p:int) (a:real)
  : Lemma (requires p % 2 = 0)
          (ensures signed p a == a) = ()

let negated_base_positive (x:real)
  : Lemma (requires ~(x == zero) /\ ~(x >. zero))
          (ensures zero -. x >. zero) = ()

let power (c:classifier) (x y:real) : GTot real =
  if y == zero then one
  else if x == zero then zero
  else if x >. zero then A.pow x y
  else match c y with
       | Irrational -> zero
       | Rational r ->
         if r.denominator % 2 = 0 then zero
         else (negated_base_positive x; signed r.numerator (A.pow (zero -. x) y))

let zero_exponent (c:classifier) (x:real)
  : Lemma (power c x zero == one) = ()

let zero_base (c:classifier) (y:real)
  : Lemma (power c zero y == (if y == zero then one else zero)) = ()

let positive_base (c:classifier) (x:A.rpos) (y:real)
  : Lemma (power c x y == A.pow x y /\ power c x y >. zero) =
  if y == zero then A.pow_zero x

let one_base (c:classifier) (y:real)
  : Lemma (power c one y == one) =
  positive_base c one y;
  A.pow_one_base y

let negative_rational (c:classifier) (x:real{x <. zero}) (r:fraction)
  : Lemma (power c x (value r) ==
      (if r.denominator % 2 = 0 then zero
       else signed r.numerator (A.pow (zero -. x) (value r)))) =
  classify_rational c r;
  if value r == zero then begin
    integral_value 0;
    fraction_unique r (integral 0);
    integral_fields 0;
    assert (r.numerator == 0);
    assert (r.denominator == 1);
    assert (r.denominator % 2 <> 0);
    zero_exponent c x;
    assert (power c x (value r) == one);
    A.pow_zero (zero -. x);
    assert (A.pow (zero -. x) (value r) == one);
    signed_even r.numerator (A.pow (zero -. x) (value r));
    assert (signed r.numerator (A.pow (zero -. x) (value r)) == one)
  end

let negative_irrational (c:classifier) (x:real{x <. zero}) (y:real)
  : Lemma (requires c y == Irrational)
          (ensures power c x y == zero) =
  integral_value 0;
  classify_rational c (integral 0);
  assert (y =!= zero)

(* This is a property of the exponent VALUE, not of its syntax or of one
   candidate base. In particular an unreduced even written denominator is
   not sufficient evidence for this predicate. *)
let outside_negative_domain (c:classifier) (y:real) : prop =
  match c y with
  | Irrational -> True
  | Rational r -> r.denominator % 2 == 0

let even_fraction_outside (c:classifier) (r:fraction)
  : Lemma (requires r.denominator % 2 == 0)
          (ensures outside_negative_domain c (value r)) =
  classify_rational c r

let irrational_outside (c:classifier) (y:real)
  : Lemma (requires c y == Irrational)
          (ensures outside_negative_domain c y) = ()

let outside_domain_zero (c:classifier) (x:real{x <. zero}) (y:real)
  : Lemma (requires outside_negative_domain c y)
          (ensures power c x y == zero) =
  match c y with
  | Irrational -> negative_irrational c x y
  | Rational r -> negative_rational c x r

(* The normalization step is essential: e.g. 2/6 has even written
   denominator but normalizes to 1/3 and is admitted on a negative base. *)
let rational_rewrite (c:classifier) (x:real{x <. zero}) (p:int) (q:pos)
  : Lemma (power c x (of_int p /. of_int q) ==
      (let r = normalize p q in
       if r.denominator % 2 = 0 then zero
       else signed r.numerator
              (A.pow (zero -. x) (of_int p /. of_int q)))) =
  normalize_value p q;
  negative_rational c x (normalize p q)

let congruence (c:classifier) (x u y v:real)
  : Lemma (requires x == u /\ y == v)
          (ensures power c x y == power c u v) = ()

let independent_of_classifier (c d:classifier) (x y:real)
  : Lemma (power c x y == power d x y) =
  classification_consistent c d y

(* Total inverse is defined explicitly, not confused with field division
   at zero. In particular no expression [one /. zero] is well typed here. *)
let inverse (x:real) : GTot real =
  if x == zero then zero else one /. x

let inverse_zero () : Lemma (inverse zero == zero) = ()
let inverse_one () : Lemma (inverse one == one) = ()

let inverse_nonzero (x:real{x =!= zero})
  : Lemma (inverse x == one /. x) = ()

#push-options "--fuel 0 --ifuel 0"
let field_negative_reciprocal (a:real{a =!= zero})
  : Lemma (one /. (zero -. a) == zero -. (one /. a)) = ()
#pop-options

let signed_reciprocal (p:int) (a:A.rpos)
  : Lemma (signed (-p) (one /. a) == inverse (signed p a)) =
  assert ((-p)%2 == p%2);
  if p%2 == 0 then inverse_nonzero a
  else begin
    assert (zero -. a =!= zero);
    inverse_nonzero (zero -. a);
    field_negative_reciprocal a
  end

(* Use the branch contracts rather than unfolding [power], [negate],
   and the classifier invariant together inside the arithmetic query.
   Each branch is a separate VC, including the two denominator parities.
   The public dispatcher only combines already-proved equalities. *)
#push-options "--fuel 0 --ifuel 1"
let reciprocal_at_zero_exponent (c:classifier) (x:real)
  : Lemma (power c x (zero -. zero) == inverse (power c x zero)) =
  zero_exponent c x;
  inverse_one ()

let reciprocal_at_zero_base (c:classifier) (y:real{y =!= zero})
  : Lemma (power c zero (zero -. y) == inverse (power c zero y)) =
  negation_nonzero y;
  zero_base c y;
  zero_base c (zero -. y);
  inverse_zero ()

let reciprocal_at_positive_base (c:classifier) (x:A.rpos) (y:real)
  : Lemma (power c x (zero -. y) == inverse (power c x y)) =
  positive_base c x y;
  positive_base c x (zero -. y);
  A.pow_neg x y;
  inverse_nonzero (A.pow x y)

let reciprocal_at_irrational (c:classifier) (x:real{x <. zero}) (y:real)
  : Lemma (requires c y == Irrational)
          (ensures power c x (zero -. y) == inverse (power c x y)) =
  classify_neg c y;
  negative_irrational c x y;
  negative_irrational c x (zero -. y);
  inverse_zero ()

let reciprocal_at_even_fraction (c:classifier) (x:real{x <. zero})
    (r:fraction{r.denominator%2 == 0})
  : Lemma (power c x (zero -. value r) == inverse (power c x (value r))) =
  negate_value r;
  negate_fields r;
  negative_rational c x r;
  negative_rational c x (negate r);
  assert (power c x (value r) == zero);
  assert (power c x (zero -. value r) == zero);
  inverse_zero ()

let reciprocal_at_odd_fraction (c:classifier) (x:real{x <. zero})
    (r:fraction{r.denominator%2 <> 0})
  : Lemma (power c x (zero -. value r) == inverse (power c x (value r))) =
  negate_value r;
  negate_fields r;
  negative_rational c x r;
  negative_rational c x (negate r);
  assert (power c x (value r) ==
          signed r.numerator (A.pow (zero -. x) (value r)));
  A.pow_neg (zero -. x) (value r);
  assert (power c x (zero -. value r) ==
          signed (-r.numerator) (one /. A.pow (zero -. x) (value r)));
  signed_reciprocal r.numerator (A.pow (zero -. x) (value r));
  assert (power c x (zero -. value r) == inverse (power c x (value r)))

let reciprocal_at_fraction (c:classifier) (x:real{x <. zero}) (r:fraction)
  : Lemma (power c x (zero -. value r) == inverse (power c x (value r))) =
  if r.denominator%2 == 0 then reciprocal_at_even_fraction c x r
  else reciprocal_at_odd_fraction c x r

let reciprocal_at_negative_base (c:classifier) (x:real{x <. zero}) (y:real)
  : Lemma (power c x (zero -. y) == inverse (power c x y)) =
  match c y with
  | Irrational -> reciprocal_at_irrational c x y
  | Rational r ->
    rational_value c y r;
    reciprocal_at_fraction c x r;
    assert (power c x (zero -. y) == inverse (power c x y))

let reciprocal (c:classifier) (x y:real)
  : Lemma (power c x (zero -. y) == inverse (power c x y)) =
  if y == zero then reciprocal_at_zero_exponent c x
  else if x == zero then reciprocal_at_zero_base c y
  else if x >. zero then reciprocal_at_positive_base c x y
  else reciprocal_at_negative_base c x y
#pop-options

let guarded_reciprocal (c:classifier) (x y:real)
  : Lemma (requires power c x y =!= zero)
          (ensures power c x (zero -. y) == one /. power c x y) =
  reciprocal c x y;
  inverse_nonzero (power c x y)

let positive_nested (c:classifier) (x:A.rpos) (y z:real)
  : Lemma (power c (power c x y) z == power c x (y *. z)) =
  positive_base c x y;
  positive_base c (A.pow x y) z;
  positive_base c x (y *. z);
  A.pow_pow x y z

let rec natural_positive (x:A.rpos) (n:nat)
  : Lemma (ensures A.pow x (of_int n) == N.ipow x n)
          (decreases n) =
  if n == 0 then A.pow_zero x
  else begin
    natural_positive x (n-1);
    A.pow_succ x (n-1)
  end

let rec natural_sign (x:real) (n:nat)
  : Lemma (ensures N.ipow (zero -. x) n == signed n (N.ipow x n))
          (decreases n) =
  if n > 0 then begin
    natural_sign x (n-1);
    assert ((n-1)%2 == (if n%2 == 0 then 1 else 0))
  end

let natural_bridge (c:classifier) (x:real) (n:nat)
  : Lemma (power c x (of_int n) == N.ipow x n) =
  integral_value n;
  if n == 0 then ()
  else if x == zero then N.power_zero_base n
  else if x >. zero then begin
    positive_base c x (of_int n);
    natural_positive x n
  end
  else begin
    negative_rational c x (integral n);
    natural_positive (zero -. x) n;
    natural_sign (zero -. x) n
  end

let negative_integer (c:classifier) (x:real) (n:pos)
  : Lemma (power c x (zero -. of_int n) == inverse (N.ipow x n)) =
  natural_bridge c x n;
  reciprocal c x (of_int n)

let one_exponent (c:classifier) (x:real)
  : Lemma (power c x one == x) =
  natural_bridge c x 1;
  N.power_one x
