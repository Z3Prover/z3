module Z3RealPowerGraphs

open FStar.Real
module R = Z3RealPower
module A = FStar.Math.Pow
module N = Z3ArithRewriterPower

#set-options "--fuel 2 --ifuel 0 --z3rlimit 10 --smtencoding.nl_arith_repr native"

(* Purification is a UNIQUE graph, not just an equation. An even root of a
   negative real is the designated zero value, not an unconstrained symbol.
   The even nonnegative branch also requires k >= 0. *)
let root_graph (x:real) (n:pos) (k:real) : prop =
  if n % 2 <> 0 then N.ipow k n == x
  else if x >=. zero then N.ipow k n == x /\ k >=. zero
  else k == zero

let root (x:real) (n:pos) : GTot real =
  if x == zero then zero
  else if x >. zero then A.pow x (one /. of_int n)
  else if n % 2 = 0 then zero
  else zero -. A.pow (zero -. x) (one /. of_int n)

let root_satisfies (x:real) (n:pos)
  : Lemma (root_graph x n (root x n)) =
  if x == zero then N.power_zero_base n
  else if x >. zero then begin
    A.pow_rational x 1 n;
    R.natural_positive (A.pow x (one /. of_int n)) n;
    R.natural_positive x 1;
    N.power_one x
  end
  else if n % 2 <> 0 then begin
    let a = zero -. x in
    A.pow_rational a 1 n;
    R.natural_positive (A.pow a (one /. of_int n)) n;
    R.natural_positive a 1;
    N.power_one a;
    R.natural_sign (A.pow a (one /. of_int n)) n
  end

let root_is_total_power (c:R.classifier) (x:real) (n:pos)
  : Lemma (root x n == R.power c x (one /. of_int n)) =
  R.unit_value n;
  assert (one /. of_int n >. zero);
  if x == zero then R.zero_base c (one /. of_int n)
  else if x >. zero then R.positive_base c x (one /. of_int n)
  else R.negative_rational c x (R.unit_fraction n)

let rec natural_nonnegative (x:real{x >=. zero}) (n:nat)
  : Lemma (ensures N.ipow x n >=. zero) (decreases n) =
  if n > 0 then natural_nonnegative x (n-1)

let rec natural_strict (x z:real) (n:pos)
  : Lemma (requires zero <=. x /\ x <. z)
          (ensures N.ipow x n <. N.ipow z n)
          (decreases n) =
  if n == 1 then begin N.power_one x; N.power_one z end
  else begin
    natural_strict x z (n-1);
    natural_nonnegative x (n-1);
    assert (N.ipow z (n-1) >. zero);
    assert (x *. N.ipow x (n-1) <=. x *. N.ipow z (n-1));
    assert (x *. N.ipow z (n-1) <. z *. N.ipow z (n-1))
  end

let nonnegative_injective (u v:real) (n:pos)
  : Lemma (requires u >=. zero /\ v >=. zero /\ N.ipow u n == N.ipow v n)
          (ensures u == v) =
  if u <. v then natural_strict u v n
  else if v <. u then natural_strict v u n

let odd_injective (u v:real) (n:pos{n%2 <> 0})
  : Lemma (requires N.ipow u n == N.ipow v n)
          (ensures u == v) =
  if u >=. zero && v >=. zero then nonnegative_injective u v n
  else if u <=. zero && v <=. zero then begin
    R.natural_sign (zero -. u) n;
    R.natural_sign (zero -. v) n;
    nonnegative_injective (zero -. u) (zero -. v) n
  end
  else if u <. zero then begin
    R.natural_sign (zero -. u) n;
    natural_strict zero (zero -. u) n;
    N.power_zero_base n;
    natural_nonnegative v n
  end
  else begin
    R.natural_sign (zero -. v) n;
    natural_strict zero (zero -. v) n;
    N.power_zero_base n;
    natural_nonnegative u n
  end

let root_unique (x:real) (n:pos) (u v:real)
  : Lemma (requires root_graph x n u /\ root_graph x n v)
          (ensures u == v) =
  if n%2 <> 0 then odd_injective u v n
  else if x >=. zero then nonnegative_injective u v n

let purification_exact (x:real) (n:pos) (k:real)
  : Lemma (root_graph x n k <==> k == root x n) =
  root_satisfies x n;
  if root_graph x n k then root_unique x n k (root x n)

(* The shared rational-power graph is valid for a REDUCED exponent m/q.
   For an even q the negative-base branch is p=0; the equation p^q=x^m
   is intentionally NOT asserted there. m must be strictly positive:
   m=0 would instead invoke the unconditional exponent-zero rule. *)
let rational_graph (x p:real) (m q:pos) : prop =
  if q%2 <> 0 then N.ipow p q == N.ipow x m
  else if x >=. zero then N.ipow p q == N.ipow x m /\ p >=. zero
  else p == zero

let shared_rational_graph (c:R.classifier) (x:real)
    (r:R.fraction{r.numerator > 0})
  : Lemma (rational_graph x (R.power c x (R.value r))
                     r.numerator r.denominator) =
  let m = r.numerator in
  let q = r.denominator in
  assert (R.value r >. zero);
  if x == zero then begin
    R.zero_base c (R.value r);
    N.power_zero_base m;
    N.power_zero_base q
  end
  else if x >. zero then begin
    R.positive_base c x (R.value r);
    A.pow_rational x m q;
    R.natural_positive (A.pow x (R.value r)) q;
    R.natural_positive x m
  end
  else begin
    R.negative_rational c x r;
    if q%2 <> 0 then begin
      let a = zero -. x in
      A.pow_rational a m q;
      R.natural_positive (A.pow a (R.value r)) q;
      R.natural_positive a m;
      R.natural_sign a m;
      if m%2 <> 0 then R.natural_sign (A.pow a (R.value r)) q
    end
  end

(* Odd-power injectivity gives uniqueness even when m is even.
   Even q requires the nonnegative-result guard. *)
let rational_graph_unique (x u v:real) (m q:pos)
  : Lemma (requires rational_graph x u m q /\ rational_graph x v m q)
          (ensures u == v) =
  if q%2 <> 0 then odd_injective u v q
  else if x >=. zero then nonnegative_injective u v q

let exact_rational_refinement (c:R.classifier) (x:real)
    (r:R.fraction{r.numerator > 0}) (candidate:real)
  : Lemma (requires rational_graph x candidate r.numerator r.denominator)
          (ensures candidate == R.power c x (R.value r)) =
  shared_rational_graph c x r;
  rational_graph_unique x candidate (R.power c x (R.value r))
    r.numerator r.denominator

let shared_bounds (c:R.classifier) (x y p:real)
  : Lemma (requires p == R.power c x y)
          (ensures
            (y == zero ==> p == one) /\
            (x == zero /\ y =!= zero ==> p == zero) /\
            (x == one ==> p == one) /\
            (x >. zero ==> p >. zero)) =
  R.zero_exponent c x;
  R.zero_base c y;
  R.one_base c y;
  if x >. zero then R.positive_base c x y

(* Generic exact-value validation boundary. The checker must supply an
   equality established by exact evaluation, NOT a mere proposed value.
   The grounded lemma constrains only the matching pair of operands. *)
let exact_refinement (c:R.classifier) (a b expected x y p:real)
  : Lemma (requires expected == R.power c a b /\
                    (x == a /\ y == b ==> p == expected))
          (ensures x == a /\ y == b ==> p == R.power c x y) = ()

let exclude_mismatch (c:R.classifier) (a b expected candidate:real)
  : Lemma (requires expected == R.power c a b /\ candidate =!= expected)
          (ensures ~(candidate == R.power c a b)) = ()

(* Generalized exact-model refinement: fix ONLY the exponent b.
   There is deliberately no guard x=a for a particular model base.
   This covers every negative base simultaneously and therefore does not
   enumerate infinitely many negative model values.

   For an irrational algebraic b the exact evaluator must establish
   c b = Irrational (e.g. from a separately checked algebraic certificate).
   No algebraic-number representation or irrationality oracle is assumed
   here. For a rational b, [even_fraction_outside] supplies the obligation
   from its reduced, positive-denominator representative. *)
let negative_domain_guard (c:R.classifier) (b x y:real)
  : Lemma (requires R.outside_negative_domain c b)
          (ensures x <. zero /\ y == b ==> R.power c x y == zero) =
  if x <. zero && y == b then R.outside_domain_zero c x b

let negative_domain_lemma (c:R.classifier) (b:real)
  : Lemma (requires R.outside_negative_domain c b)
          (ensures forall (x:real). forall (y:real).
            x <. zero /\ y == b ==> R.power c x y == zero) =
  introduce forall (x:real) (y:real).
    (x <. zero /\ y == b ==> R.power c x y == zero)
  with negative_domain_guard c b x y

let negative_domain_refinement (c:R.classifier) (b x y p:real)
  : Lemma (requires R.outside_negative_domain c b /\
                    (x <. zero /\ y == b ==> p == zero))
          (ensures x <. zero /\ y == b ==> p == R.power c x y) =
  negative_domain_guard c b x y

let negative_domain_excludes_mismatch (c:R.classifier)
    (b:real) (x:real{x <. zero}) (candidate:real)
  : Lemma (requires R.outside_negative_domain c b /\ candidate =!= zero)
          (ensures candidate =!= R.power c x b) =
  R.outside_domain_zero c x b

(* [guard] can be a rational-coefficient polynomial equation together with
   rational isolating-interval bounds. Its correctness is a PREMISE:
   this module does not check the extraction of coefficients/endpoints
   from a native algebraic numeral, nor manufacture a root certificate.
   Both existence at b and uniqueness within the guard are necessary. *)
let isolates_value (guard:real -> prop) (b:real) : prop =
  guard b /\ (forall (z:real). guard z ==> z == b)

let isolation_guard_equivalent (guard:real -> prop) (b y:real)
  : Lemma (requires isolates_value guard b)
          (ensures guard y <==> y == b) =
  if guard y then assert (y == b)

(* Replace an unsupported equality y=b by the certified polynomial/interval
   predicate. The base is still guarded ONLY by x<0, never by x=a. *)
let negative_domain_isolation_guard (c:R.classifier) (guard:real -> prop)
    (b x y:real)
  : Lemma (requires isolates_value guard b /\ R.outside_negative_domain c b)
          (ensures x <. zero /\ guard y ==> R.power c x y == zero) =
  isolation_guard_equivalent guard b y;
  negative_domain_guard c b x y

let isolation_guard_refinement (c:R.classifier) (guard:real -> prop)
    (b x y p:real)
  : Lemma (requires
             isolates_value guard b /\ R.outside_negative_domain c b /\
             (x <. zero /\ guard y ==> p == zero))
          (ensures x <. zero /\ guard y ==> p == R.power c x y) =
  negative_domain_isolation_guard c guard b x y

let exact_root_refinement (x:real) (n:pos) (candidate:real)
  : Lemma (requires root_graph x n candidate)
          (ensures candidate == root x n) =
  purification_exact x n candidate
