module Z3RealPowerCertificates

open FStar.Real
module R = Z3RealPower

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10 --smtencoding.nl_arith_repr native"

(* A certificate is a predicate on the exponent, not an equality with an
   algebraic numeral. This separates soundness from representability in a
   particular arithmetic backend. Rational coefficients/endpoints suffice.
   The backend must still support the polynomial constraint itself.

   Validity must hold for EVERY value satisfying the guard. Merely knowing
   that the current model's exponent is irrational is not sufficient. *)
let valid_zero_certificate (c:R.classifier) (guard:real -> prop) : prop =
  forall (y:real). guard y ==> R.outside_negative_domain c y

let certified_domain_guard (c:R.classifier) (guard:real -> prop)
    (x y:real)
  : Lemma (requires valid_zero_certificate c guard)
          (ensures x <. zero /\ guard y ==> R.power c x y == zero) =
  if x <. zero && guard y then R.outside_domain_zero c x y

let certified_refinement (c:R.classifier) (guard:real -> prop)
    (x y p:real)
  : Lemma (requires valid_zero_certificate c guard /\
                    (x <. zero /\ guard y ==> p == zero))
          (ensures x <. zero /\ guard y ==> p == R.power c x y) =
  certified_domain_guard c guard x y

(* Increasing coefficient order: [a0;a1;...;an] denotes
   a0 + a1*y + ... + an*y^n, evaluated by Horner's rule. *)
let rec polynomial (coefficients:list int) (y:real)
  : Tot real (decreases coefficients) =
  match coefficients with
  | [] -> zero
  | a::rest -> of_int a +. y *. polynomial rest y

let isolated_polynomial_guard (coefficients:list int)
    (lower upper y:real) : prop =
  polynomial coefficients y == zero /\ lower <. y /\ y <. upper

(* This is an explicit proof obligation, NOT an axiom or a supplied
   irreducibility/rational-root checker. It may be established separately
   by a rational-root theorem, or by a checked algebraic certificate.
   Root uniqueness is unnecessary for this zero-domain implication: all
   roots in the selected interval must be irrational. *)
let excludes_rationals (guard:real -> prop) : prop =
  forall (r:R.fraction). ~(guard (R.value r))

let certified_irrational (c:R.classifier) (guard:real -> prop) (y:real)
  : Lemma (requires excludes_rationals guard /\ guard y)
          (ensures c y == R.Irrational) =
  match c y with
  | R.Irrational -> ()
  | R.Rational r ->
    assert (R.value r == y);
    assert (~(guard (R.value r)))

let irrational_certificate_valid (c:R.classifier) (guard:real -> prop)
  : Lemma (requires excludes_rationals guard)
          (ensures valid_zero_certificate c guard) =
  introduce forall (y:real).
    (guard y ==> R.outside_negative_domain c y)
  with (if guard y then begin
    certified_irrational c guard y;
    R.irrational_outside c y
  end)

let polynomial_domain_guard (c:R.classifier) (coefficients:list int)
    (lower upper x y:real)
  : Lemma (requires excludes_rationals
             (isolated_polynomial_guard coefficients lower upper))
          (ensures
            x <. zero /\
            isolated_polynomial_guard coefficients lower upper y
            ==> R.power c x y == zero) =
  let guard = isolated_polynomial_guard coefficients lower upper in
  irrational_certificate_valid c guard;
  certified_domain_guard c guard x y

let polynomial_mismatch_excluded (c:R.classifier) (coefficients:list int)
    (lower upper:real) (x:real{x <. zero}) (y candidate:real)
  : Lemma (requires
             excludes_rationals
               (isolated_polynomial_guard coefficients lower upper) /\
             isolated_polynomial_guard coefficients lower upper y /\
             candidate =!= zero)
          (ensures candidate =!= R.power c x y) =
  polynomial_domain_guard c coefficients lower upper x y
