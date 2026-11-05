module Z3RealPowerTests

open FStar.Real
module R = Z3RealPower
module G = Z3RealPowerGraphs
module N = Z3ArithRewriterPower

#set-options "--fuel 2 --ifuel 0 --z3rlimit 10 --smtencoding.nl_arith_repr native"

(* All semantic tests are conditional on the explicit classifier parameter.
   None fabricate a classifier or a positive-power analytic axiom. *)
let zero_zero (c:R.classifier)
  : Lemma (R.power c zero zero == one) =
  R.zero_exponent c zero

let zero_negative (c:R.classifier)
  : Lemma (R.power c zero (zero -. one) == zero) =
  R.zero_base c (zero -. one)

let real_reciprocal (c:R.classifier)
  : Lemma (R.power c 2.0R (zero -. one) == 0.5R) =
  R.one_exponent c 2.0R;
  R.guarded_reciprocal c 2.0R one

let cube_candidate ()
  : Lemma (G.root_graph (zero -. 8.0R) 3 (zero -. 2.0R)) =
  N.power_one (zero -. 2.0R);
  assert (N.ipow (zero -. 2.0R) 2 == 4.0R);
  assert (N.ipow (zero -. 2.0R) 3 == zero -. 8.0R)

let negative_cube_root (c:R.classifier)
  : Lemma (R.power c (zero -. 8.0R) (one /. 3.0R) == zero -. 2.0R) =
  cube_candidate ();
  G.exact_root_refinement (zero -. 8.0R) 3 (zero -. 2.0R);
  G.root_is_total_power c (zero -. 8.0R) 3

let negative_reciprocal_cube_root (c:R.classifier)
  : Lemma (R.power c (zero -. 8.0R) (zero -. (one /. 3.0R)) == zero -. 0.5R) =
  negative_cube_root c;
  R.guarded_reciprocal c (zero -. 8.0R) (one /. 3.0R)

let negative_even_root (c:R.classifier)
  : Lemma (R.power c (zero -. 4.0R) 0.5R == zero /\
           G.root_graph (zero -. 4.0R) 2 zero /\
           ~(G.root_graph (zero -. 4.0R) 2 one)) =
  G.root_is_total_power c (zero -. 4.0R) 2

let half_exponent_generalized_guard (c:R.classifier) (x y:real)
  : Lemma (x <. zero /\ y == 0.5R ==> R.power c x y == zero) =
  R.unit_value 2;
  R.even_fraction_outside c (R.unit_fraction 2);
  G.negative_domain_guard c 0.5R x y

let irrational_generalized_guard (c:R.classifier) (b x y:real)
  : Lemma (requires c b == R.Irrational)
          (ensures x <. zero /\ y == b ==> R.power c x y == zero) =
  R.irrational_outside c b;
  G.negative_domain_guard c b x y

let normalize_two_six ()
  : Lemma (R.normalize 2 6 == R.unit_fraction 3) =
  R.normalize_equivalent 2 1 6 3;
  R.normalize_value 1 3;
  R.unit_value 3;
  R.fraction_unique (R.normalize 1 3) (R.unit_fraction 3)

let unreduced_odd_root (c:R.classifier)
  : Lemma (R.power c (zero -. 8.0R) (2.0R /. 6.0R) == zero -. 2.0R) =
  normalize_two_six ();
  negative_cube_root c

let nested_power_requires_guard (c:R.classifier)
  : Lemma (
      R.power c (R.power c (zero -. one) 2.0R) 0.5R =!=
      R.power c (zero -. one) (2.0R *. 0.5R)) =
  R.natural_bridge c (zero -. one) 2;
  N.power_one (zero -. one);
  assert (N.ipow (zero -. one) 2 == one);
  R.one_base c 0.5R;
  R.one_exponent c (zero -. one)
