module Z3IndependentModOrderTests

module F = FStar.Math.Fermat
module P = Z3IndependentFiniteFieldPrime
module O = Z3IndependentModOrder

let composite_period () : Lemma (ensures True) =
  assert_norm (F.pow 2 4 % 15 == 1 /\ F.pow 2 12 % 15 == 1);
  assert_norm (F.pow 2 1 % 15 <> 1 /\ F.pow 2 2 % 15 <> 1 /\
               F.pow 2 3 % 15 <> 1);
  let k = O.least_period 2 15 4 in
  assert (k == 4);
  O.lemma_period_divides 2 15 k 12

let prime_period () : Lemma (ensures True) =
  if P.small_prime 13 then (
    assert_norm (2 % 13 <> 0 /\ F.pow 2 12 % 13 == 1);
    let k = O.prime_period 13 2 12 in
    assert (12 % k == 0))
