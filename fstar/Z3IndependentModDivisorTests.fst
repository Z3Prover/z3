module Z3IndependentModDivisorTests

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat
module P = Z3IndependentFiniteFieldPrime
module D = Z3IndependentModDivisor

let divisor_period () : Lemma (ensures True) =
  if P.small_prime 3 then (
    assert_norm (15 % 3 == 0);
    E.mod_divides 15 3;
    D.lemma_residue_divisor (-23) 15 3;
    assert_norm (F.pow 2 4 % 15 == 1 /\ F.pow 2 1 == 2);
    E.is_gcd_1 15;
    E.is_gcd_symmetric 15 1 1;
    let k = D.prime_divisor_period 15 2 4 3 in
    D.lemma_coprime_excludes_period 2 15 3 k 1;
    assert (1 % k <> 0))
