module Z3IndependentPrimeFactorsTests

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat
module L = FStar.List.Tot
module C = FStar.Classical
module S = Z3IndependentFiniteFieldPrime
module P = Z3IndependentPrimeFactors

let factor_list_primality () : Lemma (ensures True) =
  if S.small_prime 2 then (
    assert_norm (P.product [2] == 2 /\ F.pow 2 2 % 3 == 1 /\
                 F.pow 2 1 - 1 == 1);
    E.is_gcd_1 3;
    E.is_gcd_symmetric 3 1 1;
    let prime_member (q:int) : Lemma
      (L.mem q [2] ==> E.is_prime q) = () in
    C.forall_intro prime_member;
    let gcd_member (q:int) : Lemma
      (L.mem q [2] /\ E.is_prime q ==>
       E.is_gcd (F.pow 2 (2 / q) - 1) 3 1) =
      if q > 1 then () in
    C.forall_intro gcd_member;
    P.lemma_factor_lucas 3 2 [2])
