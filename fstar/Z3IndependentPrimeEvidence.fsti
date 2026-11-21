module Z3IndependentPrimeEvidence

module E = FStar.Math.Euclid

let max_modulus : nat =
  115792089237316195423570985008687907853269984665640564039457584007913129639936

val check (n a:int) (xs:list int)
  : Tot (ok:bool{ok ==> n >= 2 /\ n <= max_modulus /\ E.is_prime n})
