module Z3IndependentFactorPrime

module E = FStar.Math.Euclid

let max_factor : nat = 268435456

val factor_prime (p:int)
  : Tot (ok:bool{ok ==> 2 <= p /\ p <= max_factor /\ E.is_prime p})
