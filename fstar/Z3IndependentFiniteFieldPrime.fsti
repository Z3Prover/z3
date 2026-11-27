module Z3IndependentFiniteFieldPrime

module E = FStar.Math.Euclid

let max_small_modulus : nat = 65536

val small_prime (p:int)
  : Tot (result:bool{result ==> 2 <= p /\ p <= max_small_modulus /\ E.is_prime p})

val witness (p:int{E.is_prime p}) (a b:int)
  : GTot (w:int{0 <= w /\ w < p /\
      ((a - b) % p <> 0 ==> (w * (a - b) - 1) % p == 0)})
