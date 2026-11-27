module Z3IndependentPrimeDivisor

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat

val prime_divisor (n:int{n > 1})
  : GTot (p:int{E.is_prime p /\ E.divides p n /\ p <= n})

val proper_factor (e:pos) (k:pos{k < e /\ e % k == 0})
  : GTot (q:int{E.is_prime q /\ e % q == 0 /\ (e / q) % k == 0})

val lemma_lucas (n:int{n > 1}) (a:int)
  : Lemma
      (requires F.pow a (n - 1) % n == 1 /\
        (forall (q:int). E.is_prime q /\ (n - 1) % q == 0 ==>
          E.is_gcd (F.pow a ((n - 1) / q) - 1) n 1))
      (ensures E.is_prime n)
