module Z3IndependentModOrder

module F = FStar.Math.Fermat
module E = FStar.Math.Euclid

val least_period (a:int) (p:int{p > 1})
  (n:pos{F.pow a n % p == 1})
  : GTot (k:pos{k <= n /\ F.pow a k % p == 1 /\
      (forall (m:nat). 0 < m /\ m < k ==> F.pow a m % p <> 1)})

val lemma_pow_reduce (a:int) (p:int{p > 1}) (period:pos) (n:nat)
  : Lemma (requires F.pow a period % p == 1 /\ F.pow a n % p == 1)
          (ensures F.pow a (n % period) % p == 1)

val lemma_period_divides (a:int) (p:int{p > 1}) (period:pos) (n:nat)
  : Lemma
      (requires F.pow a period % p == 1 /\ F.pow a n % p == 1 /\
        (forall (m:nat). 0 < m /\ m < period ==> F.pow a m % p <> 1))
      (ensures n % period == 0)

val prime_period (r:int{E.is_prime r}) (a:int{a % r <> 0})
  (n:pos{F.pow a n % r == 1})
  : GTot (k:pos{k <= n /\ n % k == 0 /\ (r - 1) % k == 0 /\
      F.pow a k % r == 1 /\
      (forall (m:nat). 0 < m /\ m < k ==> F.pow a m % r <> 1)})
