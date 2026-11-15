module Z3IndependentModDivisor

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat

val lemma_residue_divisor (x:int) (n d:pos)
  : Lemma (requires E.divides d n)
          (ensures (x % n) % d == x % d)

val lemma_coprime_nonunit (x:int) (n:pos) (d:int{d > 1})
  : Lemma (requires E.divides d n /\ E.is_gcd (x - 1) n 1)
          (ensures x % d <> 1)

val lemma_multiple_is_period (a:int) (p:int{p > 1}) (period:pos) (n:nat)
  : Lemma (requires F.pow a period % p == 1 /\ n % period == 0)
          (ensures F.pow a n % p == 1)

val lemma_coprime_excludes_period (a:int) (n:pos) (d:int{d > 1})
  (period:pos) (v:nat)
  : Lemma (requires E.divides d n /\ F.pow a period % d == 1 /\
                    E.is_gcd (F.pow a v - 1) n 1)
          (ensures v % period <> 0)

val prime_divisor_period (n:int{n > 1}) (a:int) (e:pos{F.pow a e % n == 1})
  (r:int{E.is_prime r /\ E.divides r n})
  : GTot (k:pos{k <= e /\ e % k == 0 /\ (r - 1) % k == 0 /\
      F.pow a k % r == 1})
