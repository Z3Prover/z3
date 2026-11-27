module Z3IndependentModPow

module F = FStar.Math.Fermat

val lemma_pow_plus (a:int) (n m:nat)
  : Lemma (F.pow a (n + m) == F.pow a n * F.pow a m)

val pow_mod (a:int) (e:nat) (p:pos)
  : Tot (r:int{0 <= r /\ r < p /\ r == F.pow a e % p})
