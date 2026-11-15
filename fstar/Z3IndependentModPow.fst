module Z3IndependentModPow

module F = FStar.Math.Fermat
module M = FStar.Math.Lemmas

let rec lemma_pow_plus (a:int) (n m:nat)
  : Lemma (F.pow a (n + m) == F.pow a n * F.pow a m)
          (decreases n) =
  if n > 0 then lemma_pow_plus a (n - 1) m

let rec pow_mod (a:int) (e:nat) (p:pos)
  : Tot (r:int{0 <= r /\ r < p /\ r == F.pow a e % p})
        (decreases e) =
  if e = 0 then (
    M.lemma_mod_lt 1 p;
    1 % p)
  else (
    let h = e / 2 in
    let r = pow_mod a h p in
    let sq = (r * r) % p in
    lemma_pow_plus a h h;
    M.lemma_mod_mul_distr_l (F.pow a h) (F.pow a h) p;
    M.lemma_mod_mul_distr_r (F.pow a h % p) (F.pow a h) p;
    M.lemma_mod_lt (r * r) p;
    M.euclidean_division_definition e 2;
    M.lemma_mod_lt e 2;
    assert (sq == F.pow a (h + h) % p);
    if e % 2 = 0 then sq
    else (
      assert (e == h + h + 1);
      assert (F.pow a e == a * F.pow a (h + h));
      M.lemma_mod_mul_distr_r a (F.pow a (h + h)) p;
      M.lemma_mod_lt (a * sq) p;
      (a * sq) % p))
