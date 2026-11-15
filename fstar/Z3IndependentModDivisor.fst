module Z3IndependentModDivisor

module E = FStar.Math.Euclid
module M = FStar.Math.Lemmas
module F = FStar.Math.Fermat
module P = Z3IndependentModPow
module O = Z3IndependentModOrder

let lemma_residue_divisor (x:int) (n d:pos)
  : Lemma (requires E.divides d n)
          (ensures (x % n) % d == x % d) =
  E.divides_mod n d;
  M.euclidean_division_definition n d;
  M.nat_over_pos_is_nat n d;
  assert (n / d > 0);
  M.modulo_modulo_lemma x d (n / d)

let impossible_unit (d:int{d > 1})
  : Lemma (requires d == 1 \/ d == -1) (ensures False) = ()

let lemma_coprime_nonunit (x:int) (n:pos) (d:int{d > 1})
  : Lemma (requires E.divides d n /\ E.is_gcd (x - 1) n 1)
          (ensures x % d <> 1) =
  if x % d = 1 then (
    M.lemma_mod_add_distr (-1) x d;
    M.small_mod 0 d;
    assert ((x - 1) % d == 0);
    E.mod_divides (x - 1) d;
    assert (E.divides d 1);
    E.divides_1 d;
    impossible_unit d)

let rec lemma_multiple_is_period (a:int) (p:int{p > 1}) (period:pos) (n:nat)
  : Lemma (requires F.pow a period % p == 1 /\ n % period == 0)
          (ensures F.pow a n % p == 1)
          (decreases n) =
  if n = 0 then M.small_mod 1 p
  else (
    M.lemma_mod_lt n period;
    if n < period then M.small_mod n period;
    M.lemma_mod_sub n period 1;
    lemma_multiple_is_period a p period (n - period);
    P.lemma_pow_plus a period (n - period);
    M.lemma_mod_mul_distr_l (F.pow a period) (F.pow a (n - period)) p)

let lemma_coprime_excludes_period (a:int) (n:pos) (d:int{d > 1})
  (period:pos) (v:nat)
  : Lemma (requires E.divides d n /\ F.pow a period % d == 1 /\
                    E.is_gcd (F.pow a v - 1) n 1)
          (ensures v % period <> 0) =
  lemma_coprime_nonunit (F.pow a v) n d;
  if v % period = 0 then lemma_multiple_is_period a d period v

let prime_divisor_period (n:int{n > 1}) (a:int) (e:pos{F.pow a e % n == 1})
  (r:int{E.is_prime r /\ E.divides r n})
  : GTot (k:pos{k <= e /\ e % k == 0 /\ (r - 1) % k == 0 /\
      F.pow a k % r == 1}) =
  lemma_residue_divisor (F.pow a e) n r;
  M.small_mod 1 r;
  if a % r = 0 then (
    M.lemma_mod_mul_distr_l a (F.pow a (e - 1)) r;
    assert (F.pow a e % r == 0));
  O.prime_period r a e
