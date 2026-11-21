module Z3IndependentModOrder

module F = FStar.Math.Fermat
module M = FStar.Math.Lemmas
module E = FStar.Math.Euclid
module P = Z3IndependentModPow
module C = FStar.Classical

let rec find_period (a:int) (p:int{p > 1})
  (n:pos{F.pow a n % p == 1}) (i:pos{i <= n})
  : GTot (k:pos{i <= k /\ k <= n /\ F.pow a k % p == 1 /\
      (forall (m:nat). i <= m /\ m < k ==> F.pow a m % p <> 1)})
      (decreases (n - i)) =
  if F.pow a i % p == 1 then i
  else (
    let k = find_period a p n (i + 1) in
    let aux (m:nat) : Lemma
      (i <= m /\ m < k ==> F.pow a m % p <> 1) =
      if m = i then () else () in
    C.forall_intro aux;
    k)

let least_period (a:int) (p:int{p > 1})
  (n:pos{F.pow a n % p == 1})
  : GTot (k:pos{k <= n /\ F.pow a k % p == 1 /\
      (forall (m:nat). 0 < m /\ m < k ==> F.pow a m % p <> 1)}) =
  find_period a p n 1

let rec lemma_pow_reduce (a:int) (p:int{p > 1}) (period:pos) (n:nat)
  : Lemma (requires F.pow a period % p == 1 /\ F.pow a n % p == 1)
          (ensures F.pow a (n % period) % p == 1)
          (decreases n) =
  if n < period then M.small_mod n period
  else (
    P.lemma_pow_plus a period (n - period);
    M.lemma_mod_mul_distr_l (F.pow a period) (F.pow a (n - period)) p;
    M.lemma_mod_sub n period 1;
    lemma_pow_reduce a p period (n - period))

let lemma_period_divides (a:int) (p:int{p > 1}) (period:pos) (n:nat)
  : Lemma
      (requires F.pow a period % p == 1 /\ F.pow a n % p == 1 /\
        (forall (m:nat). 0 < m /\ m < period ==> F.pow a m % p <> 1))
      (ensures n % period == 0) =
  lemma_pow_reduce a p period n;
  M.lemma_mod_lt n period

let prime_period (r:int{E.is_prime r}) (a:int{a % r <> 0})
  (n:pos{F.pow a n % r == 1})
  : GTot (k:pos{k <= n /\ n % k == 0 /\ (r - 1) % k == 0 /\
      F.pow a k % r == 1 /\
      (forall (m:nat). 0 < m /\ m < k ==> F.pow a m % r <> 1)}) =
  let k = least_period a r n in
  F.fermat_alt r a;
  lemma_period_divides a r k n;
  lemma_period_divides a r k (r - 1);
  k
