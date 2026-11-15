module Z3IndependentPrimeDivisor

module E = FStar.Math.Euclid
module M = FStar.Math.Lemmas
module C = FStar.Classical
module F = FStar.Math.Fermat
module D = Z3IndependentModDivisor

let rec least_divisor (n:int{n > 1}) (i:int{2 <= i /\ i <= n})
  : GTot (d:int{2 <= d /\ d <= n /\ n % d == 0 /\
      (forall (j:int). i <= j /\ j < d ==> n % j <> 0)})
      (decreases (n - i)) =
  if n % i = 0 then i
  else (
    let d = least_divisor n (i + 1) in
    let aux (j:int) : Lemma
      (i <= j /\ j < d ==> n % j <> 0) =
      if j = i then () else () in
    C.forall_intro aux;
    d)

let prime_divisor (n:int{n > 1})
  : GTot (p:int{E.is_prime p /\ E.divides p n /\ p <= n}) =
  let p = least_divisor n 2 in
  E.mod_divides n p;
  let positive (d:pos) : Lemma
    (requires E.divides d p)
    (ensures d == 1 \/ d == p) =
    E.divides_mod p d;
    if d > p then M.small_mod p d
    else if d > 1 && d < p then (
      E.divides_transitive d p n;
      E.divides_mod n d) in
  let aux (d:int) : Lemma
    (E.divides d p ==> (d == 1 \/ d == -1 \/ d == p \/ d == -p)) =
    let given () : Lemma
      (requires E.divides d p)
      (ensures d == 1 \/ d == -1 \/ d == p \/ d == -p) =
      if d = 0 then ()
      else if d > 0 then positive d
      else (E.divides_opp d p; positive (-d)) in
    C.move_requires given () in
  C.forall_intro aux;
  p

let proper_factor (e:pos) (k:pos{k < e /\ e % k == 0})
  : GTot (q:int{E.is_prime q /\ e % q == 0 /\ (e / q) % k == 0}) =
  M.euclidean_division_definition e k;
  M.nat_over_pos_is_nat e k;
  assert (e / k > 1);
  let t = e / k in
  let q = prime_divisor t in
  E.divides_mod t q;
  M.euclidean_division_definition t q;
  M.nat_over_pos_is_nat t q;
  assert (e == ((t / q) * k) * q);
  M.multiple_division_lemma ((t / q) * k) q;
  M.multiple_modulo_lemma (t / q) k;
  q

let lemma_lucas (n:int{n > 1}) (a:int)
  : Lemma
      (requires F.pow a (n - 1) % n == 1 /\
        (forall (q:int). E.is_prime q /\ (n - 1) % q == 0 ==>
          E.is_gcd (F.pow a ((n - 1) / q) - 1) n 1))
      (ensures E.is_prime n) =
  let e = n - 1 in
  let r = prime_divisor n in
  let k = D.prime_divisor_period n a e r in
  if k < e then (
    let q = proper_factor e k in
    M.nat_over_pos_is_nat e q;
    D.lemma_coprime_excludes_period a n r k (e / q);
    assert False);
  if r < n then M.small_mod (r - 1) e;
  assert (r == n)
