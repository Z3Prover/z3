module Z3IndependentFiniteFieldPrime

module E = FStar.Math.Euclid
module M = FStar.Math.Lemmas
module C = FStar.Classical

let rec no_factor (p:int) (d:nat) : Tot bool (decreases d) =
  if d < 2 then true
  else p % d <> 0 && no_factor p (d - 1)

let rec lemma_no_factor (p:int) (d:nat) (k:nat)
  : Lemma (requires no_factor p d /\ 2 <= k /\ k <= d)
          (ensures p % k <> 0)
          (decreases d) =
  if k < d then lemma_no_factor p (d - 1) k

let lemma_positive_divisor (p:pos) (d:pos)
  : Lemma (requires no_factor p (p - 1) /\ E.divides d p)
          (ensures d == 1 \/ d == p) =
  E.divides_mod p d;
  if d > p then M.small_mod p d
  else if d > 1 && d < p then lemma_no_factor p (p - 1) d

let lemma_prime (p:int{p > 1})
  : Lemma (requires no_factor p (p - 1))
          (ensures E.is_prime p) =
  let aux (d:int) : Lemma
    (E.divides d p ==> (d == 1 \/ d == -1 \/ d == p \/ d == -p)) =
    let given () : Lemma
      (requires E.divides d p)
      (ensures d == 1 \/ d == -1 \/ d == p \/ d == -p) =
      if d = 0 then ()
      else if d > 0 then lemma_positive_divisor p d
      else (
        E.divides_opp d p;
        lemma_positive_divisor p (-d)) in
    C.move_requires given () in
  C.forall_intro aux

let lemma_bounded_positive_divisor (p:pos{p <= max_small_modulus}) (d:pos)
  : Lemma (requires no_factor p 256 /\ E.divides d p)
          (ensures d == 1 \/ d == p) =
  E.divides_mod p d;
  if d > p then M.small_mod p d
  else if d > 1 && d < p then (
    if d <= 256 then lemma_no_factor p 256 d
    else (
      M.euclidean_division_definition p d;
      M.nat_over_pos_is_nat p d;
      let q = p / d in
      if q >= 257 then (
        M.lemma_mult_le_right q 257 d;
        M.lemma_mult_le_left 257 257 q);
      assert (q >= 2 /\ q <= 256);
      assert (E.divides q p);
      E.divides_mod p q;
      lemma_no_factor p 256 q))

let lemma_bounded_prime (p:int{257 < p /\ p <= max_small_modulus})
  : Lemma (requires no_factor p 256)
          (ensures E.is_prime p) =
  let aux (d:int) : Lemma
    (E.divides d p ==> (d == 1 \/ d == -1 \/ d == p \/ d == -p)) =
    let given () : Lemma
      (requires E.divides d p)
      (ensures d == 1 \/ d == -1 \/ d == p \/ d == -p) =
      if d = 0 then ()
      else if d > 0 then lemma_bounded_positive_divisor p d
      else (
        E.divides_opp d p;
        lemma_bounded_positive_divisor p (-d)) in
    C.move_requires given () in
  C.forall_intro aux

let small_prime (p:int)
  : Tot (result:bool{result ==> 2 <= p /\ p <= max_small_modulus /\ E.is_prime p}) =
  if p < 2 || p > max_small_modulus then false
  else if p <= 257 then (
    if no_factor p (p - 1) then (lemma_prime p; true) else false)
  else if no_factor p 256 then (lemma_bounded_prime p; true)
  else false

let inverse (p:int{E.is_prime p}) (a:int{a % p <> 0})
  : GTot (x:int{0 <= x /\ x < p /\ (x * a) % p = 1}) =
  let r = a % p in
  M.lemma_mod_lt a p;
  let k, s = E.bezout_prime p r in
  M.lemma_mod_plus (s * r) k p;
  M.lemma_mod_mul_distr_r s a p;
  M.lemma_mod_mul_distr_l s a p;
  M.small_mod 1 p;
  M.lemma_mod_lt s p;
  assert ((s * r + k * p) % p == (s * r) % p);
  s % p

let witness (p:int{E.is_prime p}) (a b:int)
  : GTot (w:int{0 <= w /\ w < p /\
      ((a - b) % p <> 0 ==> (w * (a - b) - 1) % p == 0)}) =
  if (a - b) % p = 0 then 0
  else
    let w = inverse p (a - b) in
    M.lemma_mod_add_distr (-1) (w * (a - b)) p;
    M.lemma_mod_lt (w * (a - b)) p;
    w

let test_gate () : Lemma (
  small_prime 2 /\ small_prime 3 /\ small_prime 5 /\ small_prime 17 /\
  small_prime 257 /\ not (small_prime 0) /\ not (small_prime 1) /\
  not (small_prime 4) /\ not (small_prime 25) /\ not (small_prime 256) /\
  small_prime 263 /\ not (small_prime 258) /\ not (small_prime (-7))) =
  assert_norm (small_prime 2 /\ small_prime 3 /\ small_prime 5 /\ small_prime 17 /\
    small_prime 257 /\ not (small_prime 0) /\ not (small_prime 1) /\
    not (small_prime 4) /\ not (small_prime 25) /\ not (small_prime 256) /\
    small_prime 263 /\ not (small_prime 258) /\ not (small_prime (-7)))
