module Z3IndependentFactorPrime

module E = FStar.Math.Euclid
module M = FStar.Math.Lemmas
module C = FStar.Classical
module P = Z3IndependentFiniteFieldPrime

let rec no_factor (p:int) (d:nat) : Tot bool (decreases d) =
  if d < 2 then true
  else p % d <> 0 && no_factor p (d - 1)

let rec lemma_no_factor (p:int) (d:nat) (k:nat)
  : Lemma (requires no_factor p d /\ 2 <= k /\ k <= d)
          (ensures p % k <> 0)
          (decreases d) =
  if k < d then lemma_no_factor p (d - 1) k

let lemma_bounded_positive_divisor (p:pos{p <= max_factor}) (d:pos)
  : Lemma (requires no_factor p 16384 /\ E.divides d p)
          (ensures d == 1 \/ d == p) =
  E.divides_mod p d;
  if d > p then M.small_mod p d
  else if d > 1 && d < p then (
    if d <= 16384 then lemma_no_factor p 16384 d
    else (
      M.euclidean_division_definition p d;
      M.nat_over_pos_is_nat p d;
      let q = p / d in
      if q >= 16385 then (
        M.lemma_mult_le_right q 16385 d;
        M.lemma_mult_le_left 16385 16385 q);
      assert (q >= 2 /\ q <= 16384);
      assert (E.divides q p);
      E.divides_mod p q;
      lemma_no_factor p 16384 q))

let lemma_bounded_prime (p:int{p > 1 /\ p <= max_factor})
  : Lemma (requires no_factor p 16384)
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

let factor_prime (p:int)
  : Tot (ok:bool{ok ==> 2 <= p /\ p <= max_factor /\ E.is_prime p}) =
  if p < 2 || p > max_factor then false
  else if p <= 65536 then P.small_prime p
  else if no_factor p 16384 then (lemma_bounded_prime p; true)
  else false
