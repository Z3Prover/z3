module Z3IndependentPrimeEvidence

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat
module M = FStar.Math.Lemmas
module P = Z3IndependentModPow
module Q = Z3IndependentFactorPrime
module CP = Z3IndependentCoprimePower
module X = Z3IndependentPrimeFactors
module L = FStar.List.Tot
module C = FStar.Classical

let exponent (n:int{n > 1}) (q:int)
  : Tot (e:nat{q > 1 ==> e == (n - 1) / q}) =
  if q > 1 then (
    M.nat_over_pos_is_nat (n - 1) q;
    (n - 1) / q)
  else 0

let good_factor (n:int{n > 1}) (a q:int) : prop =
  E.is_prime q /\ E.is_gcd (F.pow a (exponent n q) - 1) n 1

let lemma_quotient_positive (n q:pos)
  : Lemma (requires n % q == 0) (ensures n / q > 0) =
  M.euclidean_division_definition n q;
  M.nat_over_pos_is_nat n q

let rec check_factors (n:int{n > 1}) (a:int) (remaining:pos)
  (xs:list int) (fuel:nat) (previous:option int)
  : Tot bool (decreases fuel) =
  match xs with
  | [] -> remaining = 1
  | q :: rest ->
    if fuel = 0 then false
    else (
      let next : nat = fuel - 1 in
      if q < 2 then false
      else if remaining % q <> 0 then false
      else if previous <> Some q &&
              (not (Q.factor_prime q) ||
               not (CP.coprime_power a (exponent n q) n)) then false
      else (
        lemma_quotient_positive remaining q;
        check_factors n a (remaining / q) rest next (Some q)))

let rec lemma_check_factors (n:int{n > 1}) (a:int) (remaining:pos)
  (xs:list int) (fuel:nat) (previous:option int)
  : Lemma (requires check_factors n a remaining xs fuel previous /\
                    (match previous with None -> True | Some q -> good_factor n a q))
          (ensures X.product xs == remaining /\
            (forall (q:int). L.mem q xs ==> good_factor n a q))
          (decreases fuel) =
  match xs with
  | [] -> ()
  | q :: rest ->
    assert (fuel > 0);
    let next : nat = fuel - 1 in
    M.euclidean_division_definition remaining q;
    lemma_quotient_positive remaining q;
    lemma_check_factors n a (remaining / q) rest next (Some q);
    assert (X.product xs == q * X.product rest);
    let member (x:int) : Lemma
      (L.mem x xs ==> good_factor n a x) =
      if x = q then () else (
        if L.mem x xs then (
          assert (L.mem x rest);
          assert (good_factor n a x))) in
    C.forall_intro member

let lemma_good_factors (n:int{n > 1}) (a:int) (xs:list int)
  : Lemma (requires (forall (q:int). L.mem q xs ==> good_factor n a q))
          (ensures (forall (q:int). L.mem q xs ==> E.is_prime q) /\
            (forall (q:int). L.mem q xs /\ E.is_prime q ==>
              E.is_gcd (F.pow a ((n - 1) / q) - 1) n 1)) =
  let prime_member (q:int) : Lemma
    (L.mem q xs ==> E.is_prime q) = () in
  C.forall_intro prime_member;
  let gcd_member (q:int) : Lemma
    (L.mem q xs /\ E.is_prime q ==>
      E.is_gcd (F.pow a ((n - 1) / q) - 1) n 1) =
    if q > 1 then (let _ = exponent n q in ()) in
  C.forall_intro gcd_member

let check (n a:int) (xs:list int)
  : Tot (ok:bool{ok ==> n >= 2 /\ n <= max_modulus /\ E.is_prime n}) =
  if n < 2 || n > max_modulus || a < 0 || a >= n then false
  else if P.pow_mod a (n - 1) n <> 1 then false
  else if check_factors n a (n - 1) xs 256 None then (
    lemma_check_factors n a (n - 1) xs 256 None;
    lemma_good_factors n a xs;
    X.lemma_factor_lucas n a xs;
    true)
  else false
