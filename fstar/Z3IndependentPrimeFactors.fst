module Z3IndependentPrimeFactors

module E = FStar.Math.Euclid
module L = FStar.List.Tot
module F = FStar.Math.Fermat
module C = FStar.Classical
module P = Z3IndependentPrimeDivisor

let rec lemma_factor_member (q:int{E.is_prime q}) (xs:list int)
  : Lemma (requires (forall (x:int). L.mem x xs ==> E.is_prime x) /\
                    E.divides q (product xs))
          (ensures L.mem q xs)
          (decreases xs) =
  match xs with
  | [] -> E.divides_1 q
  | x :: rest ->
    E.divides_mod (x * product rest) q;
    E.euclid_prime q x (product rest);
    if x % q = 0 then (
      E.mod_divides x q;
      assert (E.is_prime x);
      assert (q == x))
    else (
      E.mod_divides (product rest) q;
      lemma_factor_member q rest)

let lemma_factor_lucas (n:int{n > 1}) (a:int) (xs:list int)
  : Lemma
      (requires product xs == n - 1 /\ F.pow a (n - 1) % n == 1 /\
        (forall (q:int). L.mem q xs ==> E.is_prime q) /\
        (forall (q:int). L.mem q xs /\ E.is_prime q ==>
          E.is_gcd (F.pow a ((n - 1) / q) - 1) n 1))
      (ensures E.is_prime n) =
  let aux (q:int) : Lemma
    (E.is_prime q /\ (n - 1) % q == 0 ==>
     E.is_gcd (F.pow a ((n - 1) / q) - 1) n 1) =
    let given () : Lemma
      (requires E.is_prime q /\ (n - 1) % q == 0)
      (ensures L.mem q xs) =
      E.mod_divides (n - 1) q;
      lemma_factor_member q xs in
    C.move_requires given () in
  C.forall_intro aux;
  P.lemma_lucas n a
