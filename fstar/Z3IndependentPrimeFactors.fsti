module Z3IndependentPrimeFactors

module E = FStar.Math.Euclid
module L = FStar.List.Tot
module F = FStar.Math.Fermat

let rec product (xs:list int) : Tot int (decreases xs) =
  match xs with
  | [] -> 1
  | x :: rest -> x * product rest

val lemma_factor_member (q:int{E.is_prime q}) (xs:list int)
  : Lemma (requires (forall (x:int). L.mem x xs ==> E.is_prime x) /\
                    E.divides q (product xs))
          (ensures L.mem q xs)

val lemma_factor_lucas (n:int{n > 1}) (a:int) (xs:list int)
  : Lemma
      (requires product xs == n - 1 /\ F.pow a (n - 1) % n == 1 /\
        (forall (q:int). L.mem q xs ==> E.is_prime q) /\
        (forall (q:int). L.mem q xs /\ E.is_prime q ==>
          E.is_gcd (F.pow a ((n - 1) / q) - 1) n 1))
      (ensures E.is_prime n)
