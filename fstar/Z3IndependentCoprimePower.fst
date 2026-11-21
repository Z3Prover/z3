module Z3IndependentCoprimePower

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat
module M = FStar.Math.Lemmas
module P = Z3IndependentModPow

let lemma_gcd_lift (x:int) (n:pos)
  : Lemma (requires E.is_gcd (x % n - 1) n 1)
          (ensures E.is_gcd (x - 1) n 1) =
  E.is_gcd_symmetric (x % n - 1) n 1;
  M.euclidean_division_definition x n;
  E.is_gcd_plus n (x % n - 1) (x / n) 1;
  E.is_gcd_symmetric n (x - 1) 1

let coprime_power (a:int) (e:nat) (n:int{n > 1})
  : Tot (ok:bool{ok ==> E.is_gcd (F.pow a e - 1) n 1}) =
  let r = P.pow_mod a e n in
  let _, _, g = E.euclid_gcd (r - 1) n in
  if g = 1 then (
    lemma_gcd_lift (F.pow a e) n;
    true)
  else false
