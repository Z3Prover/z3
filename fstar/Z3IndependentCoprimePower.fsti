module Z3IndependentCoprimePower

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat

val coprime_power (a:int) (e:nat) (n:int{n > 1})
  : Tot (ok:bool{ok ==> E.is_gcd (F.pow a e - 1) n 1})
