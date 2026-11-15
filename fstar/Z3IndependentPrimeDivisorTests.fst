module Z3IndependentPrimeDivisorTests

module E = FStar.Math.Euclid
module F = FStar.Math.Fermat
module M = FStar.Math.Lemmas
module C = FStar.Classical
module P = Z3IndependentPrimeDivisor

let three_prime () : Lemma (E.is_prime 3) =
  assert_norm (F.pow 2 2 % 3 == 1 /\ F.pow 2 1 - 1 == 1);
  E.is_gcd_1 3;
  E.is_gcd_symmetric 3 1 1;
  let aux (q:int) : Lemma
    (E.is_prime q /\ 2 % q == 0 ==>
     E.is_gcd (F.pow 2 (2 / q) - 1) 3 1) =
    if q > 1 then (
      M.nat_over_pos_is_nat 2 q;
      let given () : Lemma
        (requires E.is_prime q /\ 2 % q == 0)
        (ensures E.is_gcd (F.pow 2 (2 / q) - 1) 3 1) =
        if q > 2 then M.small_mod 2 q;
        assert (q == 2) in
      C.move_requires given ()) in
  C.forall_intro aux;
  P.lemma_lucas 3 2

let fermat_alone_is_insufficient ()
  : Lemma (F.pow 4 14 % 15 == 1 /\
           not (E.is_gcd (F.pow 4 7 - 1) 15 1)) =
  assert_norm (F.pow 4 14 % 15 == 1 /\ F.pow 4 7 - 1 == 16383 /\
               16383 % 3 == 0 /\ 15 % 3 == 0);
  E.mod_divides 16383 3;
  E.mod_divides 15 3;
  let impossible () : Lemma
    (requires E.is_gcd 16383 15 1)
    (ensures False) =
    assert (E.divides 3 1);
    E.divides_1 3 in
  C.move_requires impossible ()
