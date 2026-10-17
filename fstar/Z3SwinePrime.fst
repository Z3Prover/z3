module Z3SwinePrime

(* Uses the checked library's ordinary divisibility-based definition of
   primality and Euclid's theorem, not a zero-divisor-free axiom.
   Checked by the parent WSL F* session; see ZWINE_NFV_REPORT.md. *)
module P = Z3SwinePower
module R = Z3SwineRefinements
module E = FStar.Math.Euclid

#set-options "--fuel 2 --ifuel 0 --z3rlimit 10"

let rec prime_power (p:int{E.is_prime p}) (x:int) (n:nat)
  : Lemma
      (ensures (P.power x n % p == 0) <==> (x % p == 0 /\ n > 0))
      (decreases n) =
  if n = 0 then begin
    P.power_zero x;
    if 1 % p == 0 then begin
      E.mod_divides 1 p;
      E.divides_1 p
    end
  end
  else begin
    prime_power p x (n-1);
    P.power_succ x (n-1);
    let previous = P.power x (n-1) in
    assert (P.power x n == x*previous);
    if P.power x n % p == 0 then
      E.euclid_prime p x previous;
    if x % p == 0 then begin
      E.mod_divides x p;
      E.divides_mult_right previous x p;
      E.divides_mod (previous*x) p;
      assert (previous*x == P.power x n)
    end
  end

(* Literal-for-literal biconditional emitted by arith_swine::prime,
   for arbitrary SIGNED bases/exponents and every actual prime numeral.
   Primality of C++'s selected numeral remains a separate source-mapped
   witness-selection invariant, not a theorem about the C++ loop. *)
let prime_clause_sound (p:int{E.is_prime p}) (x y:int)
  : Lemma (R.prime_clause x y p) =
  prime_power p x (P.magnitude y);
  assert (P.magnitude y > 0 <==> y <> 0)
