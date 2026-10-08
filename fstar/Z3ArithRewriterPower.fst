module Z3ArithRewriterPower

(*
   Companion module to Z3ArithRewriter.fst: formalizes the exponent
   constant-folding and nested-power identities from mk_power_core in
   src/ast/rewriter/arith_rewriter.cpp. Split into its own file because
   combined verification together with the div/mod/abs lemmas is slow;
   each module verifies quickly on its own.
*)

open FStar.Real

let rec ipow (x:real) (n:nat) : real =
  if n = 0 then one else x *. ipow x (n - 1)

/// x^1 = x (mk_power_core's "y.is_one()" branch).
let power_one (x:real) : Lemma (ipow x 1 == x) = ()

/// x^0 = 1 for x <> 0 (mk_power_core's "y.is_zero()" branch; Z3 leaves
/// 0^0 unevaluated, matching the BR_FAILED case for x = y = 0).
let power_zero (x:real) : Lemma (requires x =!= zero) (ensures ipow x 0 == one) = ()

/// 0^y = 0 for y <> 0 (mk_power_core's "x.is_zero()" branch, y nonzero).
let power_zero_base (n:nat) : Lemma (requires n > 0) (ensures ipow zero n == zero) =
  let rec aux (k:nat) : Lemma (requires k > 0) (ensures ipow zero k == zero) =
    if k = 1 then () else aux (k - 1)
  in aux n

let rec power_add (x:real) (m n:nat) :
  Lemma (ensures ipow x m *. ipow x n == ipow x (m + n))
        (decreases m) =
  if m = 0 then ()
  else power_add x (m - 1) n

/// (x^y1)^y2 = x^(y1*y2) for positive integer exponents -- mk_power_core's
/// nested-power merge rule.
let rec power_merge (x:real) (y1 y2:nat) :
  Lemma (ensures ipow (ipow x y1) y2 == ipow x (y1 * y2))
        (decreases y2) =
  if y2 = 0 then ()
  else begin
    power_merge x y1 (y2 - 1);
    power_add x y1 (y1 * (y2 - 1));
    // ipow x y1 *. ipow x (y1*(y2-1)) == ipow x (y1 + y1*(y2-1));
    // distribute y1 * y2 = y1 * ((y2-1) + 1) = y1*(y2-1) + y1.
    FStar.Math.Lemmas.distributivity_add_right y1 (y2 - 1) 1
  end
