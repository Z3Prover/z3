module AuditLshrSelf
module U = FStar.UInt

let rec lemma_nat_lt_pow2 (n:nat) : Lemma (n < pow2 n) (decreases n) =
  match n with
  | 0 -> ()
  | _ ->
    lemma_nat_lt_pow2 (n - 1);
    FStar.Math.Lemmas.pow2_plus 1 (n - 1)

(* O1: a >> a = 0 for every in-range operand, any width (incl. a >= width) *)
let lemma_lshr_self (#width:pos) (a:U.uint_t width) : Lemma (U.shift_right a a == 0) =
  lemma_nat_lt_pow2 a;
  U.shift_right_value_lemma a a;
  FStar.Math.Lemmas.small_division_lemma_1 a (pow2 a)

(* O2: concrete witnesses at 8 and 65 bits, incl. a >= width *)
let w8 : U.uint_t 8 = 200
let _ = assert (U.shift_right w8 w8 == 0) by (FStar.Tactics.V2.norm [delta; zeta; iota; primops])
let lemma_8 (a:U.uint_t 8) : Lemma (U.shift_right a a == 0) = lemma_lshr_self #8 a
let lemma_65 (a:U.uint_t 65) : Lemma (U.shift_right a a == 0) = lemma_lshr_self #65 a

(* O3: the analogous bvshl rewrite is invalid: a=1,width 8: 1<<1 = 2 <> 0 *)
let shl_witness () : Lemma (U.shift_left #8 1 1 == 2 /\ U.shift_left #8 1 1 <> 0) =
  assert_norm (U.shift_left #8 1 1 == 2)
