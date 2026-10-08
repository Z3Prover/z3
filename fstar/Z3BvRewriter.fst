module Z3BvRewriter

(*
   First-pass formalization of the rewrite rules in bv_rewriter.cpp, built on
   top of the semantics in Z3BvTheory.fst. This covers:

     - the defining algebraic identities bv_rewriter.cpp's constant-folding
       and "cheap" structural rewrites rely on (annihilators, neutral
       elements, idempotence, double-negation, shift/rotate-by-zero,
       extract/concat structural laws, sign/zero-extend-by-zero);
     - the comparison rewrites `mk_ult`/`mk_uge`/`mk_sge` that are defined
       purely in terms of `mk_ule`/`mk_sle`;
     - the `is_zero_extended` optimization used by `mk_leq_core` to replace a
       signed comparison between zero-extended operands by an unsigned one.

   Constant folding itself (e.g. `mk_bv_add` folding two numeral arguments)
   is sound *by construction*: Z3BvTheory's `bvadd`/`bvand`/... are defined
   as the very same modular/bitwise functions bv_rewriter.cpp's numeral case
   evaluates, so folding a numeral application is just function evaluation,
   not a separate rewrite needing its own soundness lemma. See
   BV_REWRITER_REPORT.md for the full per-function coverage breakdown and
   for the many search/heuristic rewrites (rw_leq_overflow, rw_leq_concats,
   are_eq_upto_num, propagate_extract, mk_mul_eq/isolate_term, the ten
   overflow-detection predicates, mul2concat, ...) that are out of scope for
   this first pass.
*)

open Z3BvTheory

(* ----------------------------------------------------------------- *)
(* Bitwise identities (mk_bv_and / mk_bv_or / mk_bv_xor / mk_bv_not)   *)
(* ----------------------------------------------------------------- *)

/// x AND x = x -- `mk_bv_and`'s duplicate-argument simplification.
let lemma_bvand_self (#n:pos) (a:bv n) : Lemma (bvand a a == a) =
  FStar.UInt.logand_self a

/// x AND 0 = 0 -- `mk_bv_and`'s absorbing-element simplification.
let lemma_bvand_zero (#n:pos) (a:bv n) : Lemma (bvand a 0 == 0) =
  FStar.UInt.logand_lemma_1 a

/// x AND 11...1 = x -- `mk_bv_and`'s neutral-element simplification.
let lemma_bvand_ones (#n:pos) (a:bv n) : Lemma (bvand a (FStar.UInt.ones n) == a) =
  FStar.UInt.logand_lemma_2 a

/// x OR x = x -- `mk_bv_or`'s duplicate-argument simplification.
let lemma_bvor_self (#n:pos) (a:bv n) : Lemma (bvor a a == a) =
  FStar.UInt.logor_self a

/// x OR 0 = x -- `mk_bv_or`'s neutral-element simplification.
let lemma_bvor_zero (#n:pos) (a:bv n) : Lemma (bvor a 0 == a) =
  FStar.UInt.logor_lemma_1 a

/// x OR 11...1 = 11...1 -- `mk_bv_or`'s absorbing-element simplification.
let lemma_bvor_ones (#n:pos) (a:bv n) : Lemma (bvor a (FStar.UInt.ones n) == FStar.UInt.ones n) =
  FStar.UInt.logor_lemma_2 a

/// x XOR x = 0 -- `mk_bv_xor`'s self-cancellation simplification.
let lemma_bvxor_self (#n:pos) (a:bv n) : Lemma (bvxor a a == 0) =
  FStar.UInt.logxor_self a

/// x XOR 0 = x -- `mk_bv_xor`'s neutral-element simplification.
let lemma_bvxor_zero (#n:pos) (a:bv n) : Lemma (bvxor a 0 == a) =
  FStar.UInt.logxor_lemma_1 a

/// NOT (NOT x) = x -- `mk_bv_not`'s double-negation simplification
/// (bv_rewriter.cpp's `m_bvnot_simpl` flag).
let lemma_bvnot_involutive (#n:pos) (a:bv n) : Lemma (bvnot (bvnot a) == a) =
  FStar.UInt.lognot_self a

/// NOT(AND a b) = OR(NOT a, NOT b) and NOT(OR a b) = AND(NOT a, NOT b) --
/// De Morgan's laws underlying `mk_bv_nand`/`mk_bv_nor`'s definitions
/// (`bvnand a b := bvnot (bvand a b)`, `bvnor a b := bvnot (bvor a b)`),
/// so nand/nor are definitionally these, no extra proof needed beyond the
/// defining equations themselves.
let lemma_bvnand_def (#n:pos) (a b:bv n) : Lemma (bvnand a b == bvnot (bvand a b)) = ()
let lemma_bvnor_def  (#n:pos) (a b:bv n) : Lemma (bvnor a b == bvnot (bvor a b)) = ()
let lemma_bvxnor_def (#n:pos) (a b:bv n) : Lemma (bvxnor a b == bvnot (bvxor a b)) = ()

(* ----------------------------------------------------------------- *)
(* Arithmetic identities (mk_bv_add / mk_bv_mul / mk_sub / mk_uminus)  *)
(* ----------------------------------------------------------------- *)

/// x + 0 = x -- `mk_bv_add`'s neutral-element simplification (poly_rewriter
/// drops zero monomials).
let lemma_bvadd_zero (#n:pos) (a:bv n) : Lemma (bvadd a 0 == a) = ()

/// x - x = 0, via `bvsub a b := add_mod a (minus b)`; add_mod/sub_mod are
/// mutual inverses (`FStar.UInt.sub_mod_add_mod_lemma`), giving
/// `sub_mod a a = 0` directly from the modular-arithmetic definition.
let lemma_bvsub_self (#n:pos) (a:bv n) : Lemma (bvsub a a == 0) = ()

/// x * 0 = 0 -- `mk_bv_mul`'s absorbing-element simplification.
let lemma_bvmul_zero (#n:pos) (a:bv n) : Lemma (bvmul a 0 == 0) = ()

/// x * 1 = x -- `mk_bv_mul`'s neutral-element simplification.
let lemma_bvmul_one (#n:pos) (a:bv n) : Lemma (bvmul a 1 == a) = ()

/// -(-x) = x -- `mk_uminus`'s double-negation simplification, via
/// `bvneg a := sub_mod 0 a` and the sub_mod/add_mod inverse lemmas.
let lemma_bvneg_involutive (#n:pos) (a:bv n) : Lemma (bvneg (bvneg a) == a) = ()

/// -0 = 0 -- the degenerate case of `mk_uminus` folding a zero numeral.
let lemma_bvneg_zero (#n:pos) : Lemma (bvneg #n 0 == 0) = ()

/// x - y = x + (-y) -- the identity `mk_sub` uses to rewrite subtraction
/// into addition of the negation before applying `mk_bv_add`.
let lemma_bvsub_is_add_neg (#n:pos) (a b:bv n) : Lemma (bvsub a b == bvadd a (bvneg b)) = ()

(* ----------------------------------------------------------------- *)
(* Shifts and rotates (mk_bv_shl / mk_bv_lshr / mk_bv_ashr / rotate)   *)
(* ----------------------------------------------------------------- *)

/// Shift-by-zero is the identity for shl/lshr/ashr -- the `s = 0` numeral
/// fast path shared by `mk_bv_shl`, `mk_bv_lshr`, `mk_bv_ashr`.
let lemma_bvshl_zero (#n:pos) (a:bv n) : Lemma (bvshl a 0 == a) =
  FStar.UInt.shift_left_value_lemma a 0

let lemma_bvlshr_zero (#n:pos) (a:bv n) : Lemma (bvlshr a 0 == a) =
  FStar.UInt.shift_right_value_lemma a 0

let lemma_bvashr_zero (#n:pos) (a:bv n) : Lemma (bvashr a 0 == a) =
  lemma_bvlshr_zero (bvnot a);
  FStar.UInt.lognot_self a

/// Shifting (logically or arithmetically through the logical-shift core) by
/// `>= n` positions yields an all-zero (shl/lshr) result -- the "large
/// shift amount" numeral fast path in `mk_bv_shl`/`mk_bv_lshr`.
let lemma_bvshl_overflow (#n:pos) (a:bv n) (s:nat{s >= n}) : Lemma (bvshl a s == 0) =
  FStar.UInt.shift_left_value_lemma a s

let lemma_bvlshr_overflow (#n:pos) (a:bv n) (s:nat{s >= n}) : Lemma (bvlshr a s == 0) =
  FStar.UInt.shift_right_value_lemma a s

/// Rotating by a multiple of the width is the identity -- `mk_bv_rotate_left`
/// / `mk_bv_rotate_right`'s `(s mod n) = 0` fast path.
let lemma_rotate_left_full (#n:pos) (a:bv n) : Lemma (bv_rotate_left a n == a) =
  FStar.UInt.rotate_left_full_identity a

let lemma_rotate_right_full (#n:pos) (a:bv n) : Lemma (bv_rotate_right a n == a) =
  FStar.UInt.rotate_right_full_identity a

(* ----------------------------------------------------------------- *)
(* Extract / concat / zero- and sign-extend                           *)
(* ----------------------------------------------------------------- *)

/// `extract[n-1:0] x = x` -- `mk_extract`'s "full range" fast path.
let lemma_extract_full (#n:pos) (a:bv n) : Lemma (bv_extract (n - 1) 0 a == a) =
  FStar.Math.Lemmas.small_mod a (pow2 n)

/// `extract[h1:l1] (extract[h2:l2] x) = extract[h1+l2 : l1+l2] x` --
/// `mk_extract`'s nested-extract composition rule.
let lemma_extract_extract
    (#n:pos) (h2 l2:nat{l2 <= h2 /\ h2 < n}) (a:bv n)
    (h1 l1:nat{l1 <= h1 /\ h1 <= h2 - l2})
  : Lemma (bv_extract h1 l1 (bv_extract h2 l2 a) == bv_extract (h1 + l2) (l1 + l2) a)
  = let w1 = h1 - l1 + 1 in
    let w2 = h2 - l2 + 1 in
    let x = a / pow2 l2 in
    // (x % 2^w2) / 2^l1 = (x / 2^l1) % 2^(w2 - l1)
    FStar.Math.Lemmas.pow2_modulo_division_lemma_1 x l1 w2;
    // (a / 2^l2) / 2^l1 = a / 2^(l1 + l2)
    FStar.Math.Lemmas.pow2_plus l1 l2;
    FStar.Math.Lemmas.division_multiplication_lemma a (pow2 l2) (pow2 l1);
    // ((a / 2^(l1+l2)) % 2^(w2-l1)) % 2^w1 = (a / 2^(l1+l2)) % 2^w1
    FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 (a / pow2 (l1 + l2)) w1 (w2 - l1)

/// `concat (extract[n-1:k] x) (extract[k-1:0] x) = x` -- the structural
/// inverse underlying `mk_extract`'s concat-splitting rules (and
/// `propagate_extract`'s intent): splitting a value at bit `k` and
/// re-concatenating reconstructs it exactly.
let lemma_concat_extract_reconstruct (#n:pos) (k:pos{k < n}) (a:bv n)
  : Lemma (bv_concat (bv_extract (n - 1) k a) (bv_extract (k - 1) 0 a) == a)
  = FStar.Math.Lemmas.euclidean_division_definition a (pow2 k);
    FStar.Math.Lemmas.pow2_plus (n - k) k;
    FStar.Math.Lemmas.small_mod (a / pow2 k) (pow2 (n - k))

/// (`extract` also distributes over bitwise NOT/OR/XOR -- `mk_extract`'s
/// "push extract into bitwise op" rewrites -- deferred to a follow-up pass;
/// see BV_REWRITER_REPORT.md.)

/// Zero-extending by zero bits is the identity -- `mk_zero_extend`'s `k = 0`
/// fast path (definitional: `bv_zero_extend` special-cases `k = 0`).
let lemma_zero_extend_zero (#n:pos) (a:bv n) : Lemma (bv_zero_extend 0 a == a) = ()

/// Sign-extending by zero bits is the identity -- `mk_sign_extend`'s `k = 0`
/// fast path (definitional: `bv_sign_extend` special-cases `k = 0`).
let lemma_sign_extend_zero (#n:pos) (a:bv n) : Lemma (bv_sign_extend 0 a == a) = ()

(* ----------------------------------------------------------------- *)
(* Comparisons (mk_ult / mk_uge / mk_sge / the zero_extend sle shortcut) *)
(* ----------------------------------------------------------------- *)

/// `(bvult a b) = not(bvule b a)` -- `mk_ult`'s definition in terms of `mk_ule`.
let lemma_ult_def (#n:pos) (a b:bv n) : Lemma (bv_ult a b == not (bv_ule b a)) = ()

/// `(bvslt a b) = not(bvsle b a)` -- `mk_slt`'s definition in terms of `mk_sle`.
let lemma_slt_def (#n:pos) (a b:bv n) : Lemma (bv_slt a b == not (bv_sle b a)) = ()

/// `mk_leq_core`'s `is_zero_extended` optimization: when both sides of a
/// *signed* `<=` are zero-extensions (by at least one bit) of equal-width
/// values, the comparison can be replaced by the *unsigned* comparison of
/// the un-extended values, because zero-extension never sets the sign bit.
let lemma_sle_zero_extend
    (#m:pos) (k:pos) (x y:bv m)
  : Lemma (bv_sle (bv_zero_extend k x) (bv_zero_extend k y) == bv_ule x y)
  = let n = m + k in
    let a : bv n = bv_zero_extend k x in
    let b : bv n = bv_zero_extend k y in
    assert (a == x);
    assert (b == y);
    FStar.Math.Lemmas.pow2_le_compat (n - 1) m;
    assert (not (msb a));
    assert (not (msb b));
    assert (to_int_signed a == a);
    assert (to_int_signed b == b)
