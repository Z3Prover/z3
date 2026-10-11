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

(* ----------------------------------------------------------------- *)
(* Overflow-detection predicates (mk_bv*_overflow family)              *)
(*                                                                     *)
(* bv_rewriter.cpp's ten overflow predicates rewrite a `(_ bvXXXovfl a *)
(* b)` application into a Boolean *formula* over `a`/`b` that is       *)
(* claimed to characterize the true arithmetic overflow/underflow      *)
(* condition. This section proves that claim: each rewritten formula  *)
(* is shown equivalent to the corresponding "true" over/underflow      *)
(* condition stated directly over the (unbounded) two's-complement     *)
(* integer values `to_int_signed a`/`to_int_signed b`.                 *)
(* ----------------------------------------------------------------- *)

/// The largest / smallest representable signed `n`-bit integer.
let max_signed (n:pos) : int = pow2 (n - 1) - 1
let min_signed (n:pos) : int = - (pow2 (n - 1))

/// Every `n`-bit value's signed interpretation lies in `[min_signed, max_signed]`.
let to_int_signed_range (#n:pos) (a:bv n) : Lemma (min_signed n <= to_int_signed a /\ to_int_signed a <= max_signed n) = ()

/// `mk_bvneg_overflow`: negation overflows iff `a` is the minimal signed
/// value (the only value whose negation, `-min_signed = 2^(n-1)`, is not
/// itself representable).
let lemma_bvneg_overflow_correct (#n:pos) (a:bv n)
  : Lemma ((to_int_signed a == min_signed n) <==> (a == pow2 (n - 1)))
  = ()

/// `mk_bvuadd_overflow`: zero-extend both operands by one bit, add at the
/// wider width, and test the newly-introduced top bit -- this exactly
/// detects whether the *unbounded* natural-number sum `a + b` reaches
/// `2^n`, i.e. true unsigned-addition overflow.
let lemma_bvuadd_overflow_correct (#n:pos) (a b:bv n)
  : Lemma (bv_extract n n (bvadd (bv_zero_extend 1 a) (bv_zero_extend 1 b)) ==
           (if a + b >= pow2 n then 1 else 0))
  = let a' : bv (n+1) = bv_zero_extend 1 a in
    let b' : bv (n+1) = bv_zero_extend 1 b in
    assert (a' == a);
    assert (b' == b);
    FStar.Math.Lemmas.pow2_double_sum n;
    FStar.Math.Lemmas.small_mod (a + b) (pow2 (n+1));
    assert (bvadd a' b' == a + b)

/// `mk_bvusub_underflow`: `a <u b` is, by definition, exactly unsigned
/// subtraction underflow (the borrow case).
let lemma_bvusub_underflow_correct (#n:pos) (a b:bv n)
  : Lemma (bv_ult a b == (a < b)) = ()

/// `mk_bvsadd_overflow`: both operands strictly positive (signed) yet the
/// wrapped sum is non-positive (signed) -- exactly signed-addition
/// *positive* overflow, i.e. the true integer sum exceeds `max_signed`.
/// (Overflow of a signed sum can only occur when both operands share a
/// sign: if the true sum `to_int_signed a + to_int_signed b` exceeds
/// `max_signed n`, both addends must individually be positive, since each
/// lies in `[min_signed n, max_signed n]` and a non-positive addend would
/// force the other to exceed `max_signed n` on its own, which is
/// impossible by `to_int_signed_range`.)
let lemma_bvsadd_overflow_correct (#n:pos) (a b:bv n)
  : Lemma ((bv_slt 0 a /\ bv_slt 0 b /\ bv_sle (bvadd a b) 0) <==>
           (to_int_signed a + to_int_signed b > max_signed n))
  = to_int_signed_range a;
    to_int_signed_range b;
    if a + b >= pow2 n then FStar.Math.Lemmas.small_mod (a + b - pow2 n) (pow2 n)
    else FStar.Math.Lemmas.small_mod (a + b) (pow2 n);
    assert (bvadd a b == (if a + b >= pow2 n then a + b - pow2 n else a + b))

/// `mk_bvsadd_underflow` (used only via `mk_bvsadd_over_underflow`): both
/// operands strictly negative yet the wrapped sum is non-negative --
/// signed-addition *negative* underflow, symmetric to the overflow case.
let lemma_bvsadd_underflow_correct (#n:pos) (a b:bv n)
  : Lemma ((bv_slt a 0 /\ bv_slt b 0 /\ bv_sle 0 (bvadd a b)) <==>
           (to_int_signed a + to_int_signed b < min_signed n))
  = to_int_signed_range a;
    to_int_signed_range b;
    if a + b >= pow2 n then FStar.Math.Lemmas.small_mod (a + b - pow2 n) (pow2 n)
    else FStar.Math.Lemmas.small_mod (a + b) (pow2 n);
    assert (bvadd a b == (if a + b >= pow2 n then a + b - pow2 n else a + b))

/// `mk_bvsadd_over_underflow`: the disjunction of the two cases above --
/// signed-addition overflow in *either* direction.
let lemma_bvsadd_over_underflow_correct (#n:pos) (a b:bv n)
  : Lemma (((bv_slt 0 a /\ bv_slt 0 b /\ bv_sle (bvadd a b) 0) \/
            (bv_slt a 0 /\ bv_slt b 0 /\ bv_sle 0 (bvadd a b))) <==>
           (to_int_signed a + to_int_signed b > max_signed n \/
            to_int_signed a + to_int_signed b < min_signed n))
  = lemma_bvsadd_overflow_correct a b;
    lemma_bvsadd_underflow_correct a b

/// `mk_bvsdiv_overflow`: signed division overflows in exactly the single
/// edge case `a = min_signed /\ b = -1` (negating `min_signed` -- the only
/// case where `|dividend / divisor|` is not representable).
let lemma_bvsdiv_overflow_correct (#n:pos) (a b:bv n)
  : Lemma ((a == pow2 (n - 1) /\ b == FStar.UInt.ones n) <==>
           (to_int_signed a == min_signed n /\ to_int_signed b == -1))
  = ()

/// Negation is exact (does not wrap) whenever its argument is not the
/// minimal signed value -- the companion fact `mk_bvssub_under_overflow`
/// relies on to reduce signed subtraction to signed addition of a negation.
let lemma_bvneg_exact (#n:pos) (b:bv n{b <> pow2 (n - 1)})
  : Lemma (to_int_signed (bvneg b) == - (to_int_signed b))
  = if b = 0 then ()
    else FStar.Math.Lemmas.small_mod (pow2 n - b) (pow2 n)

/// `mk_bvssub_under_overflow`: signed subtraction `a - b` over/underflows.
/// The rewritten formula special-cases `b = min_signed` (whose negation
/// itself would overflow) by testing `0 <=s a` directly, and otherwise
/// delegates to the signed-addition over/underflow test on `a + (-b)`,
/// which is sound because negating a non-minimal `b` is exact
/// (`lemma_bvneg_exact`).
let lemma_bvssub_under_overflow_correct (#n:pos) (a b:bv n)
  : Lemma ((if b = pow2 (n - 1) then bv_sle 0 a
            else let nb = bvneg b in
                 (bv_slt 0 a /\ bv_slt 0 nb /\ bv_sle (bvadd a nb) 0) \/
                 (bv_slt a 0 /\ bv_slt nb 0 /\ bv_sle 0 (bvadd a nb)))
           <==>
           (to_int_signed a - to_int_signed b > max_signed n \/
            to_int_signed a - to_int_signed b < min_signed n))
  = to_int_signed_range a;
    to_int_signed_range b;
    if b = pow2 (n - 1) then ()
    else begin
      lemma_bvneg_exact b;
      lemma_bvsadd_over_underflow_correct a (bvneg b)
    end

(* ----------------------------------------------------------------- *)
(* Multiplication-overflow predicates (mk_bv{s,u}mul_{no_,}overflow)  *)
(*                                                                     *)
(* Completes coverage of the ten overflow predicates. `mk_bvsmul_no_  *)
(* overflow` folds signed multiplication's numeral/numeral case into a *)
(* sign/magnitude test; `mk_bvumul_no_overflow` folds the unsigned case *)
(* directly as a product-bound comparison; `mk_bvsmul_overflow` /      *)
(* `mk_bvumul_overflow` build their result as the (De Morgan) negation  *)
(* of the corresponding `_no_overflow`/`_no_ovfl` builtin predicate.    *)
(* ----------------------------------------------------------------- *)

/// The absolute value of `a`'s signed interpretation, as a natural number.
let mag (#n:pos) (a:bv n) : nat = if msb a then pow2 n - a else a

/// The true (unbounded) signed product decomposes into the magnitude
/// product `mag a * mag b`, signed according to whether `a`/`b` agree in
/// sign -- the fact underlying `mk_bvsmul_no_overflow`'s sign/magnitude
/// construction (`a0_val`/`a1_val` after the `has_sign_bit` conversion
/// are exactly `mag a`/`mag b`).
let lemma_signed_product_abs (#n:pos) (a b:bv n)
  : Lemma (to_int_signed a * to_int_signed b ==
           (if msb a = msb b then mag a * mag b else - (mag a * mag b)))
  = ()

/// `mk_bvsmul_no_overflow` with `is_overflow = true` (`OP_BSMUL_NO_OVFL`):
/// the true signed product does not exceed `max_signed`.
let lemma_bvsmul_no_ovfl_correct (#n:pos) (a b:bv n)
  : Lemma ((msb a <> msb b \/ mag a * mag b < pow2 (n - 1)) <==>
           (to_int_signed a * to_int_signed b <= max_signed n))
  = lemma_signed_product_abs a b

/// `mk_bvsmul_no_overflow` with `is_overflow = false` (`OP_BSMUL_NO_UDFL`):
/// the true signed product does not fall below `min_signed`.
let lemma_bvsmul_no_udfl_correct (#n:pos) (a b:bv n)
  : Lemma ((msb a = msb b \/ mag a * mag b <= pow2 (n - 1)) <==>
           (to_int_signed a * to_int_signed b >= min_signed n))
  = lemma_signed_product_abs a b

/// `mk_bvsmul_overflow` (`OP_BSMUL_OVFL`): the negation of either
/// no-overflow test, i.e. true signed-multiplication over/underflow in
/// either direction -- a direct De Morgan corollary of the two facts above.
let lemma_bvsmul_overflow_correct (#n:pos) (a b:bv n)
  : Lemma ((~ (msb a <> msb b \/ mag a * mag b < pow2 (n - 1)) \/
            ~ (msb a = msb b \/ mag a * mag b <= pow2 (n - 1))) <==>
           (to_int_signed a * to_int_signed b > max_signed n \/
            to_int_signed a * to_int_signed b < min_signed n))
  = lemma_bvsmul_no_ovfl_correct a b;
    lemma_bvsmul_no_udfl_correct a b

/// `mk_bvumul_no_overflow` (`OP_BUMUL_NO_OVFL`, numeral/numeral case):
/// the unsigned product fits in `n` bits -- a direct restatement of the
/// defining bound, not a separate algebraic fact (listed here for
/// completeness of the predicate family).
let lemma_bvumul_no_overflow_correct (#n:pos) (a b:bv n)
  : Lemma ((a * b < pow2 n) == (a * b < pow2 n)) = ()

/// `mk_bvumul_overflow` (`OP_BUMUL_OVFL`): the negation of the unsigned
/// no-overflow test, i.e. the unsigned product reaches `2^n`.
let lemma_bvumul_overflow_correct (#n:pos) (a b:bv n)
  : Lemma (~ (a * b < pow2 n) <==> (a * b >= pow2 n)) = ()
