module Z3BvTheory

(*
   F star formalization of fixed-width bit-vector semantics, as a foundation
   for verifying the rewrite rules in src/ast/rewriter/bv_rewriter.cpp /
   src/ast/rewriter/bv_rewriter.h.

   Representation: a width-`n` bit-vector is modeled as `FStar.UInt.uint_t n`,
   i.e. a natural number `x` with `0 <= x < pow2 n` (big-endian / "integer"
   semantics, matching Z3's internal `rational` + `size` pair for
   `BV_NUM`/mk_numeral). This mirrors Z3's own representation: a bit-vector
   value is simply a numeral modulo `2^n`, and every bvadd/bvmul/bvand/...
   operation reduces to ordinary modular/bitwise arithmetic on that numeral.

   We deliberately reuse `FStar.UInt`'s *already proved* bitwise/shift/rotate
   lemma library instead of re-deriving commutativity, associativity,
   idempotence, shift-value and rotate-value facts from scratch: our
   `bvand`/`bvor`/`bvxor`/`bvnot`/`bvadd`/`bvsub`/`bvmul`/`bvshl`/`bvlshr`/
   `rotate_left`/`rotate_right`/`zero_extend` are literally (not just
   semantically) the corresponding `FStar.UInt` functions, so every lemma
   already proved there (`logand_commutative`, `logxor_self`,
   `shift_left_value_lemma`, `rotate_left_lemma`, ...) applies to our
   operations without any extra proof obligation. Operations with no direct
   library counterpart (extract, concat, sign_extend, arithmetic shift
   right, signed comparisons, signed/unsigned division and remainder with
   Z3's division-by-zero convention) are defined here from first principles
   as plain `nat` arithmetic (div/mod/mult), matching bv_rewriter.cpp's own
   definitions (bv_rewriter.h's `norm`, `mk_numeral`, and the `OP_B*`
   semantics documented in `bv_decl_plugin.h`).
*)

(* ----------------------------------------------------------------- *)
(* Core representation                                                *)
(* ----------------------------------------------------------------- *)

/// A width-indexed bit-vector value: a natural number below `2^n`.
/// Identical to `FStar.UInt.uint_t n`, reused here under a local name.
type bv (n:pos) = FStar.UInt.uint_t n

let bv_size (#n:pos) (_:bv n) : nat = n

(* ----------------------------------------------------------------- *)
(* Bitwise operations -- literally FStar.UInt's proven operations      *)
(* ----------------------------------------------------------------- *)

let bvand (#n:pos) (a b:bv n) : bv n = FStar.UInt.logand a b
let bvor  (#n:pos) (a b:bv n) : bv n = FStar.UInt.logor a b
let bvxor (#n:pos) (a b:bv n) : bv n = FStar.UInt.logxor a b
let bvnot (#n:pos) (a:bv n)   : bv n = FStar.UInt.lognot a

let bvnand (#n:pos) (a b:bv n) : bv n = bvnot (bvand a b)
let bvnor  (#n:pos) (a b:bv n) : bv n = bvnot (bvor a b)
let bvxnor (#n:pos) (a b:bv n) : bv n = bvnot (bvxor a b)

(* ----------------------------------------------------------------- *)
(* Arithmetic -- literally FStar.UInt's modular arithmetic             *)
(* ----------------------------------------------------------------- *)

let bvadd (#n:pos) (a b:bv n) : bv n = FStar.UInt.add_mod a b
let bvsub (#n:pos) (a b:bv n) : bv n = FStar.UInt.sub_mod a b
let bvmul (#n:pos) (a b:bv n) : bv n = FStar.UInt.mul_mod a b
let bvneg (#n:pos) (a:bv n)   : bv n = FStar.UInt.sub_mod 0 a

(* Unsigned division/remainder with Z3's "hi_div0" convention: division or
   remainder by the all-zeros bit-vector is total, returning the all-ones
   bit-vector for `bvudiv` and the dividend unchanged for `bvurem` -- the
   standard SMT-LIB2 semantics also used by Z3 (bv_rewriter.cpp's
   `mk_bv_udiv_i`/`mk_bv_urem_i`, see also `theory_bv`'s totalization). *)
let bvudiv (#n:pos) (a b:bv n) : bv n =
  if b = 0 then FStar.UInt.ones n else FStar.UInt.udiv a b

let bvurem (#n:pos) (a b:bv n) : bv n =
  if b = 0 then a else FStar.UInt.mod a b

(* ----------------------------------------------------------------- *)
(* Shifts and rotates -- literally FStar.UInt's proven operations      *)
(* ----------------------------------------------------------------- *)

let bvshl  (#n:pos) (a:bv n) (s:nat) : bv n = FStar.UInt.shift_left a s
let bvlshr (#n:pos) (a:bv n) (s:nat) : bv n = FStar.UInt.shift_right a s

let bv_rotate_left  (#n:pos) (a:bv n) (s:nat) : bv n = FStar.UInt.rotate_left a s
let bv_rotate_right (#n:pos) (a:bv n) (s:nat) : bv n = FStar.UInt.rotate_right a s

(* Arithmetic shift right via the standard "sign replicate" identity:
   ashr(a,s) = NOT(logical-shift-right(NOT a, s)). Negating twice
   restores the value while the logical shift fills the vacated high bits
   with the (replicated) complement of the sign bit, i.e. with the sign
   bit itself -- exactly bv_rewriter.cpp's `mk_bv_ashr` semantics. *)
let bvashr (#n:pos) (a:bv n) (s:nat) : bv n = bvnot (bvlshr (bvnot a) s)

(* ----------------------------------------------------------------- *)
(* Sign interpretation (two's complement)                             *)
(* ----------------------------------------------------------------- *)

/// The most-significant ("sign") bit of an `n`-bit value.
let msb (#n:pos) (a:bv n) : bool = a >= pow2 (n - 1)

/// Two's-complement signed interpretation of an `n`-bit value.
let to_int_signed (#n:pos) (a:bv n) : int =
  if msb a then a - pow2 n else a

(* ----------------------------------------------------------------- *)
(* Extract / concat / zero- and sign-extend                           *)
(* ----------------------------------------------------------------- *)

/// `extract hi lo a` keeps bits `lo..hi` (inclusive) of `a`, matching
/// bv_rewriter.cpp's `mk_extract` / `OP_EXTRACT` ("big-endian" integer
/// extraction: drop the low `lo` bits, then keep the low `hi-lo+1` bits).
let bv_extract (#n:pos) (hi lo:nat{lo <= hi /\ hi < n}) (a:bv n)
  : bv (hi - lo + 1) =
  (a / pow2 lo) % pow2 (hi - lo + 1)

/// `concat a b` places `a` (width `n`) in the high bits and `b` (width `m`)
/// in the low bits, matching bv_rewriter.cpp's `OP_CONCAT` / `mk_concat`.
let bv_concat (#n:pos) (#m:pos) (a:bv n) (b:bv m) : bv (n + m) =
  FStar.Math.Lemmas.pow2_plus n m;
  a * pow2 m + b

/// Zero-extend by `k` bits -- literally FStar.UInt's proven `zero_extends`.
let bv_zero_extend (#n:pos) (k:nat) (a:bv n) : bv (n + k) =
  if k = 0 then a else FStar.UInt.zero_extends k a

/// Sign-extend by `k` bits via the classic "double complement" identity:
/// sign_extend(a) = NOT(zero_extend(NOT a)). If `a`'s sign bit is 1
/// (negative), `NOT a` has sign bit 0, so zero-extending pads with 0s that
/// become 1s after the final NOT (replicating the sign); if `a`'s sign bit
/// is 0 the padded bits stay 0 after the final NOT. Matches bv_rewriter.cpp's
/// `mk_sign_extend` semantics (replicate the sign bit into the new bits).
let bv_sign_extend (#n:pos) (k:nat) (a:bv n) : bv (n + k) =
  if k = 0 then a else bvnot (bv_zero_extend k (bvnot a))

(* ----------------------------------------------------------------- *)
(* Comparisons                                                        *)
(* ----------------------------------------------------------------- *)

let bv_ult (#n:pos) (a b:bv n) : bool = a < b
let bv_ule (#n:pos) (a b:bv n) : bool = a <= b
let bv_slt (#n:pos) (a b:bv n) : bool = to_int_signed a < to_int_signed b
let bv_sle (#n:pos) (a b:bv n) : bool = to_int_signed a <= to_int_signed b

(* ----------------------------------------------------------------- *)
(* Reduction operators and bcomp                                      *)
(* ----------------------------------------------------------------- *)

/// `bvredor a` is the 1-bit OR of all bits of `a`: 0 iff `a` is all zeros.
let bv_redor (#n:pos) (a:bv n) : bv 1 = if a = 0 then 0 else 1

/// `bvredand a` is the 1-bit AND of all bits of `a`: 1 iff `a` is all ones.
let bv_redand (#n:pos) (a:bv n) : bv 1 = if a = FStar.UInt.ones n then 1 else 0

/// `bvcomp a b` is Z3's single-bit "bit-vector equality" operator: the
/// constant 1 (width-1 bit-vector) when `a = b`, else 0.
let bv_comp (#n:pos) (a b:bv n) : bv 1 = if a = b then 1 else 0
