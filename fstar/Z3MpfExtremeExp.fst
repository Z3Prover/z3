(*
   Z3MpfExtremeExp.fst

   Targeted audit of `mpf_manager::set`'s exponent-range handling
   (src/util/mpf.cpp, ~line 266-294), motivated by open PR #11160
   ("Fix floating-point rounding for extreme integer exponents").

   `mpf_manager::set(o, ebits, sbits, rm, exponent, significand)`
   builds the correctly-rounded `ebits`/`sbits`-format float for an
   exact rational `significand * 2^exponent`, where `exponent` is an
   arbitrary-precision integer (`mpz`, i.e. *unbounded* in principle --
   e.g. it may arise from a 64-bit or larger bit-vector exponent field
   in `fpa2bv_converter.cpp`'s `to_fp` encodings). Two independent bugs
   in how this arbitrary-precision `exponent` was funneled through
   machine-word-sized (`int64`) arithmetic are fixed by PR #11160:

   Bug A (overflow check, mpf.cpp ~line 269, before the fix):

       if (m_mpz_manager.is_int64(exp) && m_mpz_manager.get_int64(exp) > mk_max_exp(ebits))
           { mk_round_inf(rm, o); return; }

   `is_int64(exp)` is false whenever `|exp|` exceeds the `int64` range.
   For such an `exp` -- which, being *larger in magnitude* than
   `int64`, is certainly also larger than the tiny `mk_max_exp(ebits)`
   bound (e.g. 1023 for binary64) whenever it is positive -- the
   condition as a whole is simply `false`, so the overflow-to-infinity
   short-circuit is skipped entirely, and execution falls through to
   code that (bug B below) assumed `exp` fits in a representable
   range. The fix replaces the `int64`-gated comparison with a direct
   arbitrary-precision comparison against an `mpz`-valued bound,
   independent of `is_int64`.

   Bug B (underflow path, mpf.cpp ~line 288, before the fix):

       if (m_mpz_manager.is_small(exp)) { o.exponent = get_int64(exp); round(rm, o); }
       else mk_inf(ebits, sbits, o.sign, o);

   By this point `exp <= mk_max_exp(ebits)` is known (bug A's check,
   now assumed fixed, already excluded overflow), so the only reason
   `exp` could fail `is_small` here is that it is *very negative*
   (a deep-underflow exponent, again arising from a wide bit-vector
   exponent field). The `else` branch unconditionally calls `mk_inf`
   -- i.e. it reports **infinity** for a deep *underflow*, the exact
   opposite of the correct answer (which should be zero, or the
   smallest subnormal when the rounding mode is directed away from
   zero). The fix recognizes that `round()`'s internal right-shift
   distance (`sigma`, mpf.cpp ~line 1994-2008) is itself *capped* at
   `-(sbits+2)` -- i.e. `round()` already treats every sufficiently
   negative raw exponent identically -- and so it is sound to clamp
   any `exp` below a safe floor `min_exp = mk_min_exp(ebits) - sbits - 4`
   to that floor (a value that always fits in `int64`) before calling
   `round()` uniformly, rather than special-casing "not small" as
   infinity.

   This file formalizes both bugs/fixes at the level of idealized
   (unbounded, F* `int`-valued) exponents, cross-checked directly
   against the cited `round()` code (the `sigma`-capping computation
   is reproduced in full, not treated as an opaque black box, since it
   is exactly the fact the fix's soundness hinges on; the surrounding
   significand rounding arithmetic itself remains out of scope, as in
   Z3MpfTheory.fst/MPF_REPORT.md's scope decision).
*)
module Z3MpfExtremeExp

(* ----------------------------------------------------------------- *)
(* Bug A: the overflow check.                                         *)
(*                                                                      *)
(* `is_int64_repr` abstracts `mpz_manager::is_int64`: true iff the      *)
(* (unbounded) value fits the concrete int64 range. We use the actual   *)
(* int64 bounds so the "overflow is invisible to the old check"        *)
(* witness below is a literal, not merely a schematic, counterexample.  *)
(* ----------------------------------------------------------------- *)
let int64_min : int = -9223372036854775808
let int64_max : int = 9223372036854775807

let is_int64_repr (e:int) : bool = int64_min <= e && e <= int64_max

(* old check: only fires when exp is both int64-representable AND
   exceeds max_exp. *)
let old_overflow (max_exp:int) (e:int) : bool =
  is_int64_repr e && e > max_exp

(* new check (the fix): a direct, unrestricted comparison. *)
let new_overflow (max_exp:int) (e:int) : bool =
  e > max_exp

(* Theorem A1 (the fix is a generalization): every exponent flagged as
   overflowing by the old check is also flagged by the new one -- the
   fix never *loses* a previously-correct overflow detection. *)
let lemma_new_overflow_generalizes (max_exp e:int)
  : Lemma (requires old_overflow max_exp e)
          (ensures new_overflow max_exp e)
  = ()

(* Theorem A2 (the bug, precisely located): there exist genuinely
   overflowing exponents (e > max_exp, in fact arbitrarily large ones)
   that the old check fails to catch, because they exceed the int64
   range. Witness: e = 2^64 (one of PR #11160's literal regression-test
   exponent strings, "18446744073709551616"), with any realistic
   `max_exp` (e.g. 1023, binary64's). The new check correctly flags it. *)
let lemma_old_overflow_misses_huge_exponent ()
  : Lemma (let max_exp = 1023 in
           let e = 18446744073709551616 in  (* 2^64 *)
           e > max_exp /\
           ~(old_overflow max_exp e) /\
           new_overflow max_exp e)
  = ()

(* Same witness, the PR's other literal boundary case just above
   int64_max: e = 2^63 = int64_max + 1 ("9223372036854775808"). *)
let lemma_old_overflow_misses_int64_max_plus_one ()
  : Lemma (let max_exp = 1023 in
           let e = 9223372036854775808 in  (* 2^63 *)
           e > max_exp /\
           ~(old_overflow max_exp e) /\
           new_overflow max_exp e)
  = ()

(* ----------------------------------------------------------------- *)
(* Bug B: the underflow path, modeled via `round()`'s own, *exact*      *)
(* shift-distance computation (mpf.cpp 1985-2008), not a black box.    *)
(*                                                                      *)
(* Restricting to the "denormal/TINY" branch relevant here (beta <     *)
(* e_min, which always holds once the raw exponent is sufficiently     *)
(* negative, since beta == exponent - lz + 1 for an `lz` bounded        *)
(* independent of `exponent`): `sigma = exponent - e_min`, then capped   *)
(* below at `sigma_cap = -(sbits+2)`.                                   *)
(* ----------------------------------------------------------------- *)
let sigma_cap (sbits:int) : int = -(sbits + 2)

let capped_sigma (e_min sbits exponent:int) : int =
  let sigma = exponent - e_min in
  if sigma < sigma_cap sbits then sigma_cap sbits else sigma

(* Theorem B1 (the saturation fact the fix relies on): once `exponent`
   is at or below the fix's chosen floor `min_exp = e_min - sbits - 4`,
   `capped_sigma` has *already saturated* -- it equals `sigma_cap`,
   independent of exactly how far below the floor `exponent` is. *)
let lemma_sigma_saturates (e_min sbits exponent:int)
  : Lemma (requires exponent <= e_min - sbits - 4)
          (ensures capped_sigma e_min sbits exponent == sigma_cap sbits)
  = ()

(* Theorem B2 (soundness of clamping): consequently, for *any* two
   exponents both at or below the floor, `capped_sigma` -- and hence,
   since `round()`'s entire subsequent computation (right-shift amount,
   sticky bit, final stored exponent `e_min`) is a function of
   `capped_sigma` alone in this branch -- the two calls to `round()`
   are computing on identical inputs and so produce identical results.
   In particular, clamping any such `exponent` up to the floor itself
   (as the fix does, `o.exponent = exp < exp_bound ? min_exp : ...`)
   changes nothing observable. *)
let lemma_clamp_is_transparent (e_min sbits min_exp exponent:int)
  : Lemma (requires min_exp == e_min - sbits - 4 /\
                    exponent <= min_exp)
          (ensures capped_sigma e_min sbits exponent == capped_sigma e_min sbits min_exp)
  =
  lemma_sigma_saturates e_min sbits exponent;
  lemma_sigma_saturates e_min sbits min_exp

(* Theorem B3 (the bug, precisely located): the old code's `else`
   branch reports infinity for *every* non-"small" exponent, including
   deep-underflow ones that are nowhere near overflowing -- e.g.
   `exponent = -(2^64)`, with `e_min = -1022` (binary64), `sbits = 53`:
   this is far below the floor (so by B1/B2 it should round to zero or
   the smallest subnormal, matching `mk_min_exp(ebits) - sbits - 4`'s
   derivation), yet the old code's `mk_inf` fallback would report
   infinity -- the opposite of underflow-to-zero. We witness this as:
   the exponent is (a) at/below the saturation floor (so its true
   rounded result only depends on `sigma_cap`, a *finite*, small
   negative shift -- not infinity), while (b) "not small" in the old
   code's sense is exactly the condition (`is_int64_repr` failing for
   magnitudes beyond int64) that PR #11160's own test exponent
   "-18446744073709551616" exercises. *)
let lemma_deep_underflow_is_not_overflow ()
  : Lemma (let e_min = -1022 in let sbits = 53 in
           let exponent = -18446744073709551616 in  (* -(2^64) *)
           exponent <= e_min - sbits - 4 /\
           ~(is_int64_repr exponent) /\
           capped_sigma e_min sbits exponent == sigma_cap sbits)
  = ()
