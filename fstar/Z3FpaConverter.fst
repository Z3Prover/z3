(*
   Z3FpaConverter.fst

   A self-contained axiomatization, in F*, of the *bit-pattern level*
   classification logic of src/ast/fpa/fpa2bv_converter.cpp, together
   with a proof of the (non-obvious) bias/unbias round-trip identity
   used by that converter's exponent (de)normalization.

   Scope decision (mirrors Z3FpaTheory.fst / fpa_rewriter.cpp): the
   converter's floating-point *arithmetic* (mk_add/mk_mul/mk_div/
   mk_sqrt/mk_fma/mk_round_to_integral, the `unpack`/`round` pipeline)
   is a genuine bit-precise rounding circuit, analogous in complexity
   to the regex/automata machinery excluded from the seq audit, and is
   explicitly *not* modeled here. What *is* modeled, exactly and
   completely, are:
     (1) the classification predicates mk_is_nan/is_inf/is_pinf/
         is_ninf/is_pos/is_neg/is_zero/is_nzero/is_pzero/is_denormal/
         is_normal (fpa2bv_converter.cpp 3760-3875), which operate
         purely combinatorially on the (sign, exponent, significand)
         bit-pattern triple -- no rounding involved; and
     (2) the mk_bias / mk_unbias round-trip (fpa2bv_converter.cpp
         3952-3975), a self-contained modular-arithmetic bit trick.

   `mk_leading_zeros` (a recursive divide-and-conquer bit-counting
   circuit, fpa2bv_converter.cpp 3913-3951) is judged out of scope for
   the same reason as `mk_leading_zeros`'s seq-audit analogue (regex
   derivatives): it is a nontrivial recursive algorithm whose
   correctness is best established by a dedicated, separate effort,
   not as a byproduct of this rewrite-rule audit.
*)
module Z3FpaConverter

(* ----------------------------------------------------------------- *)
(* A self-contained power-of-two function (consistent with the         *)
(* seq-theory style of not depending on FStar.Math.Lemmas for its      *)
(* *definitions*; we do use a couple of its lemmas below for the        *)
(* bias/unbias proof, which is standard modular-arithmetic reasoning,   *)
(* not a structural-induction technique we want to keep self-contained).*)
(* ----------------------------------------------------------------- *)

let rec pow2 (n:nat) : pos =
  if n = 0 then 1 else 2 * pow2 (n - 1)

let rec lemma_pow2_pos (n:nat)
  : Lemma (pow2 n > 0)
  = if n = 0 then () else lemma_pow2_pos (n - 1)

(* ----------------------------------------------------------------- *)
(* Bit patterns (fpa2bv_converter.cpp's `split_fp` triple: sign bit,    *)
(* exponent field, significand field).                                 *)
(* ----------------------------------------------------------------- *)

(* sign: `false` = 0 = positive, `true` = 1 = negative, matching
   fpa2bv_converter.cpp's mk_is_pos/mk_is_neg (which compare the raw
   sign bitvector against the 0/1 numeral). *)
type bits (ebits sbits: pos) = {
  sgn : bool;
  exp : n:nat{n < pow2 ebits};
  sig_ : n:nat{n < pow2 sbits}
}

(* mk_top_exp / mk_bot_exp (fpa2bv_converter.cpp 3894, 3898) *)
let top_exp (ebits:pos) : nat = pow2 ebits - 1
let bot_exp (ebits:pos) : nat = 0

(* ----------------------------------------------------------------- *)
(* Classification predicates (fpa2bv_converter.cpp 3760-3875)           *)
(* ----------------------------------------------------------------- *)

(* mk_is_nan: exp == top_exp /\ sig <> 0 *)
let is_nan (#ebits #sbits:pos) (x: bits ebits sbits) : bool =
  x.exp = top_exp ebits && x.sig_ <> 0

(* mk_is_inf: exp == top_exp /\ sig == 0 *)
let is_inf (#ebits #sbits:pos) (x: bits ebits sbits) : bool =
  x.exp = top_exp ebits && x.sig_ = 0

(* mk_is_pos / mk_is_neg: raw sign bit comparison *)
let is_pos (#ebits #sbits:pos) (x: bits ebits sbits) : bool = x.sgn = false
let is_neg (#ebits #sbits:pos) (x: bits ebits sbits) : bool = x.sgn = true

(* mk_is_pinf = is_pos && is_inf ; mk_is_ninf = is_neg && is_inf *)
let is_pinf (#ebits #sbits:pos) (x: bits ebits sbits) : bool = is_pos x && is_inf x
let is_ninf (#ebits #sbits:pos) (x: bits ebits sbits) : bool = is_neg x && is_inf x

(* mk_is_zero: exp == bot_exp /\ sig == 0 *)
let is_zero (#ebits #sbits:pos) (x: bits ebits sbits) : bool =
  x.exp = bot_exp ebits && x.sig_ = 0

(* mk_is_nzero / mk_is_pzero: is_zero /\ sign bit *)
let is_nzero (#ebits #sbits:pos) (x: bits ebits sbits) : bool = is_zero x && x.sgn = true
let is_pzero (#ebits #sbits:pos) (x: bits ebits sbits) : bool = is_zero x && x.sgn = false

(* mk_is_denormal: exp == 0 /\ ~is_zero (i.e. sig <> 0) *)
let is_denormal (#ebits #sbits:pos) (x: bits ebits sbits) : bool =
  x.exp = 0 && not (is_zero x)

(* mk_is_normal: not (is_special || is_denormal || is_zero), where
   is_special == (exp == top_exp). Note this coincides with
   not(is_nan || is_inf || is_denormal || is_zero), since
   is_special == is_nan || is_inf exactly (both are exp == top_exp;
   they differ only in sig, which is irrelevant to is_special itself). *)
let is_normal (#ebits #sbits:pos) (x: bits ebits sbits) : bool =
  not (x.exp = top_exp ebits) && not (is_denormal x) && not (is_zero x)

(* ----------------------------------------------------------------- *)
(* Classification lemmas: disjointness and exhaustiveness.             *)
(*                                                                      *)
(* Every bit pattern falls into exactly one of: NaN, Infinity, Zero,    *)
(* Denormal, Normal -- determined entirely by where `exp` falls in      *)
(* {0} / (0, top_exp) / {top_exp}, and (for the exp==top_exp case)      *)
(* whether `sig` is zero.                                               *)
(* ----------------------------------------------------------------- *)

let lemma_classes_exhaustive (#ebits #sbits:pos) (x: bits ebits sbits)
  : Lemma (is_nan x || is_inf x || is_zero x || is_denormal x || is_normal x)
  = ()

let lemma_classes_disjoint (#ebits #sbits:pos) (x: bits ebits sbits)
  : Lemma ((is_nan x      ==> ~(is_inf x || is_zero x || is_denormal x || is_normal x)) /\
           (is_inf x      ==> ~(is_zero x || is_denormal x || is_normal x)) /\
           (is_zero x     ==> ~(is_denormal x || is_normal x)) /\
           (is_denormal x ==> ~(is_normal x)))
  = ()

(* is_pinf / is_ninf partition is_inf by sign; is_pzero / is_nzero
   partition is_zero by sign; is_pos / is_neg are complementary. *)
let lemma_pos_neg_exclusive (#ebits #sbits:pos) (x: bits ebits sbits)
  : Lemma (is_pos x <> is_neg x)
  = ()

let lemma_inf_sign_partition (#ebits #sbits:pos) (x: bits ebits sbits)
  : Lemma (requires is_inf x) (ensures is_pinf x <> is_ninf x)
  = ()

let lemma_zero_sign_partition (#ebits #sbits:pos) (x: bits ebits sbits)
  : Lemma (requires is_zero x) (ensures is_pzero x <> is_nzero x)
  = ()

(* ----------------------------------------------------------------- *)
(* Bias / unbias (fpa2bv_converter.cpp mk_bias 3952, mk_unbias 3961)    *)
(*                                                                      *)
(* Modeled over `e : nat{e < pow2 ebits}` (the raw unsigned value of    *)
(* an `ebits`-bit exponent field), with all bitvector addition/         *)
(* extraction/concatenation translated to the corresponding mod/div     *)
(* arithmetic on that value.                                            *)
(* ----------------------------------------------------------------- *)

(* mk_bias: result = e + (2^(ebits-1) - 1), as an ebits-bit (i.e. mod
   2^ebits) addition. *)
let bias (ebits:pos{ebits >= 2}) (e:nat{e < pow2 ebits}) : nat =
  (e + (pow2 (ebits - 1) - 1)) % (pow2 ebits)

(* mk_unbias:
     e_plus_one = (f + 1) mod 2^ebits
     leading    = bit (ebits-1) of e_plus_one       (top/sign-like bit)
     n_leading  = 1 - leading                        (bitwise not of a single bit)
     rest       = low (ebits-1) bits of e_plus_one   (e_plus_one mod 2^(ebits-1))
     result     = concat(n_leading, rest)
                = n_leading * 2^(ebits-1) + rest *)
let unbias (ebits:pos{ebits >= 2}) (f:nat{f < pow2 ebits}) : nat =
  let e_plus_one = (f + 1) % (pow2 ebits) in
  let half = pow2 (ebits - 1) in
  let leading = e_plus_one / half in
  let n_leading = 1 - leading in
  let rest = e_plus_one % half in
  n_leading * half + rest

(* ----------------------------------------------------------------- *)
(* Round-trip correctness: unbias(bias(e)) == e for every valid         *)
(* exponent value e. This is the key sanity property that justifies     *)
(* the converter's "unbias" bit trick as a genuine inverse of "bias",   *)
(* rather than merely a plausible-looking circuit.                      *)
(* ----------------------------------------------------------------- *)

(* Step 1: bias(e) + 1, reduced mod 2^ebits, equals (e + half) mod
   2^ebits, where half = 2^(ebits-1). This is pure modular arithmetic:
   ((e + (half - 1)) mod M + 1) mod M == (e + half) mod M. *)
let lemma_bias_plus_one (ebits:pos{ebits >= 2}) (e:nat{e < pow2 ebits})
  : Lemma (let m = pow2 ebits in
           let half = pow2 (ebits - 1) in
           ((bias ebits e) + 1) % m == (e + half) % m)
  =
  let m = pow2 ebits in
  let half = pow2 (ebits - 1) in
  lemma_pow2_pos (ebits - 1);
  // bias ebits e == (e + (half - 1)) % m
  // (bias ebits e + 1) % m == ((e + (half-1)) % m + 1) % m
  //                        == (e + (half-1) + 1) % m      [mod/add fact]
  //                        == (e + half) % m
  FStar.Math.Lemmas.lemma_mod_add_distr 1 (e + (half - 1)) m

(* Step 2: the round-trip. We split on whether e < half or e >= half,
   mirroring the hand-verification: in the first case, (e+half) is
   already < m, in the second case it wraps around by subtracting m
   exactly once (since e < m = 2*half). *)
let lemma_bias_unbias_inverse (ebits:pos{ebits >= 2}) (e:nat{e < pow2 ebits})
  : Lemma (unbias ebits (bias ebits e) == e)
  =
  let m = pow2 ebits in
  let half = pow2 (ebits - 1) in
  lemma_pow2_pos (ebits - 1);
  assert (m == 2 * half);
  lemma_bias_plus_one ebits e;
  let f = bias ebits e in
  let e_plus_one = (f + 1) % m in
  assert (e_plus_one == (e + half) % m);
  if e < half then begin
    // e + half < 2*half = m, so the mod is a no-op.
    FStar.Math.Lemmas.small_mod (e + half) m;
    assert (e_plus_one == e + half);
    // leading = (e+half) / half == 1, since half <= e+half < 2*half.
    FStar.Math.Lemmas.lemma_div_plus e 1 half; // (e + 1*half)/half == e/half + 1
    assert (e_plus_one / half == e / half + 1);
    FStar.Math.Lemmas.small_div e half;
    assert (e_plus_one / half == 1);
    // rest = (e+half) mod half == e mod half == e.
    FStar.Math.Lemmas.lemma_mod_plus e 1 half;
    FStar.Math.Lemmas.small_mod e half
  end else begin
    // half <= e < m = 2*half, so e + half is in [m, m+half), and the
    // mod subtracts exactly one copy of m.
    assert (e + half >= m /\ e + half < m + half);
    FStar.Math.Lemmas.lemma_mod_sub (e + half) m 1;
    assert (e_plus_one == e + half - m);
    assert (e_plus_one == e - half);
    // leading = (e - half) / half == 0, since 0 <= e - half < half.
    FStar.Math.Lemmas.small_div (e - half) half;
    // rest = (e - half) mod half == e - half.
    FStar.Math.Lemmas.small_mod (e - half) half
  end
