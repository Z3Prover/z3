(*
   Z3MpfRound.fst

   Correctness proof of the rounding-DECISION logic at the heart of
   `mpf_manager::round` (src/util/mpf.cpp:1973-2093). This single
   routine is the shared "last mile" of every mpf arithmetic operation
   (add/sub/mul/div/fma/sqrt/round_to_integral all finish by calling
   `round(rm, o)` on an extended-precision significand), so correctness
   here is a correctness condition for the whole arithmetic layer, not
   just one operation.

   Scope. `round`'s job splits into two parts:

     1. Compute an extended significand of the form
        `f[-1:0].f[1:sbits-1][round,extra,sticky]` (mpf.cpp:1974) by a
        shift distance `sigma` derived from leading-zero count and the
        exponent range (mpf.cpp:1992-2037), and extract three decision
        bits `last`/`round`/`sticky` from it (mpf.cpp:2039-2051).

     2. Decide, from `(rm, sign, last, round, sticky)` alone, whether
        to increment the retained significand by 1 (mpf.cpp:2055-2062),
        then handle the resulting carry/overflow (mpf.cpp:2066-2093).

   Part 1 is bit-shifting mechanics (determining *which* integer is
   "kept" and what its true discarded remainder is) -- genuinely hard,
   out of scope here, same as `fpa2bv_converter.cpp`'s analogous
   circuit (Z3FpaConverter.fst). Part 2, the decision table itself, is
   a *finite, self-contained* piece of real/rational reasoning: given
   what `last`/`round`/`sticky` are supposed to *mean* (the kept
   integer's parity, and the discarded fraction's position relative to
   the half-way point), is the increment decision IEEE-754 correct for
   all five rounding modes? This file proves yes, closing the
   "capstone" gap flagged (but left open for lack of a `rat_eq`
   congruence toolkit) at the end of Z3FpaRoundingBits.fst, now at the
   level of the actual mpf.cpp code rather than an abstraction of it.

   The post-rounding carry propagation that follows the decision
   (mpf.cpp:2066-2072: "if significand reached 2^sbits, shift right and
   bump the exponent") is the exact same arithmetic fact as
   `lemma_succ_binade_boundary` in Z3FpaRoundingBits.fst; we do not
   reprove it here, only note the connection in MPF_REPORT.md.
*)
module Z3MpfRound

(* ----------------------------------------------------------------- *)
(* Self-contained rational numbers, as in Z3FpaRoundingAudit.fst.      *)
(* ----------------------------------------------------------------- *)

type rat = { num: int; den: pos }

let mk_int (n:int) : rat = { num = n; den = 1 }
let mk_frac (n:int) (d:pos) : rat = { num = n; den = d }

let rat_eq (a b:rat) : bool = a.num * b.den = b.num * a.den
let rat_lt (a b:rat) : bool = a.num * b.den < b.num * a.den
let rat_le (a b:rat) : bool = a.num * b.den <= b.num * a.den

(* ----------------------------------------------------------------- *)
(* The five mpf rounding modes (mpf.h's `mpf_rounding_mode` enum).     *)
(* ----------------------------------------------------------------- *)

type rounding_mode =
  | RNE  // MPF_ROUND_NEAREST_TEVEN
  | RNA  // MPF_ROUND_NEAREST_TAWAY
  | RTP  // MPF_ROUND_TOWARD_POSITIVE
  | RTN  // MPF_ROUND_TOWARD_NEGATIVE
  | RTZ  // MPF_ROUND_TOWARD_ZERO

(* ----------------------------------------------------------------- *)
(* Ground truth: what `last`/`round`/`sticky` are meant to represent.  *)
(*                                                                      *)
(* After the normalization shift, `round()` holds an infinite-precision *)
(* true value of the form                                              *)
(*                                                                      *)
(*     true_value = kept_int + frac,     0 <= frac < 1                 *)
(*                                                                      *)
(* where `kept_int` is the (to-be-rounded, sign-less) significand that  *)
(* remains after discarding the bottom 3 bits, and `frac` is the exact  *)
(* discarded fraction, in units of one ulp of `kept_int`. The code      *)
(* extracts (mpf.cpp:2039-2051):                                        *)
(*                                                                      *)
(*   last   = parity of kept_int (true <=> kept_int is odd)             *)
(*   round  = the single bit worth exactly 1/2 ulp (true <=> frac>=1/2) *)
(*   sticky = OR of every bit below that (true <=> frac is not a        *)
(*            multiple of 1/2, i.e. frac in (0,1/2) u (1/2,1))          *)
(*                                                                      *)
(* We derive round/sticky from `frac` directly, by this specification,  *)
(* rather than from the bit-shifting mechanics (out of scope, see       *)
(* header comment).                                                     *)
(* ----------------------------------------------------------------- *)

let half : rat = mk_frac 1 2
let zero : rat = mk_int 0

let round_bit (frac:rat) : bool = rat_le half frac
let sticky_bit (frac:rat) : bool = not (rat_eq frac zero) && not (rat_eq frac half)

(* ----------------------------------------------------------------- *)
(* `mpf_round_inc`: a verbatim transcription of the switch statement   *)
(* at mpf.cpp:2056-2061.                                                *)
(* ----------------------------------------------------------------- *)

let mpf_round_inc (rm:rounding_mode) (sign last round sticky:bool) : bool =
  match rm with
  | RNE -> round && (last || sticky)
  | RNA -> round
  | RTP -> (not sign) && (round || sticky)
  | RTN -> sign && (round || sticky)
  | RTZ -> false

(* ----------------------------------------------------------------- *)
(* `correct_inc`: the independent IEEE-754 ground truth -- "should the  *)
(* magnitude be rounded up to kept_int+1, given the exact (sign, parity,*)
(* discarded fraction) and rounding-mode semantics?" -- written         *)
(* directly from the IEEE-754 definitions (nearest/ties-to-even,         *)
(* nearest/ties-away, directed toward +-infinity, toward zero), with no *)
(* reference to mpf.cpp's bit-level formula.                            *)
(* ----------------------------------------------------------------- *)

let correct_inc (rm:rounding_mode) (sign last:bool) (frac:rat{rat_le zero frac /\ rat_lt frac (mk_int 1)}) : bool =
  if rat_eq frac zero then
    false                                  // exact: never round away from the kept value
  else if rat_lt frac half then
    (match rm with
     | RTP -> not sign                     // ceiling: bump positive magnitudes up
     | RTN -> sign                         // floor:   bump negative magnitudes up
     | _   -> false)                       // nearest modes and RTZ: below halfway, keep
  else if rat_eq frac half then
    (match rm with
     | RNE -> last                         // exact tie: break to even (odd kept -> bump)
     | RNA -> true                         // exact tie: always away from zero -> bump
     | RTP -> not sign
     | RTN -> sign
     | RTZ -> false)
  else                                      // frac > 1/2
    (match rm with
     | RTZ -> false                        // truncate regardless
     | RTP -> not sign
     | RTN -> sign
     | _   -> true)                        // RNE, RNA: strictly more than half -> bump

(* ----------------------------------------------------------------- *)
(* Main theorem: `round()`'s literal decision formula agrees with the   *)
(* independent IEEE-754 ground truth, for every rounding mode, sign,    *)
(* kept-value parity, and every possible discarded fraction in [0,1).   *)
(* ----------------------------------------------------------------- *)

let lemma_round_decision_correct
    (rm:rounding_mode) (sign last:bool) (frac:rat{rat_le zero frac /\ rat_lt frac (mk_int 1)})
  : Lemma (ensures mpf_round_inc rm sign last (round_bit frac) (sticky_bit frac) = correct_inc rm sign last frac)
  =
  // Case split exactly mirrors the case split inside `correct_inc`,
  // so that `round_bit`/`sticky_bit` reduce to concrete booleans on
  // each branch and both sides of the equation become literal
  // boolean formulas that Z3 discharges directly.
  if rat_eq frac zero then ()
  else if rat_lt frac half then ()
  else if rat_eq frac half then ()
  else ()

(* ----------------------------------------------------------------- *)
(* Sanity corollaries: concrete instances pinning down the reading of   *)
(* each mode, so a future reader/reviewer can spot-check the theorem    *)
(* against familiar examples without re-deriving the case split.        *)
(* ----------------------------------------------------------------- *)

(* RNE: an exact tie (frac = 1/2) on an already-even kept value does    *)
(* NOT round up (stays at the even candidate). *)
let lemma_rne_tie_even_no_bump ()
  : Lemma (mpf_round_inc RNE false false (round_bit half) (sticky_bit half) = false)
  = ()

(* RNE: an exact tie on an odd kept value DOES round up (to make it     *)
(* even). *)
let lemma_rne_tie_odd_bumps ()
  : Lemma (mpf_round_inc RNE false true (round_bit half) (sticky_bit half) = true)
  = ()

(* RNA: an exact tie always rounds away from the kept value, regardless *)
(* of parity. *)
let lemma_rna_tie_always_bumps (last:bool)
  : Lemma (mpf_round_inc RNA false last (round_bit half) (sticky_bit half) = true)
  = ()

(* RTZ: never increments, for any sign/parity/fraction -- pure           *)
(* truncation. *)
let lemma_rtz_never_bumps (sign last:bool) (frac:rat{rat_le zero frac /\ rat_lt frac (mk_int 1)})
  : Lemma (mpf_round_inc RTZ sign last (round_bit frac) (sticky_bit frac) = false)
  = ()

(* RTP (toward +infinity): a positive number with any nonzero discarded *)
(* fraction rounds its magnitude up (ceiling); a negative number never   *)
(* does (truncating the magnitude moves the signed value toward +inf).  *)
let lemma_rtp_positive_any_discard_bumps (last:bool)
  : Lemma (mpf_round_inc RTP false last (round_bit half) (sticky_bit half) = true)
  = ()

let lemma_rtp_negative_never_bumps (last:bool) (frac:rat{rat_le zero frac /\ rat_lt frac (mk_int 1)})
  : Lemma (mpf_round_inc RTP true last (round_bit frac) (sticky_bit frac) = false)
  = ()
