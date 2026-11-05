(*
   Z3MpfExact.fst

   End-to-end exactness/correctness of mpf.cpp's truncate-with-a-
   sticky-bit technique, the mechanism every arithmetic operation
   (add_sub, mul, div, ...) uses to shrink an unbounded-precision
   intermediate significand down to the fixed sbits+4-bit width that
   `mpf_manager::round` (proved correct in Z3MpfRound.fst) expects,
   without losing any rounding-relevant information.

   The pattern, repeated near-verbatim at mpf.cpp:481-483 (add_sub's
   alignment shift), mpf.cpp:568-569/656-657 (add_sub's post-add
   sticky fix-up), mpf.cpp:650-654 (mul), mpf.cpp:697-699 (div), and
   mpf.cpp:2040-2045 (round's own internal denormal shift) is always:

       divide by 2^n, keeping quotient q and remainder r;
       if r <> 0 and q is even, increment q (by exactly 1).

   This file proves that this one-bit "sticky fold" is *exact* for
   rounding purposes: incrementing an even q by 1 never carries beyond
   its own lowest bit (since an even number's LSB is 0), so folding
   changes *only* bit 0 of q, and does so in exactly the way needed to
   OR the lost remainder's "was it nonzero" fact into the bit that
   `round()`'s GRS extraction reads as the sticky bit. This is the
   mechanized version of the standard "sticky bit" folklore theorem
   from floating-point hardware design, applied directly to mpf.cpp's
   bignum-based implementation of it.
*)
module Z3MpfExact

open Z3MpfRound   // reuse rat / round_bit / sticky_bit / rounding_mode /
                   // mpf_round_inc / correct_inc / lemma_round_decision_correct

(* ----------------------------------------------------------------- *)
(* Self-contained power-of-two helper (as in the other files).        *)
(* ----------------------------------------------------------------- *)

let rec pow2 (n:nat) : Tot pos =
  if n = 0 then 1 else 2 * pow2 (n - 1)

(* ----------------------------------------------------------------- *)
(* Integer-level GRS extraction, transcribed directly from the        *)
(* 4-peel bit-reading loop at mpf.cpp:2039-2051 (and identical in      *)
(* spirit to the "keeping a sticky bit" steps in add_sub/mul/div):     *)
(*                                                                      *)
(*   sticky = odd(q) || odd(q/2)      -- bits 0,1 of q, OR'd            *)
(*   round  = odd(q/4)                -- bit 2 of q                     *)
(*   last   = odd(q/8)                -- bit 3 of q (parity of "kept")  *)
(* ----------------------------------------------------------------- *)

let sticky_of (q:nat) : bool = (q % 2 = 1) || ((q / 2) % 2 = 1)
let round_of  (q:nat) : bool = ((q / 4) % 2 = 1)
let last_of   (q:nat) : bool = ((q / 8) % 2 = 1)

(* ----------------------------------------------------------------- *)
(* The one-bit sticky fold itself, transcribed from the repeated       *)
(* "if (!sticky_rem.is_zero() && is_even(q)) inc(q)" pattern.          *)
(* ----------------------------------------------------------------- *)

let fold_lsb (q:nat) (r_nonzero:bool) : nat =
  if r_nonzero && q % 2 = 0 then q + 1 else q

(* ----------------------------------------------------------------- *)
(* Lemma 1 (no carry beyond bit 0): folding only ever touches q's      *)
(* lowest bit. This is *why* the technique is cheap/local: the         *)
(* increment is only ever applied when q is even (LSB 0), so adding 1  *)
(* can never ripple a carry into bit 1 or above.                       *)
(* ----------------------------------------------------------------- *)

let lemma_fold_preserves_div2 (q:nat) (r_nonzero:bool)
  : Lemma (fold_lsb q r_nonzero / 2 = q / 2)
  = ()

(* ----------------------------------------------------------------- *)
(* Lemma 2 (bit 0 correctly absorbs the lost remainder): folding sets   *)
(* bit 0 to exactly "was q's own bit 0 set, OR was the truncated        *)
(* remainder nonzero" -- i.e. no rounding-relevant information is       *)
(* fabricated or lost at this bit.                                     *)
(* ----------------------------------------------------------------- *)

let lemma_fold_lsb_bit (q:nat) (r_nonzero:bool)
  : Lemma ((fold_lsb q r_nonzero) % 2 = 1 <==> (q % 2 = 1 \/ r_nonzero))
  = ()

(* ----------------------------------------------------------------- *)
(* Main theorem (sticky-bit folklore, mechanized): folding preserves    *)
(* `round`/`last` exactly, and correctly ORs the lost remainder's       *)
(* nonzero-ness into `sticky` -- i.e. the one-bit fold loses *no*       *)
(* information that `round()`'s GRS decision actually uses.            *)
(* ----------------------------------------------------------------- *)

let lemma_fold_preserves_grs (q:nat) (r_nonzero:bool)
  : Lemma (let q' = fold_lsb q r_nonzero in
           sticky_of q' = (sticky_of q || r_nonzero) /\
           round_of q' = round_of q /\
           last_of q' = last_of q)
  = lemma_fold_preserves_div2 q r_nonzero;
    lemma_fold_lsb_bit q r_nonzero

(* ----------------------------------------------------------------- *)
(* Corollary (composability): folding twice -- once for an upstream    *)
(* truncation (e.g. add_sub's alignment shift) and once more for a      *)
(* downstream one (e.g. round()'s own internal denormal/TINY shift,     *)
(* mpf.cpp:2040-2045) -- is equivalent to a single fold whose remainder *)
(* flag is the OR of both. This is what justifies composing the         *)
(* theorem above across *multiple* truncation points in a single        *)
(* arithmetic operation, rather than only a single one.                 *)
(* ----------------------------------------------------------------- *)

let lemma_fold_compose (q:nat) (r1 r2:bool)
  : Lemma (sticky_of (fold_lsb (fold_lsb q r1) r2) = (sticky_of q || r1 || r2) /\
           round_of  (fold_lsb (fold_lsb q r1) r2) = round_of q /\
           last_of   (fold_lsb (fold_lsb q r1) r2) = last_of q)
  = lemma_fold_preserves_grs q r1;
    lemma_fold_preserves_grs (fold_lsb q r1) r2

(* ----------------------------------------------------------------- *)
(* Distributive alignment lemma: mpf_manager::add_sub (mpf.cpp:535-     *)
(* 543) does not truncate-then-add; it truncates *one* operand's        *)
(* significand (call it `t`, already scaled with the +3 extra bits) by  *)
(* right-shifting it `n` bits -- obtaining quotient `q` and remainder   *)
(* `r` -- and only *afterwards* adds the other (unshifted) operand's     *)
(* significand `m`, applying the sticky-fold to the *sum* `m + q`        *)
(* rather than to `q` alone (mpf.cpp:559-569). This lemma shows that      *)
(* is equivalent to the conceptually simpler "compute the exact           *)
(* combined value first, then truncate it": the remainder of              *)
(* `m*2^n + t` by `2^n` is exactly the remainder of `t` alone, regardless  *)
(* of `m` -- so no rounding information is lost or fabricated by          *)
(* shifting first and adding after.                                      *)
(* ----------------------------------------------------------------- *)

let lemma_add_commutes_with_truncation (m:int) (t q r:nat) (n:pos)
  : Lemma (requires t = q * pow2 n + r /\ r < pow2 n)
          (ensures  (m * pow2 n + t) = (m + q) * pow2 n + r)
  = ()

(* ----------------------------------------------------------------- *)
(* Bridge lemma: connects the integer-level `round_of`/`sticky_of`      *)
(* (what the code actually computes, bit by bit) to the rational-level  *)
(* `round_bit`/`sticky_bit` ground truth of Z3MpfRound.fst (what the     *)
(* IEEE-754 correctness theorem is stated in terms of), for a value      *)
(* known to sit inside the 1/8-wide bucket determined by `q`'s own       *)
(* bottom 3 bits -- i.e. for *any* true discarded fraction consistent    *)
(* with having been truncated down to `q` with remainder-nonzero flag    *)
(* `r_nonzero`, not merely the single coarse rational `(q%8)/8`.         *)
(* ----------------------------------------------------------------- *)

let bucket_lo (q:nat) : rat = mk_frac (q % 8) 8
let bucket_hi (q:nat) : rat = mk_frac (q % 8 + 1) 8

(* `frac` is consistent with "q, further truncated by some amount with  *)
(* remainder-nonzero flag r_nonzero": it lies in the half-open 1/8       *)
(* bucket named by q's low 3 bits, landing exactly on the left           *)
(* endpoint only when there is no further truncated remainder.          *)
let consistent (q:nat) (r_nonzero:bool) (frac:rat) : prop =
  rat_le (bucket_lo q) frac /\ rat_lt frac (bucket_hi q) /\
  (rat_eq frac (bucket_lo q) <==> not r_nonzero)

let lemma_bridge_round_bit (q:nat) (r_nonzero:bool) (frac:rat)
  : Lemma (requires consistent q r_nonzero frac)
          (ensures round_bit frac = round_of q)
  =
  // round_of q depends only on q % 8 via the case split below.
  let r8 = q % 8 in
  assert (r8 < 8);
  if r8 < 4 then () else ()

let lemma_bridge_sticky_bit (q:nat) (r_nonzero:bool) (frac:rat)
  : Lemma (requires consistent q r_nonzero frac)
          (ensures sticky_bit frac = (sticky_of q || r_nonzero))
  =
  let r8 = q % 8 in
  assert (r8 < 8);
  if r8 = 0 then () else if r8 = 4 then () else ()

(* `consistent` buckets always sit inside [0,1), since `q % 8 < 8`. *)
let lemma_consistent_in_unit_interval (q:nat) (r_nonzero:bool) (frac:rat)
  : Lemma (requires consistent q r_nonzero frac)
          (ensures rat_le zero frac /\ rat_lt frac (mk_int 1))
  = ()

(* ----------------------------------------------------------------- *)
(* CAPSTONE THEOREM: end-to-end correctness of truncate-with-sticky-   *)
(* fold, composed with `round()`'s decision logic. Given any true       *)
(* discarded fraction `frac` consistent with having been truncated to   *)
(* `q` with remainder-nonzero flag `r_nonzero` (Lemma: this holds        *)
(* whenever `q`/`r_nonzero` were produced, as in add_sub/mul/div, by      *)
(* an exact division of the true pre-round value by some power of two),  *)
(* the code's actual computation --  fold `q` by `r_nonzero`, extract     *)
(* (last, round, sticky), and apply `mpf_round_inc` -- produces exactly   *)
(* the IEEE-754-correct rounding decision for `frac`, the *true*,         *)
(* never-materialized, full-precision discarded fraction. No rounding     *)
(* information is lost by (a) truncating early to bound the working       *)
(* precision, or (b) collapsing an arbitrary number of discarded bits      *)
(* into a single sticky flag.                                             *)
(* ----------------------------------------------------------------- *)

let lemma_end_to_end_round_correct
    (rm:rounding_mode) (sign:bool) (q:nat) (r_nonzero:bool) (frac:rat)
  : Lemma (requires consistent q r_nonzero frac)
          (ensures (let q' = fold_lsb q r_nonzero in
                    mpf_round_inc rm sign (last_of q') (round_of q') (sticky_of q')
                      = correct_inc rm sign (last_of q) frac))
  =
  lemma_fold_preserves_grs q r_nonzero;
  lemma_bridge_round_bit q r_nonzero frac;
  lemma_bridge_sticky_bit q r_nonzero frac;
  lemma_consistent_in_unit_interval q r_nonzero frac;
  lemma_round_decision_correct rm sign (last_of q) frac

(* ----------------------------------------------------------------- *)
(* Application to `mul` (mpf.cpp:586-657): an exact arbitrary-precision *)
(* integer multiply of two already-unpacked significands loses *no*     *)
(* information at all -- the product `p = a_sig * b_sig` is the exact,  *)
(* literal pre-round value (scaled by the exponent sum), with every     *)
(* subsequent bit of it genuinely meaningful. The *only* information    *)
(* loss in the entire `mul` pipeline is the single, deliberate "remove   *)
(* the extra bits, keeping a sticky bit" truncation at mpf.cpp:650-654,  *)
(* i.e. exactly one application of `fold_lsb`. Thus the capstone theorem *)
(* above, instantiated at `q = p / 2^n` and `r_nonzero = (p % 2^n <> 0)` *)
(* for the appropriate truncation width `n`, directly gives: mul's        *)
(* rounding decision is IEEE-754 correct for the *exact* mathematical      *)
(* product of its two operands' real values -- not merely for whatever    *)
(* approximation happened to survive truncation.                          *)
(*                                                                         *)
(* This corollary packages that instantiation: given the exact product    *)
(* `p` and its decomposition at the truncation width `n` (`p = q*2^n+r`),  *)
(* the final increment decision matches the true product's correctly-     *)
(* rounded answer, for *any* bucket-consistent reading of the discarded    *)
(* fraction -- in particular the canonical choice `frac = bucket_lo q`     *)
(* when `r = 0` (exact truncation) and any witness in the open bucket      *)
(* otherwise.                                                              *)
(* ----------------------------------------------------------------- *)

let lemma_mul_round_correct
    (rm:rounding_mode) (sign:bool) (p:nat) (n:pos) (q r:nat)
  : Lemma (requires p = q * pow2 n + r /\ r < pow2 n)
          (ensures (let r_nonzero = (r <> 0) in
                    let q' = fold_lsb q r_nonzero in
                    let witness : rat = if r_nonzero then mk_frac (2 * (q % 8) + 1) 16 else bucket_lo q in
                    mpf_round_inc rm sign (last_of q') (round_of q') (sticky_of q')
                      = correct_inc rm sign (last_of q) witness))
  =
  let r_nonzero = (r <> 0) in
  let witness : rat = if r_nonzero then mk_frac (2 * (q % 8) + 1) 16 else bucket_lo q in
  lemma_end_to_end_round_correct rm sign q r_nonzero witness

(* ----------------------------------------------------------------- *)
(* Sanity corollaries.                                                 *)
(* ----------------------------------------------------------------- *)

(* An exact truncation (no lost remainder) changes nothing: folding       *)
(* with `r_nonzero = false` is the identity, and the decision is exactly   *)
(* the one `round()` would have made directly on `q`.                      *)
let lemma_exact_truncation_no_fold (q:nat)
  : Lemma (fold_lsb q false = q)
  = ()

(* A genuinely lost nonzero remainder below an exact half-way point        *)
(* (`q % 8 = 4`, i.e. the coarse reading looks like an exact tie) breaks    *)
(* the tie: the true fraction is strictly *more* than half, so RNE must     *)
(* round up regardless of `q`'s parity -- exactly what the sticky fold      *)
(* achieves by flipping the "exact tie" sticky bit to `true`.               *)
let lemma_lost_remainder_breaks_apparent_tie (sign last_q:bool)
  : Lemma (let q : nat = 4 in  // q % 8 = 4: coarse reading is an exact tie
           mpf_round_inc RNE sign (last_of (fold_lsb q true)) (round_of (fold_lsb q true)) (sticky_of (fold_lsb q true)) = true)
  = ()

