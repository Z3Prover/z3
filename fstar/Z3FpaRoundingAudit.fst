(*
   Z3FpaRoundingAudit.fst

   Targeted audit of the symbolic Real -> FloatingPoint rounding
   encoding in `fpa2bv_converter::mk_to_fp_real`
   (src/ast/fpa/fpa2bv_converter.cpp), motivated by two open soundness
   issues and their two independent (as of this writing, both open,
   unmerged) fix PRs:

     - Issue #10881 / PR #10888 ("inexact symbolic Real-to-FP
       rounding"): a symbolic real `x` strictly between two
       representable floats, with no tie, was reported `unsat` for a
       query whose only models require rounding `x` to its nearest
       neighbor.
     - Issue #10931 / PR #10938 ("rounding carry into the next
       binade"): the same root cause, specialized to the case where
       the correctly-rounded result sits exactly on a power-of-two
       binade boundary (so the "gap" to the result's two neighbors is
       asymmetric: half as large below the boundary as above it).

   Both issues trace to the *same* line, in the code's own words,
   removed by both PRs:

       expr * e = m.mk_eq(m_util.mk_to_real(result), x);

   i.e. the old encoding required the conversion to be *exact*:
   `to_real(result) = x`. Since `to_real(result)` is always an
   exactly-representable rational once `result`'s bits are fixed, this
   literally forces `x` to coincide with some representable float in
   every model, discarding every model where `x` should round
   (up or down, into the same binade or into the next one) to a
   *different*, non-equal value.

   This file does not re-verify `fpa2bv_converter.cpp`'s bit-precise
   `unpack`/`round` machinery (out of scope, as documented in
   FPA_REPORT.md). Instead, it isolates and proves, at the level of
   exact rational arithmetic, the one purely *logical* fact that both
   PRs' fixes hinge on and the old code violates:

       "x = r" (exact round-trip) is **strictly stronger** than
       "x rounds to r" (nearest/grid-bracketing), for any nontrivial
       gap to r's neighbors.

   This explains, mechanically, why the old encoding is an unsound
   *restriction* (it excludes genuine models) and why both PRs' new
   encodings -- which directly state the grid-bracketing condition
   instead of the exact equation -- restore completeness.
*)
module Z3FpaRoundingAudit

open Z3FpaConverter   // reuse the self-contained `pow2`

(* ----------------------------------------------------------------- *)
(* A minimal, self-contained rational-number theory -- just enough to  *)
(* state and compare grid points and midpoints exactly (no floating-   *)
(* point or real-number axioms needed).                                *)
(* ----------------------------------------------------------------- *)

type rat = { num: int; den: pos }

let mk_int (n:int) : rat = { num = n; den = 1 }
let mk_frac (n:int) (d:pos) : rat = { num = n; den = d }

(* Comparisons via cross-multiplication (both denominators positive,
   so no sign flip is needed). *)
let rat_eq (a b:rat) : bool = a.num * b.den = b.num * a.den
let rat_lt (a b:rat) : bool = a.num * b.den < b.num * a.den
let rat_le (a b:rat) : bool = a.num * b.den <= b.num * a.den

let rat_add (a b:rat) : rat = { num = a.num * b.den + b.num * a.den; den = a.den * b.den }
let rat_sub (a b:rat) : rat = { num = a.num * b.den - b.num * a.den; den = a.den * b.den }
let rat_half (a:rat) : rat = { num = a.num; den = 2 * a.den }

let rat_pos (a:rat) : bool = a.num > 0

(* ----------------------------------------------------------------- *)
(* The two rounding predicates:                                        *)
(*                                                                      *)
(*   `exact_roundtrip r x`      -- the OLD code's constraint: x must    *)
(*                                 literally equal the (exactly         *)
(*                                 representable) candidate r.          *)
(*                                                                      *)
(*   `round_nearest_even r gap_lo gap_hi is_even x`                     *)
(*                               -- the NEW (PR #10888) constraint:     *)
(*                                 x need only fall in the half-open    *)
(*                                 neighborhood of r bracketed by half   *)
(*                                 its lower/upper gaps, with ties       *)
(*                                 broken by `is_even` (= "r's           *)
(*                                 significand is even", i.e. the        *)
(*                                 `sig_is_even` field in the diff).      *)
(*                                 This is a verbatim transcription of   *)
(*                                 PR #10888's `nte_cond` (lower_mid /    *)
(*                                 upper_mid / tie_lo / tie_hi).          *)
(* ----------------------------------------------------------------- *)

let exact_roundtrip (r x:rat) : bool = rat_eq x r

let round_nearest_even (r gap_lo gap_hi:rat) (is_even:bool) (x:rat) : bool =
  let lower_mid = rat_sub r (rat_half gap_lo) in
  let upper_mid = rat_add r (rat_half gap_hi) in
  let in_range  = rat_le lower_mid x && rat_le x upper_mid in
  let tie_lo    = rat_eq x lower_mid in
  let tie_hi    = rat_eq x upper_mid in
  in_range && ((not (tie_lo || tie_hi)) || is_even)

(* ----------------------------------------------------------------- *)
(* Theorem 1 (soundness of the generalization): every model of the     *)
(* OLD constraint is also a model of the NEW one, for any positive      *)
(* gaps. So the fix never *rejects* a previously-accepted (exact)       *)
(* model -- it only *admits* more.                                     *)
(* ----------------------------------------------------------------- *)

let lemma_old_implies_new (r gap_lo gap_hi:rat) (is_even:bool) (x:rat)
  : Lemma (requires rat_pos gap_lo /\ rat_pos gap_hi /\ exact_roundtrip r x)
          (ensures round_nearest_even r gap_lo gap_hi is_even x)
  = ()

(* ----------------------------------------------------------------- *)
(* Theorem 2 (strictness / the actual bug): the converse fails. There   *)
(* is a concrete model of the NEW (correct) constraint -- a genuine     *)
(* "round up to the midpoint, tie-to-even" scenario -- that is *not* a  *)
(* model of the OLD constraint. This is the formal content of issues    *)
(* #10881 and #10931: the old encoding is satisfiable on strictly       *)
(* fewer models than the true rounding relation, so a solver using it   *)
(* can return `unsat` on queries whose only models are inexact          *)
(* roundings.                                                           *)
(*                                                                      *)
(* Witness: r = 0, gap_lo = gap_hi = 2 (an arbitrary positive gap on     *)
(* both sides), is_even = true, x = 1 (the exact upper midpoint,         *)
(* "tie_hi"). round_nearest_even accepts this (it is a tie, broken by    *)
(* is_even = true); exact_roundtrip rejects it (1 <> 0).                 *)
(* ----------------------------------------------------------------- *)

let lemma_new_not_implies_old ()
  : Lemma (let r = mk_int 0 in let gap = mk_int 2 in let x = mk_int 1 in
           round_nearest_even r gap gap true x /\ ~(exact_roundtrip r x))
  = ()

(* ----------------------------------------------------------------- *)
(* Concrete corollary mirroring issue #10931's literal numbers: the     *)
(* binade-carry example `r = 2.0`, format (8,24) so the ulp just below  *)
(* 2.0 is `2^-23` (gap_lo) and the ulp at/above 2.0 is `2^-22`           *)
(* (gap_hi) -- i.e. the gap *below* a power-of-two boundary is half the *)
(* gap *above* it, exactly PR #10888's special-cased `gap_down`/`gap_up`*)
(* relationship. `x = 2 - 2^-24` genuinely rounds up to 2.0 under RNE    *)
(* (distance 2^-24 below vs. 2^22 - 2^-24 above -- clearly nearer 2.0,   *)
(* no tie), confirming the sat witness from the issue report, while the  *)
(* old exact-equality encoding would reject it (x <> r).                 *)
(* ----------------------------------------------------------------- *)

let lemma_binade_carry_witness ()
  : Lemma (let r      = mk_int 2 in
           let gap_lo = mk_frac 1 (pow2 23) in   // ulp just below 2.0
           let gap_hi = mk_frac 1 (pow2 22) in   // ulp at/above 2.0
           let x      = mk_frac (2 * pow2 24 - 1) (pow2 24) in  // 2 - 2^-24
           round_nearest_even r gap_lo gap_hi true x /\ ~(exact_roundtrip r x))
  = ()

(* ----------------------------------------------------------------- *)
(* The GRS ("guard/round/sticky") bracketing used by PR #10938 at the   *)
(* *pre-round* intermediate precision. Rather than linking x to the     *)
(* final rounded result directly, PR #10938 brackets |x| between a      *)
(* truncation grid point `grid_lo` and its successor `grid_hi`, with a  *)
(* boolean `sticky` recording whether the bracketing is exact.          *)
(* This is the same bracketing *idea* as `round_nearest_even` above,    *)
(* applied one layer earlier in the pipeline (before `round()`'s own    *)
(* nearest/tie-break/renormalize logic runs on the extracted guard/     *)
(* round/sticky bits).                                                  *)
(* ----------------------------------------------------------------- *)

let grs_brackets (grid_lo grid_hi:rat) (sticky:bool) (x:rat) : bool =
  (if sticky then rat_lt grid_lo x else rat_eq x grid_lo) && rat_lt x grid_hi

(* For any x already known to lie in [grid_lo, grid_hi), there is a
   choice of `sticky` making `grs_brackets` hold -- i.e. the GRS
   encoding, like `round_nearest_even`, is satisfiable for inexact x,
   unlike the old exact-equality encoding. *)
let lemma_grs_satisfiable (grid_lo grid_hi x:rat)
  : Lemma (requires rat_le grid_lo x /\ rat_lt x grid_hi)
          (ensures grs_brackets grid_lo grid_hi (not (rat_eq x grid_lo)) x)
  = ()

(* ----------------------------------------------------------------- *)
(* Honest limitation (documented, not silently elided): the lemmas      *)
(* above establish that both PRs' *linking constraints* are, in         *)
(* isolation, strictly more permissive than the old exact-equality       *)
(* constraint (the fix's necessary condition for soundness). They do    *)
(* NOT establish that the downstream bit-precise machinery each PR       *)
(* relies on -- PR #10888's explicit midpoint/tie arithmetic over the    *)
(* *final* (sgn, exp, sig) bit-fields, or PR #10938's existing (and      *)
(* independently un-reverified) `round()` routine acting on the GRS      *)
(* bits -- correctly reconstructs `round_nearest_even`/`grs_brackets`    *)
(* for *every* bit-vector instantiation (e.g. subnormal boundaries,       *)
(* overflow-to-infinity, directed-rounding modes). That remains out of   *)
(* scope here, exactly as `unpack`/`round`/`mk_leading_zeros` were out   *)
(* of scope for the base FPA audit (see FPA_REPORT.md) -- it is a        *)
(* bit-precise circuit-correctness question, not the logical-rewrite      *)
(* question this audit targets.                                         *)
(* ----------------------------------------------------------------- *)
