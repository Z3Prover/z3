# Audit: Open Floating-Point Issues/PRs vs. the `to_fp`-from-Real Rounding Encoding

This report is a focused follow-up to [`FPA_REPORT.md`](FPA_REPORT.md),
triggered by a review of currently **open** GitHub issues/PRs labeled
`Floats` on `Z3Prover/z3`. It extracts a precise correctness condition
for `fpa2bv_converter::mk_to_fp_real`'s symbolic (non-numeral) Real ->
FloatingPoint rounding encoding, and mechanically verifies (in F*,
see `Z3FpaRoundingAudit.fst`) that the **existing** (currently merged,
on `master`) encoding fails that condition, while the **new** encoding
proposed by two independent open PRs restores it.

## Open issues (label `Floats`)

| # | Title | Status |
|---|---|---|
| [#10931](https://github.com/Z3Prover/z3/issues/10931) | Unsound unsat: `to_fp` from a symbolic Real loses the rounding carry into the next binade | open, has fix PR #10938 |
| [#10881](https://github.com/Z3Prover/z3/issues/10881) | False `unsat` for inexact symbolic Real-to-binary64 rounding | open, has fix PR #10888 |
| [#10176](https://github.com/Z3Prover/z3/issues/10176) | [Solution Soundness Bug] Incorrect SAT in Float32 FP/Real round-trip arithmetic | open |
| [#9953](https://github.com/Z3Prover/z3/issues/9953) | [Refutational Soundness Bug] Incorrect UNSAT in Float32 FP/Real round-trip arithmetic | open |
| [#8052](https://github.com/Z3Prover/z3/issues/8052) | Unsat only with unnecessary asserts, else unknown | open |
| [#7842](https://github.com/Z3Prover/z3/issues/7842) | Incorrect model | open |
| [#7431](https://github.com/Z3Prover/z3/issues/7431) | Invalid model issue on float formula | open |

**#10931 and #10881 are the same root cause**: both trace to the single
exact round-trip equality `m.mk_eq(m_util.mk_to_real(result), x)` in
`fpa2bv_converter::mk_to_fp_real`'s symbolic branch (`fpa2bv_converter.cpp`,
~line 2949). #10881 exhibits it as a tie-break failure strictly inside a
binade; #10931 exhibits it at a power-of-two binade boundary (where the
rounding "carries" into the next exponent). #9953/#10176 are earlier
reports of what looks like the same class of Float32 round-trip
soundness bug (titles describe round-trip arithmetic unsoundness in
both directions); they were not independently re-triaged against the
current code as part of this audit. #8052/#7842/#7431 appear unrelated
to the rounding-encoding bug targeted here (no overlap with
`mk_to_fp_real`'s symbolic branch in their reports) and were not
further investigated.

## Open PRs (label `Floats`)

| # | Title | Fixes | CI |
|---|---|---|---|
| [#10888](https://github.com/Z3Prover/z3/pull/10888) | Fix false `unsat` for inexact symbolic Real-to-FloatingPoint rounding | #10881 | all green |
| [#10938](https://github.com/Z3Prover/z3/pull/10938) | Fix unsound `to_fp` rounding: symbolic Real→FP conversion lost carry into next binade | #10931 | CLA only (full CI not yet observed complete) |

**Both PRs touch the same line and the same function** (`mk_to_fp_real`'s
symbolic branch) but take **different, independent approaches**:

- **#10888** removes the exact-equality constraint and replaces it with
  an explicit midpoint/tie-break condition stated directly in terms of
  the *final* rounded result's bit-fields (`ulp`, `gap_up`/`gap_down`,
  `lower_mid`/`upper_mid`, `tie_lo`/`tie_hi`, `sig_is_even`), for all
  five rounding modes, plus directed-mode saturation at the largest
  finite value.
- **#10938** removes the same constraint but instead links the
  *pre-round*, extended-precision `(sgn, sig, exp)` triple to `x` via a
  guard/round/sticky ("GRS") bracketing (`sig_hi`/`sticky` bracket `|x|`
  against a grid point), plus a normalization side-condition, then lets
  the existing (unmodified) `round()` routine do the actual
  nearest/tie/renormalize/overflow logic.

Since both are open simultaneously and edit overlapping lines, **only
one can land as written** — merging both would conflict. Based on the
analysis below, #10888's encoding is self-contained and independently
checkable; #10938's correctness additionally depends on `round()`'s
(unaudited, bit-precise) renormalization behavior.

## Correctness condition

The symbolic rounding encoding's job is: given rounding mode `rm`, input
real `x`, and a candidate result `r` (with real value `r.real` and
known gaps `gap_lo`/`gap_hi` to its predecessor/successor), decide
whether `r` is correctly `rm`-rounded from `x`. For round-to-nearest
modes this is the textbook definition:

```
round_nearest_even(r, gap_lo, gap_hi, is_even, x) :=
    let lower_mid = r - gap_lo/2 in
    let upper_mid = r + gap_hi/2 in
    lower_mid <= x <= upper_mid
    /\ (x = lower_mid \/ x = upper_mid  ==>  is_even)
```

(`is_even` = "r's significand is even", i.e. RNE's tie-break rule.)
This is a verbatim transcription of PR #10888's `nte_cond`.

The **old** (currently merged) encoding instead asserts:

```
exact_roundtrip(r, x) := (x = r.real)
```

## Mechanized result (`Z3FpaRoundingAudit.fst`)

Working in a small, self-contained exact-rational theory (`rat`, with
comparisons by cross-multiplication — no floating-point or real-number
axioms needed), the following are proved, with **no `admit`/`assume`**:

1. **`lemma_old_implies_new`** — `exact_roundtrip(r,x)` implies
   `round_nearest_even(r, gap_lo, gap_hi, is_even, x)` for any positive
   gaps. The old constraint's models are always valid rounding models
   (it was never *incorrect*, only *incomplete*).

2. **`lemma_new_not_implies_old`** — the converse fails: a concrete
   model (`r=0`, symmetric gap `2`, `x=1`, a tie broken by `is_even`)
   satisfies `round_nearest_even` but not `exact_roundtrip`. This is
   the mechanized witness that the old encoding is a **strict**,
   unsound restriction: there exist models of the true rounding
   relation that the old code's constraint rules out.

3. **`lemma_binade_carry_witness`** — the same strictness result,
   instantiated with the *literal* numbers from issue #10931
   (`(_ FloatingPoint 8 24)`, `r = 2.0`, `gap_lo = 2^-23`,
   `gap_hi = 2^-22`, `x = 2 - 2^-24`), confirming mechanically that the
   issue's claimed `sat` witness (`r ≈ 1.99999998` rounds to `2.0` under
   RNE) satisfies the correct rounding relation and is exactly the kind
   of model the old `exact_roundtrip` equality excludes (since
   `x ≠ r.real`), explaining the observed false `unsat`.

4. **`lemma_grs_satisfiable`** — PR #10938's alternative GRS bracketing
   (`grs_brackets`) is, in isolation, satisfiable for every `x` in a
   half-open grid interval (by choosing `sticky = (x ≠ grid_lo)`), the
   same completeness property as point 2 above, applied one layer
   earlier in the pipeline (to the pre-round significand/exponent
   rather than the final result).

**Conclusion: the existing (merged) encoding fails this correctness
condition — it is provably strictly incomplete (sound but not
complete) with respect to `round_nearest_even`. PR #10888's encoding
*is* `round_nearest_even`, transcribed directly, so it succeeds this
condition by construction, with the two theorems above as the formal
soundness/completeness argument.** PR #10938's `grs_brackets` layer
also succeeds this condition, but its overall correctness additionally
requires `round()`'s existing bit-precise renormalization to correctly
turn a GRS-bracketed intermediate value into the final nearest/tie/
overflow-adjusted result for every bit-vector instantiation — a
bit-precise circuit-correctness question this audit does not verify
(consistent with `unpack`/`round` being out of scope for the base FPA
audit; see [`FPA_REPORT.md`](FPA_REPORT.md)).

## Deeper layer: are the gap *formulas* themselves correct? (`Z3FpaRoundingBits.fst`)

`Z3FpaRoundingAudit.fst` treated `gap_lo`/`gap_hi` as *abstract* positive
rationals — it verified the logical schema (`exact_roundtrip` is
strictly weaker than `round_nearest_even`) but not PR #10888's actual
**formulas** for those gaps (`ulp = |r|/sig_value`, "the gap below a
power of two is half the gap above it", and the smallest-normal
exception). `Z3FpaRoundingBits.fst` closes that gap: it defines a
value semantics `val_of(cs, e, s) = s · 2^e / 2^cs` for a representable
magnitude at "format position" `(e, s)` (with `e = 1` uniformly
covering subnormals, zero, and the first normal binade — the single
modeling choice that makes the smallest-normal/largest-subnormal
boundary provably *not* special), and proves:

- **`lemma_gap_up_is_successor_distance`** — `gap_up(cs,e) = unit(cs,e)`
  is *exactly* `val_of(succ) - val_of(current)`, for every position
  (same-exponent step or binade-boundary step alike).
- **`lemma_gap_down_is_predecessor_distance`** — `gap_down(cs,sigbits,e,s)`
  is *exactly* `val_of(current) - val_of(pred)`, including at binade
  boundaries (where it is proved to equal `unit(cs,e)/2`, via
  `lemma_unit_doubles`: `unit` provably doubles with each exponent
  increment).
- **`lemma_smallest_normal_gap_not_halved`** — the smallest normal's gap
  to the largest subnormal is proved to equal the *unhalved* unit,
  confirming the code's explicit exception.

**A bug was caught and fixed during this derivation**: the first draft
of `gap_down` halved `unit(cs, e-1)` instead of `unit(cs, e)` — i.e. it
would have asserted a *predecessor* gap of `unit(cs,e)/4` relative to
the correct value, off by a factor of 2 — and F* correctly refused to
verify the successor/predecessor distance lemma until the definition
was corrected to match the algebra actually proved by
`lemma_succ_binade_boundary`/`lemma_unit_doubles`. This is a direct,
concrete illustration of the audit methodology catching an error before
it could be mistaken for a verified fact.

All lemmas in `Z3FpaRoundingBits.fst` are proved with no
`admit`/`assume`.

## What this audit does *not* establish

- A composed "capstone" theorem substituting the proved true
  predecessor/successor values directly into `round_nearest_even`'s
  midpoint formulas (i.e. restating `lower_mid`/`upper_mid` as
  `(pred+r)/2`/`(r+succ)/2` and re-deriving `round_nearest_even` from
  `round_nearest_true_neighbors`). The arithmetic identity is
  straightforward on paper (`r - gap_down/2 = r - (r-pred)/2 =
  (r+pred)/2`, using the distance lemmas above), but mechanizing it
  cleanly needs a handful of `rat_eq` congruence lemmas (`rat_eq`
  respects `rat_add`/`rat_sub`/`rat_half`) not yet added — a natural,
  bounded next step, not attempted here to avoid an open-ended
  nonlinear-arithmetic proof-engineering detour.
- That the directed-rounding (`RNA`/`RTP`/`RTN`/`RTZ`) and
  overflow-to-infinity/saturation branches of PR #10888 — only the
  nearest-even case was formalized here — correctly use these same
  gap values; by symmetry of construction they almost certainly do,
  but this was not separately checked.
- That either PR's C++ *implementation* is a byte-for-byte correct
  encoding of `round_nearest_even`/`grs_brackets` in SMT bit-vector
  arithmetic across every `(ebits, sbits)` combination, subnormal
  boundary, and directed-rounding mode — that would require extending
  `Z3FpaConverter.fst`'s bit-pattern theory to the `round()`/`unpack()`
  pipeline, explicitly flagged as a gap in `FPA_REPORT.md`.
- Any judgment on issues #10176/#9953/#8052/#7842/#7431 beyond noting
  their existence; they were not re-triaged in depth here.

