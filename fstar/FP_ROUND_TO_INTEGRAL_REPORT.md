# GitHub issue #11139: `fp.roundToIntegral` mis-rounds tiny-exponent-width subnormals

## Issue

[Z3Prover/z3#11139](https://github.com/Z3Prover/z3/issues/11139) reports
that `(fp.roundToIntegral RNE (fp #b0 #b00 #b01))` on the custom sort
`(_ FloatingPoint 2 3)` — the subnormal value exactly `1/4` — rounds to
`+1` instead of the correct nearest value `+0`, in both `RNE` and `RNA`
modes, and that a `check-sat` requiring the correct `+0` result returns
`unsat` instead of `sat`. The issue's own "Source diagnosis" names two
suspects: `mpf_manager::round_to_integral` (`src/util/mpf.cpp`) and
`fpa2bv_converter::mk_round_to_integral`
(`src/ast/fpa/fpa2bv_converter.cpp`). The "Scope" section observes that
standard formats (float16/32/64/128) are unaffected; only tiny custom
formats with `ebits = 2` (FP(2,3), FP(2,5), FP(2,9)) exhibit the bug.

## Reproduction

Built the prebuilt `z3-4.13.3` binary against the issue's exact
reproducer: confirmed `(fp #b0 #b01 #b00)` (i.e. `+1`) is produced
instead of `(fp #b0 #b00 #b00)` (`+0`), and `check-sat` returns `unsat`
instead of the expected `sat`. **The bug is real, not filed in error.**

## Root cause

Z3 stores an `mpf` value as `(sign, exponent, significand)`, where
`exponent` is the *stored, unbiased* exponent and `significand` is the
**raw fraction bits only** — no hidden/implicit leading-1 bit is
inserted for either normal or denormal numbers as stored. The hidden
bit is inserted only on demand by `unpack()`, which also *renormalizes*
denormals (shifting the raw fraction left, decrementing a scratch
exponent each step) so that the result looks exactly like a normal
number's `(exponent, significand)` pair.

`round_to_integral`'s nearest-mode branch (and `mk_round_to_integral`'s
`t2`/`c423` bit-vector tests) decide whether a magnitude in `[0,1)`
rounds to `0` or `1` by comparing the **stored** exponent field
directly against the literal `-1` (tie) and `< -1` (definitely below
half) — valid *only* for normal numbers, where `exponent = -1` can only
mean "magnitude in `[0.5,1)`, hidden bit present". For **denormals**,
every value of a given format shares the same stored sentinel exponent
`mk_bot_exp(ebits)` regardless of true magnitude. For `ebits = 2`,
`mk_bot_exp(2) = -1` — this sentinel collides exactly with the
hardcoded tie-test constant, so every nonzero-significand denormal of a
2-exponent-bit format is misrouted into the "round up to 1" branch
regardless of its true magnitude (e.g. `1/4`, which should round to
`0`). For `ebits >= 3`, `mk_bot_exp(ebits) <= -2 < -1`, so the
(unmodified) `< -1` test always fires and happens to produce the right
answer anyway (every such denormal truly is `< 1/2`) — exactly matching
the issue's reported scope.

Both cited code paths have this same bug, independently:

- `mpf.cpp`'s `round_to_integral` nearest-mode branch (`MPF_ROUND_NEAREST_TEVEN`/`MPF_ROUND_NEAREST_TAWAY`) tested `x.exponent`/`x.significand` directly.
- `fpa2bv_converter.cpp`'s `mk_round_to_integral` computed `a_exp`/`a_lz` via `unpack(..., true)` but — unlike *every other* unary/binary FP operation in the file (`add`, `mul`, `div`, `sqrt`, etc., which all compute `real_exp = a_exp - a_lz` before any magnitude comparison) — never subtracted `a_lz`, comparing raw `a_exp` directly.

## Fix

Both sites now renormalize before comparing:

- **`src/util/mpf.cpp`** (`round_to_integral`, nearest-mode branch): when `is_denormal(x)`, renormalize a scratch `(exponent, significand)` pair via the already-tested `mpf_manager::renormalize()` helper (the same routine `unpack()` itself uses), strip the reinserted hidden bit back out, and use the renormalized `(eff_exponent, eff_significand)` in the tie/below-half tests instead of the raw `x.exponent`/`x.significand`.
- **`src/ast/fpa/fpa2bv_converter.cpp`** (`mk_round_to_integral`): compute `real_exp = sign_extend(1, a_exp) - zero_extend(1, a_lz)` (the same idiom used by `sqrt` et al.) and compare `real_exp` against the (now `ebits+1`-bit-widened) tie/below-half constants, instead of raw `a_exp`.

### Validation against the repro

Built Z3 (Release, Ninja) with both fixes and re-ran the issue's exact
reproducer:

| | constant-folding (`simplify`) | default `check-sat` | `check-sat-using (then fpa2bv smt)` |
|---|---|---|---|
| Before fix | `(fp #b0 #b01 #b00)` (wrong, `+1`) | `unsat` (wrong) | `unsat` (wrong) |
| After fix | `(_ +zero 2 3)` (correct) | `sat` (correct) | `sat` (correct) |

### Regression check

Re-ran `round_to_integral` on standard formats and additional FP(2,3)
cases through both the default solver and
`check-sat-using (then fpa2bv smt)`:

- float16 `1.5 -> 2`, `2.5 -> 2` (tie-to-even), `0.25 -> 0`: unchanged, correct.
- double `0.5 -> +0`, `-0.5 -> -0` (tie-to-even): unchanged, correct.
- FP(2,3) `0.5` (a genuine tie, stored fraction `#b10`) now correctly rounds to `+0` (tie-to-even; it used to also round to `+1` under the old bug, for a different reason — see `lemma_old_decision_wrong_on_true_tie` below).
- FP(2,3) `0.75` (stored fraction `#b11`) still correctly rounds to `+1` (this case happened to be correct even under the old buggy code, since "round up" was the right answer there too).

Unit tests `test-z3 mpf` and `test-z3 fpa` both still `PASS`.

## F* formalization

[`Z3MpfRoundToIntegral.fst`](Z3MpfRoundToIntegral.fst) formalizes the
nearest-mode round-to-integral decision for denormals abstractly (no
bit-vector/mpz details — consistent with the rest of this audit series)
and proves, fully mechanically (no `admit`/`assume`):

- **`lemma_old_decision_wrong_11139`**: the OLD (pre-fix) decision procedure is *wrong* for the issue's exact witness (FP(2,3), stored fraction 1, true value `1/4`), for both `RNE`/`NTE` and `RNA`/`NTA` — a mechanized confirmation that the issue is a real bug.
- **`lemma_old_decision_wrong_on_true_tie`**: a second, independent witness — the OLD code *also* mishandles the actual tie case (stored fraction 2, true value exactly `1/2`) under `RNE`, because its tie test required the stored fraction to be `0` (valid only for normals), not recognizing the denormal encoding of an exact tie.
- **`lemma_old_decision_correct_for_ebits_ge_3`**: the OLD decision procedure is nonetheless *always* correct once `ebits >= 3`, because `mk_bot_exp(ebits) <= -2` then, so every denormal of such a format is unconditionally `< 1/2` — explaining the issue's own reported "Scope" from first principles, not just by enumeration.
- **`lemma_new_decision_correct`**: the NEW (fixed), renormalized decision procedure is correct for **every** denormal of **every** format (`ebits >= 2`, `sbits >= 2`), not just `ebits >= 3` — closing exactly the gap the old procedure had for `ebits = 2`.
- **`lemma_fix_closes_11139`**: the concrete corollary that the fix is correct on the issue's own witness (`FP(2,3)`, stored fraction `1`, renormalizing to `eff_exponent = -2`, `eff_fraction = 0`), matching the fixed `z3.exe`'s observed `(_ +zero 2 3)` output.

The ground truth these are checked against (`correct_round_up`) is not
a copy of either the old or new code — it is `Z3MpfRound.fst`'s
already-proved `correct_inc`, the independent IEEE-754 rounding-decision
theorem from this audit series's earlier MPF work, applied to the
denormal's *exact* rational value. This connects the bug/fix to
pre-existing, independently-verified ground truth rather than to a
freshly-invented one.

## Scope notes

As with the rest of this audit series, the renormalization *shift
amount* itself (how many bit positions a given raw fraction must be
shifted to reach the hidden-bit position) is treated as bit-shifting
mechanics and specified declaratively (`is_renormalized_of`'s defining
equation `frac * 2^shift = eff_frac + 2^(sbits-1)`) rather than
re-proving the shift loop — consistent with how the `mpf.cpp` fix
itself reuses the already-tested `renormalize()` helper instead of
re-deriving it, and how `MPF_REPORT.md` already treats `unpack`'s
shift loop as out of scope for the same reason. Directed rounding modes
(`RTP`/`RTN`/`RTZ`) are out of scope here, since they are dispatched to
entirely different code paths in both `round_to_integral` and
`mk_round_to_integral`, untouched by this bug or fix.
