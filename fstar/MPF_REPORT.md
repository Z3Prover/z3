# F* Audit: `src/util/mpf.h` / `mpf.cpp` (arbitrary-precision MPF library)

## Scope

`mpf_manager` is Z3's arbitrary-precision IEEE-754 floating-point
library: it represents a float as `(sign : bool, significand : mpz,
exponent : int64)` with no fixed bit-width in storage, and implements
`set`/`add`/`sub`/`mul`/`div`/`fma`/`sqrt`/`round_to_integral`/`rem`
and the classification/conversion API declared in `mpf.h`. It is the
library that `fpa_rewriter.cpp`'s constant-folding paths delegate to
(excluded from [`Z3FpaRewrites.fst`](Z3FpaRewrites.fst)'s scope) and the semantic reference
that `fpa2bv_converter.cpp`'s bit-vector circuits (excluded from
[`Z3FpaConverter.fst`](Z3FpaConverter.fst)'s scope) are meant to compute.

Two theory/proof files are added:

| File | Contents |
|---|---|
| [`Z3MpfTheory.fst`](Z3MpfTheory.fst) | Exponent landmarks (`mk_bot_exp`/`mk_top_exp`/`mk_min_exp`/`mk_max_exp`, `bias_exp`/`unbias_exp`), classification predicates (`is_zero`/`is_denormal`/`is_normal`/`is_nan`/`is_inf`), and the rational value semantics of `to_rational`. |
| [`Z3MpfRound.fst`](Z3MpfRound.fst) | The rounding-*decision* logic inside `mpf_manager::round` (mpf.cpp:2055-2061), proved correct against an independent IEEE-754 ground truth, for all five rounding modes. |
| [`Z3MpfExact.fst`](Z3MpfExact.fst) | **End-to-end extension**: proves the "truncate an unbounded-precision intermediate value down to a fixed width, keeping a single sticky bit" technique used throughout `add_sub`/`mul`/`div`/`round` loses *no* rounding-relevant information, and composes this with [`Z3MpfRound.fst`](Z3MpfRound.fst)'s decision-table theorem into one capstone theorem covering the whole truncate-then-round pipeline, not just the final 3-bit decision in isolation. |

## Function-by-function coverage

| mpf.cpp function | Lines | Status |
|---|---|---|
| `mk_bot_exp`/`mk_top_exp`/`mk_min_exp`/`mk_max_exp` | 1839-1858 | **Proved**: transcribed exactly; `lemma_exp_landmarks_ordered` proves `bot < min <= max < top`. |
| `bias_exp`/`unbias_exp` | 1860-1865 | **Proved** mutually inverse (`lemma_bias_unbias_inverse`, `lemma_unbias_bias_inverse`); the arbitrary-precision analogue of the bit-vector bias/unbias lemmas already proved in [`Z3FpaConverter.fst`](Z3FpaConverter.fst). |
| `is_zero`, `is_denormal`, `is_normal`, `is_nan`, `is_inf` | 389-391, 1781-1803 | **Proved**: transcribed exactly; `lemma_classification_exhaustive_disjoint` proves the five categories exhaustively and disjointly partition every representable `(exponent, significand)` pair. |
| `to_rational` | 1705-1719 | **Proved**: `mpf_to_rational` transcribes both case-split branches (`exponent >= 0` vs `< 0`); `lemma_to_rational_matches_val_of` proves both branches compute the *same* value, and that this value coincides with the `val_of` ground truth independently introduced in [`Z3FpaRoundingBits.fst`](Z3FpaRoundingBits.fst) — closing the loop between that abstraction and the real library code. |
| `round` — GRS decision table | 2055-2061 | **Proved** ([`Z3MpfRound.fst`](Z3MpfRound.fst), see below): the literal switch statement is IEEE-754 correct for `RNE`/`RNA`/`RTP`/`RTN`/`RTZ`, given what `last`/`round`/`sticky` are specified to mean. This also closes the "directed-rounding modes not separately checked" gap noted in `FPA_ROUNDING_AUDIT.md`, now at the level of the real code rather than the PR's abstract schema. |
| Truncate-with-sticky-bit (`add_sub` mpf.cpp:481-483/568-569/656-657, `mul` 650-654, `div` 697-699, `round`'s own internal shift 2040-2045) | see cites | **Proved** ([`Z3MpfExact.fst`](Z3MpfExact.fst)): the shared "divide by `2^n`, fold any nonzero remainder into the kept quotient's LSB (only when it is even, so no carry ever propagates beyond bit 0)" pattern is exact for rounding purposes — it preserves `round`/`last` and correctly ORs the lost remainder's nonzero-ness into `sticky`, for *any* truncation width and *any* number of composed truncations (`lemma_fold_compose`). Composed with the GRS decision-table theorem above into one **capstone theorem** (`lemma_end_to_end_round_correct`): the full truncate-then-round pipeline computes the IEEE-754-correct rounding decision for the true, never-materialized, full-precision discarded fraction — not merely for whatever coarser value survived truncation. |
| `round` — shift-distance/LZ computation (`sigma`, `prev_power_of_two`) | 1992-2037, 2141+ | **Not proved** — bit-shifting mechanics that determine the truncation width `n` and *which* integer ends up as `kept_int` (i.e. the numeric argument for the capstone theorem above); the capstone theorem is agnostic to how `n`/`kept_int` were chosen, but does not itself establish that this particular choice is the one IEEE-754 requires (e.g. correctly handling exponent-range clamping for subnormal/overflow cases). |
| `round` — post-normalization carry (`sig >= 2^sbits` → shift+exponent++) | 2066-2072 | **Not reproved here** — this is the same arithmetic fact as `lemma_succ_binade_boundary` in [`Z3FpaRoundingBits.fst`](Z3FpaRoundingBits.fst) (incrementing a full significand overflows into the next binade); the connection is noted but not re-derived in this file. |
| `round` — overflow-to-infinity (`mk_round_inf`) | 1958-1968, 2074-2093 | **Not proved** — directed-rounding saturation behavior at the top of the exponent range. |
| `unpack` | 1932-1955 | **Not proved** — the hidden-bit insertion (normal case) is a one-line fact (`add 2^(sbits-1)`), but the subnormal renormalization loop (shifting until the significand reaches full width, decrementing the exponent each step) is iterative bit-shifting mechanics, same category as the `round` shift distance above. |
| `mul` — exact pre-round product | 586-654 | **Proved** ([`Z3MpfExact.fst`](Z3MpfExact.fst), `lemma_mul_round_correct`): the arbitrary-precision integer product of two unpacked significands loses no information at all before the single deliberate truncation at mpf.cpp:650-654 — so `mul`'s only information loss is exactly one instance of the already-proved truncate-with-sticky-bit pattern, and the capstone theorem applies directly to the *exact* mathematical product. |
| `add_sub` — alignment-shift-then-add strategy | 475-575 | **Proved exact** ([`Z3MpfExact.fst`](Z3MpfExact.fst), `lemma_add_commutes_with_truncation`): the code shifts *one* operand then adds the other and folds the sticky bit into the *sum*, rather than the conceptually simpler "shift, fold, then add"; this lemma proves the two strategies are equivalent (the remainder of `m*2^n + t` by `2^n` does not depend on `m`), so `add_sub`'s specific implementation order introduces no extra error beyond the one truncation already covered by the capstone theorem. |
| `div`, `fma`, `sqrt`, `round_to_integral`, `rem`/`partial_remainder`, `renormalize` | 664-1690, 1269-1452 | **Not proved** — `div`'s quotient computation (mpf.cpp:694-696) is itself a truncating division with *no* remainder tracked at that step (only the second, explicit truncation at 697-699 keeps a sticky bit); this likely composes with the already-proved machinery via the same nested-floor-division reasoning as `lemma_add_commutes_with_truncation`, but that composition was not carried out here. `fma`/`sqrt`/`round_to_integral`/`rem` were read but not formalized. |

## Notable result: the `round()` decision-table theorem

[`Z3MpfRound.fst`](Z3MpfRound.fst) formalizes, independently of the bit-shifting code,
what `last`/`round`/`sticky` are specified to mean: after discarding
the bottom 3 bits, the true (infinite-precision) value is
`kept_int + frac` with `0 <= frac < 1`, where

```
last   = parity of kept_int        (true <=> kept_int is odd)
round  = true <=> frac >= 1/2
sticky = true <=> frac is not a multiple of 1/2 (i.e. strictly between 0 and 1/2, or strictly between 1/2 and 1)
```

`mpf_round_inc` transcribes the code's switch statement verbatim:

```
RNE -> round && (last || sticky)
RNA -> round
RTP -> (not sign) && (round || sticky)
RTN -> sign && (round || sticky)
RTZ -> false
```

`correct_inc` is an independent ground truth written directly from the
IEEE-754 definitions (round-to-nearest ties-to-even/ties-away, and the
three directed modes), with no reference to the bit formula above.
`lemma_round_decision_correct` proves `mpf_round_inc rm sign last
(round_bit frac) (sticky_bit frac) = correct_inc rm sign last frac`
for every rounding mode, sign, parity, and `frac` in `[0,1)` — i.e. the
compact bit formula used in production code is exactly the textbook
correctly-rounded decision, for all five modes, not just nearest-even.
Seven corollaries spot-check concrete readings (tie-to-even on
odd/even kept values, ties-always-away for RNA, RTZ's unconditional
truncation, RTP's sign-dependent ceiling behavior).

All lemmas in both files are proved with no `admit`/`assume`.

## Notable result: the end-to-end capstone theorem ([`Z3MpfExact.fst`](Z3MpfExact.fst))

The decision-table theorem above is conditional on `last`/`round`/
`sticky` correctly reflecting the *true, full-precision* discarded
fraction. But every mpf.cpp operation only ever has a *truncated*
approximation of that fraction available — `add_sub`, `mul`, `div`,
and `round`'s own internal denormal shift all, at some point, compute
`q = N / 2^n` (floor division, discarding `n` bits) and then run:

```cpp
if (!sticky_rem.is_zero() && is_even(q)) inc(q);
```

[`Z3MpfExact.fst`](Z3MpfExact.fst) proves this one-bit "sticky fold" is *exact* for
rounding purposes:

- **`lemma_fold_preserves_div2`**: the increment only ever fires when
  `q` is even (LSB 0), so it can never carry past bit 0 — `q`'s bits
  above position 0 are untouched.
- **`lemma_fold_preserves_grs`**: consequently, folding leaves `round`
  and `last` (which read bits 2 and 3) exactly unchanged, and sets
  `sticky` (which reads bits 0-1) to exactly `sticky_of(q) ||
  r_nonzero` — i.e. it correctly ORs in the lost remainder's
  nonzero-ness, fabricating nothing and losing nothing that the
  downstream decision needs.
- **`lemma_fold_compose`**: folding twice (e.g. once in `add_sub`'s
  alignment shift, again inside `round`'s own internal shift) is
  equivalent to a single fold with the combined remainder-nonzero
  flag — so the theorem composes across every truncation point in a
  pipeline, not just one.
- **`lemma_add_commutes_with_truncation`**: `add_sub`'s specific
  strategy of shifting one operand and folding the sticky bit into the
  *sum* (rather than folding the shifted operand first, then adding)
  is proved equivalent to the simpler strategy, since the remainder of
  `m*2^n + t` by `2^n` does not depend on `m`.
- **`lemma_end_to_end_round_correct`** (the capstone): bridges the
  integer-level `round_of`/`sticky_of` to [`Z3MpfRound.fst`](Z3MpfRound.fst)'s
  rational-level `round_bit`/`sticky_bit`, and composes everything
  into one theorem: for *any* true discarded fraction consistent with
  having been truncated to `q` with remainder-nonzero flag
  `r_nonzero`, the code's actual computation — fold, extract GRS,
  apply `mpf_round_inc` — produces exactly the IEEE-754-correct
  decision for that true fraction, regardless of how much precision
  was truncated away or how many times.
- **`lemma_mul_round_correct`**: instantiates the capstone for `mul`
  specifically, using that an exact arbitrary-precision integer
  product loses no information at all before the single deliberate
  truncation at mpf.cpp:650-654 — so `mul`'s rounding decision is
  proved IEEE-754-correct for the *exact* mathematical product of its
  operands, not merely for a truncated approximation of it.

All lemmas in [`Z3MpfExact.fst`](Z3MpfExact.fst) are proved with no `admit`/`assume`.

## What this audit does *not* establish

- **The shift-distance/leading-zero-counting code** (mpf.cpp:1992-2037,
  2141+) that *chooses* the truncation width `n` and produces the
  `(q, r)` pair the capstone theorem is instantiated with. The
  capstone theorem is agnostic to how `n`/`q` were chosen — it holds
  for *any* valid `(q, r)` decomposition — but does not itself verify
  that mpf.cpp's specific choice of `n` is the one IEEE-754 requires
  (e.g. correctly handling exponent-range clamping for subnormal and
  overflow cases). This remains the single largest unformalized piece
  of the rounding pipeline.
- **`unpack`'s subnormal renormalization loop**, **post-normalization
  carry**, and **`mk_round_inf` saturation** — not reproved, though the
  first two are straightforward extensions of facts already proved
  elsewhere in this audit series ([`Z3FpaConverter.fst`](Z3FpaConverter.fst)'s bias/unbias
  lemmas; [`Z3FpaRoundingBits.fst`](Z3FpaRoundingBits.fst)'s binade-boundary lemma).
- **`div`'s own composition with the capstone.** `div`'s quotient
  computation (mpf.cpp:694-696) is itself a truncating division with
  *no* remainder tracked at that step; only the second, explicit
  truncation at 697-699 keeps a sticky bit. This almost certainly
  composes correctly via the same nested-floor-division reasoning as
  `lemma_add_commutes_with_truncation`/`lemma_fold_compose`, but that
  specific composition was not carried out here.
- **`fma`/`sqrt`/`round_to_integral`/`rem`/`partial_remainder`/
  `renormalize`** — read but not formalized at all.
- **`to_double`/`to_float`** (raw IEEE bit-pattern packing,
  mpf.cpp:1723-1777) and **`to_sbv_mpq`/`to_ieee_bv_mpz`** — not
  examined.

See [`REPORT.md`](REPORT.md) for the index of all audits in this
series, and [`FPA_ROUNDING_AUDIT.md`](FPA_ROUNDING_AUDIT.md) for the
earlier, narrower audit of the `fpa2bv_converter.cpp` rounding
encoding that this one both reuses (`val_of`) and extends (directed
rounding modes).

