# F* Audit: `src/util/mpf.h` / `mpf.cpp` (arbitrary-precision MPF library)

## Scope

`mpf_manager` is Z3's arbitrary-precision IEEE-754 floating-point
library: it represents a float as `(sign : bool, significand : mpz,
exponent : int64)` with no fixed bit-width in storage, and implements
`set`/`add`/`sub`/`mul`/`div`/`fma`/`sqrt`/`round_to_integral`/`rem`
and the classification/conversion API declared in `mpf.h`. It is the
library that `fpa_rewriter.cpp`'s constant-folding paths delegate to
(excluded from `Z3FpaRewrites.fst`'s scope) and the semantic reference
that `fpa2bv_converter.cpp`'s bit-vector circuits (excluded from
`Z3FpaConverter.fst`'s scope) are meant to compute.

Two theory/proof files are added:

| File | Contents |
|---|---|
| `Z3MpfTheory.fst` | Exponent landmarks (`mk_bot_exp`/`mk_top_exp`/`mk_min_exp`/`mk_max_exp`, `bias_exp`/`unbias_exp`), classification predicates (`is_zero`/`is_denormal`/`is_normal`/`is_nan`/`is_inf`), and the rational value semantics of `to_rational`. |
| `Z3MpfRound.fst` | The rounding-*decision* logic inside `mpf_manager::round` (mpf.cpp:2055-2061), proved correct against an independent IEEE-754 ground truth, for all five rounding modes. |

## Function-by-function coverage

| mpf.cpp function | Lines | Status |
|---|---|---|
| `mk_bot_exp`/`mk_top_exp`/`mk_min_exp`/`mk_max_exp` | 1839-1858 | **Proved**: transcribed exactly; `lemma_exp_landmarks_ordered` proves `bot < min <= max < top`. |
| `bias_exp`/`unbias_exp` | 1860-1865 | **Proved** mutually inverse (`lemma_bias_unbias_inverse`, `lemma_unbias_bias_inverse`); the arbitrary-precision analogue of the bit-vector bias/unbias lemmas already proved in `Z3FpaConverter.fst`. |
| `is_zero`, `is_denormal`, `is_normal`, `is_nan`, `is_inf` | 389-391, 1781-1803 | **Proved**: transcribed exactly; `lemma_classification_exhaustive_disjoint` proves the five categories exhaustively and disjointly partition every representable `(exponent, significand)` pair. |
| `to_rational` | 1705-1719 | **Proved**: `mpf_to_rational` transcribes both case-split branches (`exponent >= 0` vs `< 0`); `lemma_to_rational_matches_val_of` proves both branches compute the *same* value, and that this value coincides with the `val_of` ground truth independently introduced in `Z3FpaRoundingBits.fst` — closing the loop between that abstraction and the real library code. |
| `round` — GRS decision table | 2055-2061 | **Proved** (`Z3MpfRound.fst`, see below): the literal switch statement is IEEE-754 correct for `RNE`/`RNA`/`RTP`/`RTN`/`RTZ`, given what `last`/`round`/`sticky` are specified to mean. This also closes the "directed-rounding modes not separately checked" gap noted in `FPA_ROUNDING_AUDIT.md`, now at the level of the real code rather than the PR's abstract schema. |
| `round` — shift-distance/LZ computation (`sigma`, `prev_power_of_two`) | 1992-2037, 2141+ | **Not proved** — bit-shifting mechanics that determine *which* integer is `kept_int` and its true discarded remainder; this is the part that would need to be connected to `round_bit`/`sticky_bit`'s specification to get an end-to-end result. |
| `round` — post-normalization carry (`sig >= 2^sbits` → shift+exponent++) | 2066-2072 | **Not reproved here** — this is the same arithmetic fact as `lemma_succ_binade_boundary` in `Z3FpaRoundingBits.fst` (incrementing a full significand overflows into the next binade); the connection is noted but not re-derived in this file. |
| `round` — overflow-to-infinity (`mk_round_inf`) | 1958-1968, 2074-2093 | **Not proved** — directed-rounding saturation behavior at the top of the exponent range. |
| `unpack` | 1932-1955 | **Not proved** — the hidden-bit insertion (normal case) is a one-line fact (`add 2^(sbits-1)`), but the subnormal renormalization loop (shifting until the significand reaches full width, decrementing the exponent each step) is iterative bit-shifting mechanics, same category as the `round` shift distance above. |
| `add_sub`, `mul`, `div`, `fma`, `sqrt`, `round_to_integral`, `rem`/`partial_remainder`, `renormalize` | 475-1690, 1269-1452 | **Not proved** — full arithmetic pipelines (exponent alignment, significand add/multiply/divide, cancellation, extended-precision GRS production) built on top of `round`. Each ultimately reduces to (a) producing a correct extended significand (out of scope, as above) and (b) calling `round`, whose decision logic *is* now proved correct. |

## Notable result: the `round()` decision-table theorem

`Z3MpfRound.fst` formalizes, independently of the bit-shifting code,
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

## What this audit does *not* establish

- **End-to-end correctness of any arithmetic operation.** The theorem
  above is conditional on `last`/`round`/`sticky` correctly reflecting
  the true discarded fraction — i.e. on the shift-distance/LZ-counting
  code (mpf.cpp:1992-2037) being correct. That code was read but not
  formalized; it is genuinely harder (unbounded-precision integer
  shifts parameterized by a computed leading-zero count) and is left
  as the natural next step for anyone extending this audit.
- **`unpack`'s subnormal renormalization loop**, **post-normalization
  carry**, and **`mk_round_inf` saturation** — noted above as
  not-reproved, though the first two are straightforward extensions of
  facts already proved elsewhere in this audit series
  (`Z3FpaConverter.fst`'s bias/unbias lemmas; `Z3FpaRoundingBits.fst`'s
  binade-boundary lemma).
- **`add_sub`/`mul`/`div`/`fma`/`sqrt`/`round_to_integral`/`rem`'s own
  arithmetic** (exponent alignment, cancellation, extended-precision
  product/quotient construction) — each op's correctness would reduce
  to "produces a GRS-correct extended significand, then calls `round`,
  which is now proved correct downstream of that input." Only the
  second half of that conjunction is established here.
- **`to_double`/`to_float`** (raw IEEE bit-pattern packing,
  mpf.cpp:1723-1777) and **`to_sbv_mpq`/`to_ieee_bv_mpz`** — not
  examined.

See [`REPORT.md`](REPORT.md) for the index of all audits in this
series, and [`FPA_ROUNDING_AUDIT.md`](FPA_ROUNDING_AUDIT.md) for the
earlier, narrower audit of the `fpa2bv_converter.cpp` rounding
encoding that this one both reuses (`val_of`) and extends (directed
rounding modes).
