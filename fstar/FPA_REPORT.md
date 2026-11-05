# F* Formalization of Z3's FPA Rewriter/Converter — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series; see [`SEQ_REWRITER_REPORT.md`](SEQ_REWRITER_REPORT.md)
for the companion sequence-theory audit this one is modeled on; see
[`FPA_ROUNDING_AUDIT.md`](FPA_ROUNDING_AUDIT.md) for a follow-up audit
of the `to_fp`-from-Real rounding encoding against currently open
issues/PRs (#10881/#10931, #10888/#10938).

This report accompanies:

- [`Z3FpaTheory.fst`](Z3FpaTheory.fst) — value-level axiomatization of IEEE-754 special
  values (NaN / signed Infinity / signed Zero / opaque finite payload).
- [`Z3FpaRewrites.fst`](Z3FpaRewrites.fst) — proofs of the symbolic rewrite rules of
  `src/ast/rewriter/fpa_rewriter.cpp` against that theory.
- [`Z3FpaConverter.fst`](Z3FpaConverter.fst) — bit-pattern-level axiomatization and proofs
  for the classification logic and the bias/unbias exponent encoding
  of `src/ast/fpa/fpa2bv_converter.cpp`.

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend (F* pins an exact Z3
version; this is independent of the Z3 binary built from this
repository). All three files type-check and discharge all
verification conditions with no `admit`/`assume`:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3FpaTheory.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3FpaRewrites.fst
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3FpaConverter.fst
```

## Scope

Unlike `seq_rewriter.cpp` (whose "hard part" is the regex/automata
engine), `fpa_rewriter.cpp`'s and `fpa2bv_converter.cpp`'s hard part is
**bit-precise rounding arithmetic**: `mk_add`/`mk_sub`/`mk_mul`/
`mk_div`/`mk_rem`/`mk_sqrt`/`mk_fma`/`mk_round_to_integral` either (a)
constant-fold via Z3's `mpf` arbitrary-precision float library when
both operands are concrete numerals, or (b) compile down to bit-vector
rounding *circuits* (`unpack`/`round` and friends) in the converter.
Neither of these is modeled here — doing so faithfully would mean
re-verifying a significant fraction of an IEEE-754 rounding
implementation, which is its own (large) project, exactly analogous to
how the seq audit excluded Brzozowski-derivative regex automata.

**In scope** (the genuinely *symbolic*, non-constant-folding content):

- `fpa_rewriter.cpp`: NaN/Infinity propagation and absorption in
  `neg`, `sub = add∘neg`, `abs(nan)=nan`, `min`/`max` NaN-absorption,
  the full NaN/Infinity case split in `lt`, the `gt = flip(lt)` /
  `ge = flip(le)` definitional identities, the NaN case in `le`, and
  the `eq_core` (SMT `=`) vs. `float_eq` (IEEE `fp.eq`) semantic
  contrast — in particular their disagreement on NaN-reflexivity and
  (oppositely) on signed-zero equality.
- `fpa2bv_converter.cpp`: the ten classification predicates
  (`mk_is_nan/is_inf/is_pinf/is_ninf/is_pos/is_neg/is_zero/is_nzero/
  is_pzero/is_denormal/is_normal`), which are pure combinatorial
  functions of the `(sign, exponent, significand)` bit-pattern triple
  with no rounding involved, plus their disjointness/exhaustiveness
  structure; and the `mk_bias`/`mk_unbias` exponent-encoding round
  trip, a self-contained modular-arithmetic bit trick.

**Out of scope** (not modeled, not proved):

- All constant-folding arithmetic paths in `fpa_rewriter.cpp`
  (anything gated on `m_util.is_numeral(...)`), since they delegate to
  `mpf_manager`'s bit-precise arithmetic, not a symbolic rewrite rule.
- `mk_fp`, `mk_to_fp`, `mk_to_fp_unsigned`, `mk_to_bv*`, `mk_to_real`,
  `mk_bv2rm`, `mk_bvwrap` — term constructors / bit-level (de)coding
  tables, not equality-preserving rewrites in the sense formalized
  here.
- The `to_fp(rm, to_real(int))` overflow-detection special case in
  `mk_is_normal`/`mk_is_subnormal` at the `fpa_rewriter.cpp` (value)
  level, which needs bit-precise exponent-overflow magnitude
  reasoning (`mk_is_inf_of_int`); we still define `is_normal`/
  `is_subnormal` at the value level (parametrized by an abstract
  magnitude classifier) purely so the classification-exhaustiveness
  sanity lemma can be stated uniformly, but we do not attempt this
  rewrite rule itself.
- `mk_leading_zeros` (a recursive divide-and-conquer bit-counting
  circuit) in `fpa2bv_converter.cpp` — judged too complex / out of
  scope, the FPA analogue of excluding regex derivatives.
- `unpack` / `round` and the entire arithmetic pipeline
  (`mk_add`/`mk_mul`/`mk_div`/`mk_sqrt`/`mk_fma`/`mk_round_to_integral`/
  `mk_float_lt`/`gt`/`le`/`ge` at the bit-vector level) in
  `fpa2bv_converter.cpp`.
- `mk_min_exp`/`mk_max_exp` — simple numeral constructors, not rewrite
  rules; not separately proved (they don't participate in the
  bias/unbias round trip).

## Coverage: `fpa_rewriter.cpp`

| Function | Lines | Lemma(s) in [`Z3FpaRewrites.fst`](Z3FpaRewrites.fst) | Gaps / not proved |
|---|---|---|---|
| `mk_add` | 265-285 | — | bit-precise rounding / constant folding (out of scope) |
| `mk_sub` | 286-292 | `lemma_sub_is_add_neg` (`a - b = a + (-b)`, `add` abstract) | — |
| `mk_mul`, `mk_div`, `mk_rem`, `mk_fma`, `mk_sqrt`, `mk_round_to_integral` | 292-355, 432-540 | — | bit-precise rounding / constant folding (out of scope) |
| `mk_neg` | 323-355 | `lemma_neg_nan`, `lemma_neg_pinf`, `lemma_neg_ninf`, `lemma_neg_neg` | constant-numeral negation (out of scope) |
| `mk_abs` | 368-384 | `lemma_abs_nan` | constant-numeral / sign-bit-clear case (out of scope) |
| `mk_min` | 384-408 | `lemma_min_nan_left`, `lemma_min_nan_right` | the non-NaN base case (signed-zero tie-break, genuinely left unrewritten — `base` kept abstract) |
| `mk_max` | 408-432 | `lemma_max_nan_left`, `lemma_max_nan_right` | same as `mk_min` |
| `mk_float_eq` | 557-578 | `lemma_float_eq_nan_irreflexive`, `lemma_float_eq_signed_zero`, `lemma_float_eq_refl_non_nan` | — |
| `mk_lt` | 578-619 | `lemma_lt_nan`, `lemma_lt_ninf_left`, `lemma_lt_ninf_right`, `lemma_lt_pinf_left`, `lemma_lt_pinf_right` | the finite-vs-finite numeral comparison itself (modeled abstractly via `val_of`, not Z3's `mpf` comparison) |
| `mk_gt` | 619-624 | `lemma_gt_is_flipped_lt` | — |
| `mk_le` | 624-639 | `lemma_le_nan` | `le`'s non-NaN cases are not individually broken out by the code (only `lt`/`gt` have explicit infinity branches); our `le` definition is total but only the NaN rule is claimed as "proved against the code" |
| `mk_ge` | 639-644 | `lemma_ge_is_flipped_le` | — |
| `mk_is_zero`/`is_nzero`/`is_pzero` | 644-677 | (not separately proved at the value level: these are definitional unfoldings of `is_zero`/`is_pzero`/`is_nzero` in [`Z3FpaTheory.fst`](Z3FpaTheory.fst), matching the code 1:1) | — |
| `mk_is_nan` | 677-712 | (definitional, as above) | — |
| `mk_is_inf` | 712-767 | (definitional, as above) | — |
| `mk_is_normal` / `mk_is_subnormal` | 767-833 | `lemma_classes_exhaustive`, `lemma_classes_disjoint` (parametrized by abstract magnitude classifier) | the `to_fp(rm, to_real(int))` overflow special case (needs bit-precise reasoning, out of scope) |
| `mk_is_negative` / `mk_is_positive` | 833-857 | `lemma_is_positive_def`, `lemma_pos_neg_exclusive` | — |
| `mk_eq_core` | 857-872 | `lemma_eq_core_refl`, `lemma_eq_core_sym`, `lemma_eq_core_trans`, `lemma_eq_core_signed_zero`, `lemma_float_eq_eq_core_agree` | — |
| `mk_bv2rm`, `mk_fp`, `mk_to_bv*`, `mk_to_real`, `mk_bvwrap`, `mk_to_fp*` | 110-264, 872-1135 | — | term constructors / bit-decoding (out of scope) |

## Coverage: `fpa2bv_converter.cpp`

| Function | Lines | Lemma(s) in [`Z3FpaConverter.fst`](Z3FpaConverter.fst) | Gaps / not proved |
|---|---|---|---|
| `mk_is_nan` | 3760-3772 | (definitional: `is_nan`) + `lemma_classes_exhaustive`/`disjoint` | — |
| `mk_is_inf` | 3775-3786 | (definitional: `is_inf`) | — |
| `mk_is_pinf` / `mk_is_ninf` | 3786-3799 | `lemma_inf_sign_partition` | — |
| `mk_is_pos` / `mk_is_neg` | 3800-3818 | `lemma_pos_neg_exclusive` | — |
| `mk_is_zero` | 3818-3829 | (definitional: `is_zero`) | — |
| `mk_is_nzero` / `mk_is_pzero` | 3829-3849 | `lemma_zero_sign_partition` | — |
| `mk_is_denormal` | 3849-3862 | (definitional: `is_denormal`) + exhaustiveness/disjointness lemmas | — |
| `mk_is_normal` | 3862-3894 | (definitional: `is_normal`, with the `is_special == exp==top_exp` identity noted in a comment) + exhaustiveness/disjointness lemmas | — |
| `mk_top_exp` / `mk_bot_exp` | 3894-3901 | (definitional: `top_exp`/`bot_exp`) | — |
| `mk_min_exp` / `mk_max_exp` | 3902-3912 | — | simple constructors, not rewrite rules (out of scope) |
| `mk_leading_zeros` | 3913-3951 | — | recursive bit-counting circuit, out of scope (regex-derivative analogue) |
| `mk_bias` | 3952-3960 | `bias` (definition matches the code exactly: `(e + (2^(ebits-1)-1)) mod 2^ebits`) | — |
| `mk_unbias` | 3961-3975 | `unbias` (definition matches the code's bit-extract/not/concat trick exactly) + **`lemma_bias_unbias_inverse`**: `unbias(bias(e)) == e` for every valid exponent `e`, proved in general (parametric in `ebits`, not just spot-checked) | — |
| `unpack`, `round`, and all arithmetic (`mk_add`/`mk_mul`/`mk_div`/`mk_sqrt`/`mk_fma`/`mk_round_to_integral`/`mk_float_lt`/`gt`/`le`/`ge` at the BV level) | 558-2524, 3976+ | — | bit-precise rounding circuits (out of scope) |

## Notable results

1. **NaN-reflexivity contrast.** `eq_core` (backing SMT's `=`) is
   proved to be a genuine equivalence relation — reflexive
   (`lemma_eq_core_refl`, *including* on NaN), symmetric, and
   transitive — while `float_eq` (backing IEEE-754 `fp.eq`) is proved
   **not** reflexive on NaN (`lemma_float_eq_nan_irreflexive`) and
   instead identifies the two signed zeros
   (`lemma_float_eq_signed_zero`), which `eq_core` deliberately does
   *not* do (`lemma_eq_core_signed_zero`). The two relations are
   proved to coincide exactly outside these two deliberately-engineered
   divergence points (`lemma_float_eq_eq_core_agree`).

2. **Bias/unbias round trip.** `mk_unbias`'s sign-bit-flip bit trick
   was hand-verified for `ebits = 3` (all 8 exponent values) before
   attempting the proof, then proved in full generality
   (`lemma_bias_unbias_inverse`, parametric in `ebits >= 2`) via a
   two-case modular-arithmetic argument (`e < 2^(ebits-1)` vs.
   `e >= 2^(ebits-1)`), using `FStar.Math.Lemmas` for the
   div/mod reasoning steps. This is a genuine, previously-unverified
   (in this audit) correctness property of the converter's exponent
   encoding, not a restatement of the code.

3. **Classification is a clean 5-way partition.** Both the value-level
   theory ([`Z3FpaTheory.fst`](Z3FpaTheory.fst), parametrized by an abstract subnormal
   classifier) and the bit-level theory ([`Z3FpaConverter.fst`](Z3FpaConverter.fst), fully
   concrete) prove that NaN / Infinity / Zero / Subnormal / Normal are
   mutually exclusive and jointly exhaustive — i.e. the five
   `fpa2bv_converter.cpp` classification predicates never overlap and
   never miss a case, for every possible bit pattern.

## Gaps (not addressed — harder, left for future work)

- **Bit-precise rounding.** The single largest gap, by far: none of
  `add`/`sub`/`mul`/`div`/`rem`/`sqrt`/`fma`/`round_to_integral`'s
  *numeric* behavior (as opposed to their NaN/Infinity special-value
  handling) is modeled, at either the `mpf` constant-folding level or
  the `unpack`/`round` bit-vector circuit level. This would require a
  separate, substantial formalization of IEEE-754 rounding semantics.
- **`mk_leading_zeros`.** The recursive divide-and-conquer
  leading-zero-count circuit (used by `unpack` for subnormal
  renormalization) is self-contained enough to be a plausible target
  for a future, focused proof effort (it's a pure bit-manipulation
  algorithm, no rounding), but was not attempted here.
- **`to_fp(rm, to_real(int))` overflow detection** in
  `mk_is_normal`/`mk_is_subnormal` (`fpa_rewriter.cpp`, via
  `mk_is_inf_of_int`) needs bit-precise exponent-range reasoning tied
  to a specific `(ebits, sbits)` format and the magnitude of the
  integer literal; scoped out, but the abstract magnitude-classifier
  parametrization in [`Z3FpaTheory.fst`](Z3FpaTheory.fst) was specifically designed so
  this could be filled in later without re-deriving the
  exhaustiveness/disjointness lemmas.
- **Concat-boundary-style case splits.** Unlike `seq_rewriter.cpp`,
  `fpa_rewriter.cpp` has no analogous "largest remaining gap" of this
  shape — its case splits are all small, finite enumerations over
  {NaN, +Inf, -Inf} already covered above.
