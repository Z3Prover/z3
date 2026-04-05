# F\* Formalization of FPA Rewriter Rules (PR #9038)

This directory contains a formalization of the floating-point rewrite
rules introduced in [Z3 PR #9038](https://github.com/Z3Prover/z3/pull/9038)
in the [F\*](https://www.fstar-lang.org/) proof assistant.

## Overview

PR #9038 adds three families of optimizations to `src/ast/rewriter/fpa_rewriter.cpp`
that avoid expensive FP bit-blasting:

| Optimization | C++ function | F\* module and section |
|---|---|---|
| `fma(rm, ±0, y, z)` zero-multiplicand decomposition | `mk_fma` | `FPARewriterRules.fst` §1 |
| `isNaN/isInf/isNormal` applied to `to_fp(rm, to_real(int))` | `mk_is_nan`, `mk_is_inf`, `mk_is_normal`, `mk_is_inf_of_int` | `FPARewriterRules.fst` §2 |
| Push classification predicates through `ite` with concrete branches | `mk_is_nan`, `mk_is_inf`, `mk_is_normal` | `FPARewriterRules.fst` §3 |

## Files

### `IEEE754.fst`

Abstract axiomatic theory of IEEE 754 floating-point arithmetic.
- **Type** `float eb sb` — abstract float parameterized by exponent bits `eb`
  and significand bits `sb`, matching Z3's `mpf` representation.
- **Type** `rounding_mode` — the five IEEE 754 rounding modes (RNE, RNA, RTP,
  RTN, RTZ).
- **Classification predicates** — `is_nan`, `is_inf`, `is_zero`, `is_normal`,
  `is_subnormal`, `is_negative`, `is_positive`, derived `is_finite`.
- **Arithmetic operations** — `fp_add`, `fp_mul`, `fp_fma`.
- **Conversion** — `to_fp_of_int rm x` representing `to_fp(rm, to_real(x))`.
- **Axioms** (`ax_*`) — consequences of the IEEE 754-2019 standard taken as
  given, covering classification exclusivity, NaN propagation, special-value
  arithmetic, and integer-conversion properties.
- **Overflow thresholds** — `overflow_threshold eb sb` and `max_finite_int eb sb`
  corresponding to the values computed by `mk_is_inf_of_int` in the C++ rewriter.

All axioms use `assume val`, marking them as trusted without proof.

### `FPARewriterRules.fst`

Derived rewrite rules proved from `IEEE754.fst` axioms.

#### Section 1 — FMA with a Zero Multiplicand

| Lemma | Statement |
|---|---|
| `lemma_fma_zero_nan_addend` | `fma(rm, ±0, y, NaN) = NaN` |
| `lemma_fma_zero_nan_mul` | `fma(rm, ±0, NaN, z) = NaN` |
| `lemma_fma_zero_inf_mul` | `fma(rm, ±0, ±∞, z) = NaN` |
| `lemma_fma_zero_finite_decomposes` | `fma(rm, ±0, y_finite, z) = fp_add(rm, fp_mul(rm, ±0, y_finite), z)` |
| `lemma_fma_zero_const_addend` | `fma(rm, ±0, y_finite, z_nonzero_finite) = z` |
| `lemma_fma_zero_const_finite_arm` | finite arm of the `ite` for symbolic `y`, concrete non-zero `z` |
| `lemma_fma_zero_const_nan_inf_arm` | NaN/inf arm of the same `ite` |
| `lemma_fma_zero_general_finite_arm` | finite arm for fully symbolic `y` and `z` |
| `lemma_fma_zero_general_nan_inf_arm` | NaN/inf arm for fully symbolic `y` and `z` |
| `lemma_fma_zero_product_sign` | sign of `fp_mul(rm, zero_val, y)` = sign(zero_val) XOR sign(y) |
| `lemma_fma_zero_ite_correct` | full composite: `fma(rm, ±0, y, z) = ite(is_finite(y), fp_add(rm, fp_mul(rm, ±0, y), z), NaN)` |

#### Section 2 — Classification of Integer-to-Float Conversions

| Lemma | Statement |
|---|---|
| `lemma_is_nan_to_fp_int` | `isNaN(to_fp(rm, x)) = false` |
| `lemma_is_inf_to_fp_int_rne` | `isInf(to_fp(RNE, x)) ↔ \|x\| ≥ overflow_threshold` |
| `lemma_is_inf_to_fp_int_rna` | `isInf(to_fp(RNA, x)) ↔ \|x\| ≥ overflow_threshold` |
| `lemma_is_inf_to_fp_int_rtp` | `isInf(to_fp(RTP, x)) ↔ x > max_finite_int` |
| `lemma_is_inf_to_fp_int_rtn` | `isInf(to_fp(RTN, x)) ↔ x < -max_finite_int` |
| `lemma_is_inf_to_fp_int_rtz` | `isInf(to_fp(RTZ, x)) = false` |
| `lemma_is_normal_to_fp_int` | `isNormal(to_fp(rm, x)) ↔ x ≠ 0 ∧ ¬isInf(to_fp(rm, x))` |
| `lemma_is_normal_to_fp_int_rne` | combined form for RNE |
| `lemma_is_normal_to_fp_int_rtz` | combined form for RTZ |

#### Section 3 — Classification through `ite`

| Lemma | Statement |
|---|---|
| `lemma_is_nan_ite` | `isNaN(ite(c, t, e)) = ite(c, isNaN(t), isNaN(e))` |
| `lemma_is_inf_ite` | `isInf(ite(c, t, e)) = ite(c, isInf(t), isInf(e))` |
| `lemma_is_normal_ite` | `isNormal(ite(c, t, e)) = ite(c, isNormal(t), isNormal(e))` |

The Section 3 lemmas are trivially true in F\* by computation (applying a
function to `if c then t else e` reduces to `if c then f t else f e`), which
is why their proofs are the single term `()`.

### `../src/ast/rewriter/fpa_rewriter_rules.h`

C++ header containing one `#define` macro per rewrite rule, extracted from
the F\* lemmas.  Each macro is annotated with a `[extract: MACRO_NAME]`
comment in the corresponding F\* lemma.

| Macro | F\* lemma(s) | Used in C++ function |
|---|---|---|
| `FPA_REWRITE_IS_NAN_TO_FP_INT` | `lemma_is_nan_to_fp_int` | `mk_is_nan` |
| `FPA_REWRITE_IS_NAN_ITE` | `lemma_is_nan_ite` | `mk_is_nan` |
| `FPA_REWRITE_IS_INF_TO_FP_INT` | `lemma_is_inf_to_fp_int_*` | `mk_is_inf` |
| `FPA_REWRITE_IS_INF_ITE` | `lemma_is_inf_ite` | `mk_is_inf` |
| `FPA_REWRITE_IS_NORMAL_TO_FP_INT` | `lemma_is_normal_to_fp_int` | `mk_is_normal` |
| `FPA_REWRITE_IS_NORMAL_ITE` | `lemma_is_normal_ite` | `mk_is_normal` |
| `FPA_REWRITE_FMA_ZERO_MUL` | `lemma_fma_zero_*` (all §1 lemmas) | `mk_fma` |

Each macro is self-contained and uses `_fpa_`-prefixed local variables to
avoid name collisions.  All macros are designed for use inside member
functions of `fpa_rewriter` where `m()`, `m_util`, `m_fm`, and
`mk_is_inf_of_int` are in scope.

The helper function `mk_is_inf_of_int` (declared in `fpa_rewriter.h`,
implemented in `fpa_rewriter.cpp`) computes the integer-arithmetic overflow
condition for `isInf(to_fp(rm, x))` by switching on the rounding mode,
corresponding to the five `lemma_is_inf_to_fp_int_*` lemmas.

## Relationship to the C++ Code

The following table maps each lemma to its corresponding C++ macro and the function where the macro is invoked.

| Lemma | C++ macro | Used in |
|---|---|---|
| `lemma_fma_zero_nan_addend` | `FPA_REWRITE_FMA_ZERO_MUL` case (a) | `mk_fma` |
| `lemma_fma_zero_nan_mul` | `FPA_REWRITE_FMA_ZERO_MUL` case (b) | `mk_fma` |
| `lemma_fma_zero_inf_mul` | `FPA_REWRITE_FMA_ZERO_MUL` case (b) | `mk_fma` |
| `lemma_fma_zero_finite_decomposes` | `FPA_REWRITE_FMA_ZERO_MUL` case (c) | `mk_fma` |
| `lemma_fma_zero_const_addend` | `FPA_REWRITE_FMA_ZERO_MUL` case (c) | `mk_fma` |
| `lemma_fma_zero_const_*_arm` | `FPA_REWRITE_FMA_ZERO_MUL` case (d) | `mk_fma` |
| `lemma_fma_zero_general_*_arm` | `FPA_REWRITE_FMA_ZERO_MUL` case (e) | `mk_fma` |
| `lemma_fma_zero_product_sign` | `FPA_REWRITE_FMA_ZERO_MUL` sign computation | `mk_fma` |
| `lemma_is_nan_to_fp_int` | `FPA_REWRITE_IS_NAN_TO_FP_INT` | `mk_is_nan` |
| `lemma_is_inf_to_fp_int_*` | `FPA_REWRITE_IS_INF_TO_FP_INT` + `mk_is_inf_of_int` | `mk_is_inf` |
| `lemma_is_normal_to_fp_int` | `FPA_REWRITE_IS_NORMAL_TO_FP_INT` | `mk_is_normal` |
| `lemma_is_nan_ite` | `FPA_REWRITE_IS_NAN_ITE` | `mk_is_nan` |
| `lemma_is_inf_ite` | `FPA_REWRITE_IS_INF_ITE` | `mk_is_inf` |
| `lemma_is_normal_ite` | `FPA_REWRITE_IS_NORMAL_ITE` | `mk_is_normal` |

## IEEE 754 References

The axioms in `IEEE754.fst` correspond to the following sections of the
IEEE 754-2019 standard:

- §4.3 — Rounding-direction attributes (rounding modes)
- §5.4 — Arithmetic operations (`fp_add`, `fp_mul`, `fp_fma`)
- §5.4.1 — Conversion from integer (`to_fp_of_int`)
- §5.7.2 — General operations: `isNaN`, `isInfinite`, `isNormal`, etc.
- §6.2 — Operations on quiet NaNs (NaN propagation)
- §6.3 — The sign bit: signed zero (`ax_zero_mul_sign`, `ax_add_zero_nonzero`)
- §7.2 — Invalid operation exception: 0 × ∞ = NaN (`ax_zero_mul_inf`)

## Building

To type-check these files with F\*, from this directory run:

```sh
fstar.exe --include . IEEE754.fst FPARewriterRules.fst
```

F\* 2024.09.05 or later is recommended.  The files have no external
dependencies beyond the F\* standard library prelude.

Because all IEEE 754 semantics are encoded as `assume val` axioms, the
type-checker accepts the development without requiring a concrete model.
The derived lemmas in `FPARewriterRules.fst` are fully verified against
those axioms; the Section 3 lemmas (`lemma_*_ite`) are discharged by
computation reduction alone.
