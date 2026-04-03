# F\* Formalization of FPA Rewriter Rules (PR #9038)

This directory contains a formalization of the floating-point rewrite
rules introduced in [Z3 PR #9038](https://github.com/Z3Prover/z3/pull/9038)
in the [F\*](https://www.fstar-lang.org/) proof assistant.

## Overview

PR #9038 adds three families of optimizations to `src/ast/rewriter/fpa_rewriter.cpp`
that avoid expensive FP bit-blasting:

| Optimization | C++ function | Formalized in |
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
| `lemma_fma_zero_product_sign` | sign of `fp_mul(rm, ±0, y)` = sign(±0) XOR sign(y) |
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

## Relationship to the C++ Code

The following table maps each lemma to the corresponding C++ code in
`src/ast/rewriter/fpa_rewriter.cpp` after the PR is applied.

| Lemma | C++ code |
|---|---|
| `lemma_fma_zero_nan_addend` | `if (m_util.is_nan(arg4)) { result = nan; return BR_DONE; }` |
| `lemma_fma_zero_nan_mul` | `if (m_util.is_numeral(other_mul, vo) && m_fm.is_nan(vo))` |
| `lemma_fma_zero_inf_mul` | `if (m_util.is_numeral(other_mul, vo) && m_fm.is_inf(vo))` |
| `lemma_fma_zero_finite_decomposes` | `m_util.mk_add(arg1, m_util.mk_value(product), arg4)` with `m_fm.mul(rm, vzero, vo, product)` |
| `lemma_fma_zero_const_addend` | `m().mk_ite(finite_cond, arg4, nan)` (z_const branch) |
| `lemma_fma_zero_general_*` | general `m().mk_ite(finite_cond, m_util.mk_add(...), nan)` |
| `lemma_is_nan_to_fp_int` | `mk_is_nan`: `result = m().mk_false(); return BR_DONE;` |
| `lemma_is_inf_to_fp_int_*` | `mk_is_inf_of_int` switch statement |
| `lemma_is_normal_to_fp_int` | `mk_is_normal`: `result = m().mk_and(not_zero, m().mk_not(inf_cond))` |
| `lemma_is_nan_ite` | `mk_is_nan`: ite-pushthrough block |
| `lemma_is_inf_ite` | `mk_is_inf`: ite-pushthrough block |
| `lemma_is_normal_ite` | `mk_is_normal`: ite-pushthrough block |

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
