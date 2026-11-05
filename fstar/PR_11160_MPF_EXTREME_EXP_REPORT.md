# Audit: PR #11160 — "Fix floating-point rounding for extreme integer exponents"

## Summary

`mpf_manager::set` (src/util/mpf.cpp, ~line 266-294) builds the
correctly-rounded float for an exact rational `significand * 2^exponent`,
where `exponent` is an arbitrary-precision integer (`mpz`). PR #11160
fixes **two** independent bugs in how this unbounded `exponent` was
funneled through machine-word (`int64`)-sized arithmetic before
reaching the bit-precise rounding routine `round()`.

### Bug A — overflow check silently skipped for huge exponents

```cpp
if (m_mpz_manager.is_int64(exp) && m_mpz_manager.get_int64(exp) > mk_max_exp(ebits))
    { mk_round_inf(rm, o); return; }
```

`is_int64(exp)` is `false` whenever `|exp|` exceeds the `int64` range.
For such an `exp`, the whole conjunction is `false`, so the
overflow-to-infinity short-circuit is **skipped** — even though any
`exp` outside the `int64` range is certainly far larger than the tiny
`mk_max_exp(ebits)` bound (e.g. 1023 for binary64) whenever positive.

**Fix:** compare `exp` directly against an `mpz`-valued bound
(`m_mpz_manager.gt(exp, exp_bound)`), with no `is_int64` gate.

### Bug B — underflow path reports infinity instead of zero

```cpp
if (m_mpz_manager.is_small(exp)) { o.exponent = get_int64(exp); round(rm, o); }
else mk_inf(ebits, sbits, o.sign, o);
```

By this point `exp <= mk_max_exp(ebits)` is already known (bug A's
check). The only remaining reason `exp` could fail `is_small` is that
it is *very negative* — a deep-underflow exponent. The `else` branch
reports **infinity** for deep underflow, the exact opposite of the
correct behavior (zero, or the smallest subnormal for a directed
rounding mode).

**Fix:** clamp any `exp` below a safe floor
`min_exp = mk_min_exp(ebits) - sbits - 4` up to that floor (which
always fits `int64`), then call `round()` uniformly — relying on the
fact, documented in the fix's own comment, that `round()`'s internal
right-shift distance is capped, so sufficiently negative exponents all
round identically.

Both fixes are accompanied by `test_set_extreme_exponents`
(`src/test/mpf.cpp`), exercising exponent magnitudes from `2^31` up to
`2^64` (well past `int64`) in both signs, across all five rounding
modes, checking against `mk_max_value`/`mk_inf` (overflow side) and the
zero/smallest-subnormal boundary (underflow side).

## Formalization

[`Z3MpfExtremeExp.fst`](Z3MpfExtremeExp.fst) formalizes both bugs over
idealized (unbounded, F* `int`-valued) exponents:

- **Bug A**: `old_overflow`/`new_overflow` directly transcribe the two
  conditions (using the literal `int64` bounds, not an abstract
  placeholder, so the witnesses are concrete). `lemma_new_overflow_generalizes`
  proves the fix never loses a detection the old code had;
  `lemma_old_overflow_misses_huge_exponent` and
  `lemma_old_overflow_misses_int64_max_plus_one` exhibit the exact two
  boundary exponents from the regression test (`2^64` and `2^63`) for
  which the old check is a provable false negative while the new check
  correctly fires.

- **Bug B**: rather than treating `round()` as an opaque black box,
  `capped_sigma` reproduces its exact shift-distance computation
  (`sigma = exponent - e_min`, capped below at `-(sbits+2)`) for the
  "denormal/TINY" branch relevant to deep underflow (`mpf.cpp` lines
  1985-2008). `lemma_sigma_saturates` proves the saturation fact the
  fix's floor relies on: once `exponent <= e_min - sbits - 4`,
  `capped_sigma` has already hit its cap. `lemma_clamp_is_transparent`
  draws the soundness corollary — any two exponents at/below the floor
  produce the identical capped value, so clamping to the floor changes
  nothing observable in `round()`'s subsequent computation.
  `lemma_deep_underflow_is_not_overflow` exhibits the regression test's
  literal witness (`exponent = -2^64`, binary64 format) showing it sits
  at/below the saturation floor (hence should round to zero/subnormal)
  while being exactly the kind of "not small" value the old code wrongly
  mapped to infinity.

All lemmas are discharged by direct computation / linear arithmetic —
no case analysis or induction needed, since both bugs are boundary
conditions on machine-word representability rather than algorithmic
errors.

## Scope / what is *not* modeled

The surrounding significand-rounding arithmetic (normalization,
sticky-bit computation, final rounding-mode tie-breaking in `round()`'s
non-TINY branch) remains out of scope, as in `Z3MpfTheory.fst` /
`MPF_REPORT.md`'s original scope decision. This audit targets
specifically the two exponent-range boundary conditions that are the
entirety of PR #11160's diff.

## Verification

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3MpfExtremeExp.fst
```
produces `Verified module: Z3MpfExtremeExp` / all verification
conditions discharged successfully. No `admit`/`assume`/axioms.

## Conclusion

PR #11160's fix is **formally confirmed correct** on both counts: the
new overflow check is a strict generalization of the old one (catching
previously-missed huge-exponent overflows), and the new underflow floor
is a provably transparent clamp (by the saturation property of
`round()`'s own shift-capping logic) that replaces an incorrect
"report infinity" fallback with the correct zero/subnormal rounding.
