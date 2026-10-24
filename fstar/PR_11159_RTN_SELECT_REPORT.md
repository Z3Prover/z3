# Audit: PR #11159 — "Correct RTN selection for real-to-float conversion"

## Summary

`fpa2bv_converter::mk_to_fp_real_int` (src/ast/fpa/fpa2bv_converter.cpp,
~line 3188) converts a `(rm, int, real)` triple — an exactly-known
rational `q * 2^e` for a *concrete* integer exponent `e`, combined with
a *symbolic* (not-yet-known) rounding-mode bitvector `bv_rm` — into a
floating-point bitvector. Because `e`/`q` are concrete, the converter
precomputes, via the MPF library, the exactly-correctly-rounded result
for each of the five IEEE rounding modes (`tn`/`tz`/`tp`/`nta`/`nte` =
toward -inf / toward 0 / toward +inf / ties-to-away / ties-to-even),
then builds a `bv_rm`-indexed `ite` chain selecting among these five
precomputed bitvector constants. No further rounding arithmetic is
needed at this point — only correct *selection*.

**The bug** (line 3249, before the fix): the innermost selector
condition `c1`, whose role is to distinguish the two modes not already
covered by `c2`/`c3`/`c4` (namely RTN vs RTZ), was written as a literal
duplicate of `c2`:

```cpp
c1 = m.mk_eq(bv_rm, m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3));  // bug
c2 = m.mk_eq(bv_rm, m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3));
```

instead of

```cpp
c1 = m.mk_eq(bv_rm, m_bv_util.mk_numeral(BV_RM_TO_NEGATIVE, 3));  // fix
```

**The fix** is exactly the one-line change above (`src/ast/fpa/fpa2bv_converter.cpp`,
1 line changed), accompanied by a new regression test
`test_to_fp_real_int_symbolic_rtn` in `src/test/fpa.cpp` that forces
`bv_rm` to RTN via `(distinct m RNE RNA RTP RTZ)` and checks the result
against the literal, independently-computed RTN bit pattern for `-0.1`.

## Formalization

[`Z3FpaRTNSelect.fst`](Z3FpaRTNSelect.fst) models the five-way `ite`
chain abstractly, as a function `select : rm -> a -> a -> a -> a -> a -> a`
of an opaque rounding-mode tag and five opaque per-mode result values
(the `a` type stands in for the unmodeled bit-precise MPF-rounded
constants; selecting among already-computed values is pure control
flow, so no arithmetic needs to be formalized here — consistent with
`Z3FpaConverter.fst`'s scope decision to leave the bit-precise rounding
circuitry itself unmodeled).

Three theorems are proved:

1. **`lemma_fixed_correct`**: the fixed chain `select_fixed` agrees
   with the obviously-correct specification `spec` (a direct 5-way
   pattern match on the rounding mode) for *every* mode and every
   choice of per-mode values — i.e. the fix is fully correct, not just
   "correct at RTN".
2. **`lemma_old_wrong_at_rtn`**: the old chain `select_old` disagrees
   with `spec` *exactly* at RTN, always returning the RTZ value `tz`
   instead of the correct RTN value `tn` — pinpointing the bug's single
   failure locus.  `lemma_old_unsound_when_distinguishable` draws the
   corollary that matches the regression test: whenever the RTN and
   RTZ precomputed constants actually differ (e.g. any inexactly
   representable negative value, such as `-0.1`), the old code's
   output is provably wrong.
3. **`lemma_agree_off_rtn`**: for every mode *other than* RTN, the old
   and fixed chains coincide — confirming the fix is strictly local
   (a one-line diff touching only the previously-dead RTN branch),
   with no regression risk to the already-correct NTE/NTA/RTP/RTZ
   paths.

All three are discharged automatically by F*'s decision procedure for
the 5-constructor `rm` variant (no manual case split needed, since
`select_old`/`select_fixed`/`spec` are literal transcriptions of the
C++ `if`-chain and reduce definitionally).

## Scope / what is *not* modeled

The five precomputed MPF rounding results themselves (`tn`/`tz`/`tp`/
`nta`/`nte`, each produced by `m_mpf_manager.set(..., MPF_ROUND_*, ...)`
followed by `mk_numeral`) are bit-precise floating-point rounding
machinery, out of scope here exactly as in `Z3FpaConverter.fst` /
`FPA_REPORT.md`'s scope decision — this audit targets only the
selection logic, which is both where the bug lives and the entirety of
PR #11159's diff.

## Verification

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3FpaRTNSelect.fst
```
produces `Verified module: Z3FpaRTNSelect` / all verification
conditions discharged successfully. No `admit`/`assume`/axioms.

## Conclusion

PR #11159's fix is **formally confirmed correct and minimal**: the
one-line change makes the RTN branch select the right precomputed
constant, provably agrees with the full specification on all five
modes, and provably changes behavior on no other mode.
