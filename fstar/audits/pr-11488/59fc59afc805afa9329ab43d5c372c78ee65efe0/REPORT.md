# F* audit of PR #11488 @ 59fc59afc805afa9329ab43d5c372c78ee65efe0 (base deef01f5b899f47fdbeccb0f408b57324cbb1ffe)

**Scope (partial):** 1 changed function, `mpf_manager::fma` in `src/util/mpf.cpp` (extraction block, head lines ~921-929; head file blob sha256 82e8cb5dd45be64d5c73940d6cee3a335238c14ed1e2065d41ec708cb9439e0e, base sha256 b60de22b57efce3d6724e9c7d4cfea51771ee0aba8d7b642d5ba73089290c23e). Excluded: `src/test/fpa.cpp` (tests; not executed, PR code not run), the rest of fma (alignment, add/sub, renormalisation, `round`), fpa2bv/bit-blast FMA path, memory safety.

## Behaviour
After renormalisation `res.significand` S has 2s+3 bits (s=sbits), value S*2^(e-(2s+2)). Extraction must produce o with s+4 bits (3 guard bits), value m*2^(e'-(s+3)), preserving the value (discarded low bits go to the sticky bit).
Base: for s>=4, m = S / 2^(s-1) (sticky from remainder); for s<4, m = S*2^(4-s+3), exponent -= 4-s+3.
Head: uniform m = S / 2^(s-1), sticky from remainder, exponent unchanged, for all s.

## Obligations
1. **Counterexample on base (proved in F*)**, `witness_base_s3`: for s=3 (FP(2,3)), S=1536, the base mapping yields value 4x the true value (factor 2^(s-1)). Also `witness_base_s2` for s=2 (factor 2). This matches the issue's wrong FMA results; it is a model-level witness (concrete S), not an execution of Z3.
2. **Head extraction is value-exact for s in 2..6 when discarded bits are zero** (`head_exact`), proved. Non-zero discarded bits are covered by the unchanged sticky logic (`renorm_sticky |= rem != 0`), which was already used for s>=4; not separately mechanised (inconclusive for the rounding step).
3. Not attempted (bound): interaction with the following `bitsize > sbits+4` trimming and `round`; for s<4 head m has exactly s+4 bits or fewer since S < 2^(2s+3), so the trim is a no-op, argued manually only.

## Mapping and assumptions
Mpf values are modelled as integer significand times power of two, scaled by 2^20 (s<=6). Not mechanised: C++ execution, mpz behaviour, the SMT-level regression tests, memory safety. Base library only (FStar.Math.Lemmas); no admit/assume/axioms. The F* model re-derives the formulas from the C++ by hand.

## Verdict
Obligation 2 proved; base bug witnessed at model level; the PR's change is consistent with the intended property for the extraction step. Verdict `proved` applies only to the selected obligations on the head; coverage is partial as listed above.
