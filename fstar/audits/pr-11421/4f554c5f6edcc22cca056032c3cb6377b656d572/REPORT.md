# F* audit: PR 11421 (head 4f554c5f6edcc22cca056032c3cb6377b656d572, base 668d5979550e899e8341aad1b0a9ad6ff011f821)

Scope (partial): one changed function, `fpa2bv_converter::mk_to_fp_real` (symbolic-real branch), src/ast/fpa/fpa2bv_converter.cpp, head lines ~2996-3185 (head blob f7516c06, sha256 of fetched file 67ef8042feb06aa97869ed2154a1fe56140eb80fc2d7ecb644533111eef2b7eb). Three obligations on the new bit-based encoding.

## Obligations (all proved)
- O1: the conditional-weight loops over fraction/exponent bits decode to the field value (sum bit_i*2^i == x for x<2^n); the ULP loop (factor 2^(2^i) per set exponent bit i) yields 2^e.
- O2: encoded magnitude base + sum(bit_i*2^i)*gap_up equals IEEE magnitude (subnormal s*minsub, normal (2^p+s)*2^(e-1)*minsub), and lies within the asserted bounds [base, base+(2^p-1)*gap_up]. Units: half minimum subnormal, so the initial gap_up = minsub/2 is integral.
- O3: gap_down chosen by guard (exp==0 || exp==1 || sig!=0 ? gap_up : gap_up/2) is exactly the distance to the IEEE predecessor, for all e>=1 including the binade boundary and the smallest normal.

No counterexample found. Verdict: proved for these obligations only.

## Mapping / assumptions
F* nat arithmetic models rational values scaled by 2/minsub; p = sbits-1, e = biased exponent field. Assumes ebits/sbits constants as in C++ (max_exp fits uint). Proofs use only FStar.Math.Lemmas from the pinned F* standard library; no admits/axioms.

## Not verified (exclusions)
The rounding-relation conditions (nte/nta/tp/tn/tz, ties, overflow), sign constraints, zero case, test file src/test/fpa.cpp, soundness of the removed `round`/`to_real` path, NaN/inf exponent=all-ones handling (excluded in C++ by the not-NaN assertion and the not-inf guard), Z3 execution of the emitted terms, AST plumbing, memory safety. These are manually reviewed only (the guard `not (nan or inf)` -> rounding_cond looks consistent with the pre-change structure). Fresh result fields are unconstrained except via m_extra_assertions; this relies on those assertions being asserted, as before.

## Reproduce
See verification log. Versions: F* 2026.09.27, Z3 4.13.3.
