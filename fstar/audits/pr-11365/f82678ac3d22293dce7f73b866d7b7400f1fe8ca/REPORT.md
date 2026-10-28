# F* audit of PR #11365 @ f82678ac3d22293dce7f73b866d7b7400f1fe8ca (base 9dc878f01fd75e3a68364c67b5e070db0b1360b6)

Scope: PARTIAL. One changed function: `arith_rewriter::mk_eq_mod` (src/ast/rewriter/arith_rewriter.cpp, new sum-inversion branch). This is a semantic source audit of a model, not mechanized verification of C++ execution.

## Obligations (all PROVED in `ModInvSum.fst`)
1. `symmod_cong`/`symmod_bound`: `symmod(a,p)` is congruent to `a` mod p and lies in (-p/2, p/2].
2. `scale_cong`: sum of `symmod(b*c_i,p)*t_i` is congruent mod p to `b * sum(c_i*t_i)`.
3. `rewrite_sound`: given `0<=l<p` (the C++ guard) and Bezout `a*p + b*c0 == 1` (from `gcd(p,coeff,a,b)==1`),
   `(off + sum c_i t_i) mod p == l  <=>  (sum symmod(b c_i,p) t_i) mod p == (b*(l-off)) mod p`.
   This is the rewrite equivalence, both directions. Also a concrete check that for the issue #11360 values, `symmod(31337042*8691641, 100000007) == 1`.

## Correspondence
`dot cs ts` = the add-argument sum (terms abstracted by integer values; `get_power_product` plumbing is assumed to preserve value); `off` = sum of numeral args; `scale` = `symmod(inverse*coeffs[i],p)`; zero coefficients dropped by C++ contribute 0 so are consistent with `dot`; rhs = `mod(inverse*(l-offset),p)`. The guard `0<=l<p` with `p` numeral implies `p>0`, matching `p:pos`; `mod` is the non-negative Euclidean mod (F* `%` with positive divisor). Both equality orientations are handled by the swap, which is symmetric for `=`.

## Assumptions / not mechanized
- Bezout output of `gcd(p, coeff, a, b)` satisfies `a*p+b*coeff==1` when it returns 1 (assumed; hypothesis of lemma 3). Standard-library lemmas of F* (FStar.Math.Lemmas, Classical) and z3 4.13.3 are trusted; no base fstar modules imported.
- No counterexample attempted succeeded: no failing witness found; the soundness argument above found none to exist in the model.

## Excluded (not audited)
Cost/progress strictness and the 32-candidate bound (termination/performance), `BR_REWRITE2 -> BR_REWRITE_FULL` change and its termination/idempotence interaction (only tested by C++ unit tests, `tst_modular_inverse`), `m.inc()` cancellation return, hashtable dedup, integer-overflow-free rational arithmetic, AST construction (mk_mul/mk_add/mk_mod), `is_add` operand ordering, the moved `symmod` helper, and the later (unchanged) k*u mod p branches; test file src/test/arith_rewriter.cpp.

## Reproduce
```
mkdir cache out; timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out ModInvSum.fst
```
F* 2026.09.27, Z3 4.13.3 (pinned release backend). Fresh-cache result: exit 0, "All verification conditions discharged successfully".
