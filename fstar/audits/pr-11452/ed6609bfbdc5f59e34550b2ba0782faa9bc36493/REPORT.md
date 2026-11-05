# Audit of PR #11452 (curve_certificate::prove_unbounded / certify) at ed6609bfbdc5f59e34550b2ba0782faa9bc36493

Base 1b859b6bc7637a9c802a92a0dee72df9e843274d. Sources fetched via contents API at head: src/opt/opt_curve_certificate.cpp (278 lines, sha256 f323780015d82347129425db178c96c7170b00d313ec908c71b87b410849c82e), opt_curve_certificate.h (69 lines, sha256 da43d229e2bfc9b2e0a2383013718310126cc4a12f979d59344a932c557745f6).

## Scope
Changed functions audited (3): `curve_certificate::certify` (lines ~165-278, basis/integrality construction), `prove_unbounded` (lines ~118-190, backward-difference curve), and the certificate's unboundedness argument (guards in `certify`).
Excluded: optsmt.cpp/optsmt.h integration (cancellation, timeout, lexicographic handling, minimization negation), opt_params.hpp, CMake, tests, `is_polynomial`, `evaluate`, `collect_constants`, and the nlsat projection path. Not claimed: full PR coverage.

## Obligations
1. (proved) Integer basis witnesses: with `j*b_j = b_{j-1}*(t+j-1)`, b_2 = h2(t), b_3 = h3(t) defined by integer recurrences exist for every integer t>=0 (so the `along` constraints are satisfiable and do not exclude any t>=0), and satisfy 2*h2 = t(t+1), 3*h3 = h2*(t+2). Lemmas `h2_ok`, `h3_ok`.
2. (proved) Newton backward-difference interpolation (degree 3, the largest case): with the coefficients `differences[j]` from prove_unbounded, the curve c0 + d1*t + d2*B2 + d3*B3 takes the values of the latest four models at t=0,-1,-2,-3 (scaled by 6 to stay integral). Lemma `interp`. This shows the curve starts at the latest model so the objective bound p >= p(latest) is anchored at a real model value.
3. (proved) Ray case unboundedness: if c0+c1*t>=c0 for all t>=0 and is non-constant at some t1>=1, then c1>0 and the value exceeds any bound m. Lemma `ray_unbounded`. Higher degrees are argued in prose only (non-constant polynomial bounded below on t>=0 tends to +oo); not mechanized.

No counterexample found; no refutation attempt succeeded because the guards appear to match the stated property.

## Correspondence and assumptions
F* models integer polynomials in t; the C++ uses rational coefficients (integrality guard `coefficient.is_int()` for Int constants), SMT solver results for `check` (assumed sound: l_false results trusted), and `other_consts` frozen to latest-model values. The F* modules do not model the SMT calls, C++ execution, rational arithmetic, to_real casts for Real constants, memory safety, or optsmt integration. Mixed-sort and Real-sort paths, the unit-direction fallback, and the hard-constraint check (every hard constraint holds on the whole curve) are manually reviewed only. Observation (manual): the check `not(p = p0)` at t>=1 only requires non-constancy at t>=1; combined with p>=p0 for all t>=0 this implies non-constant overall, which is consistent with the claim.
Inherited assumptions: F* standard library and Z3 4.13.3 as SMT backend. No admits/assumes.

## Reproduce
```
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3OptCurveCertificate.fst
```
