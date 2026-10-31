# VerCors C++ audit, PR 11211, head 43059f2a

Sources read through the GitHub contents API at the head SHA. SHA256: arith_swine.cpp 8b53077fafd66049ca9abd276c70c678af6a10718521b6db031e282709f6fe54 (426 lines); arith_swine.h 19de765976d70c323316cfd5d3d67866dc03c04dfe2f3e606821b7aa3ff5fc51 (58 lines). The PR was open at that SHA with no existing audit comment for it.

## Selected candidate
`arith_swine::compute_power` (lines 22-49). Candidate obligations:
1. The guard `y <= max_bits/x.bitsize()` prevents huge computations.
2. The exponentiation loop terminates and the result equals x^y.
3. The special cases (0, 1, -1) are correct.

## Outcomes
All three are **inconclusive**.
- The function operates on the arbitrary-precision `rational` class (bitsize(), *=, is_unsigned()) and on the `m.inc()` resource callback. These cannot be expressed faithfully in VerCors C++ without invented trusted contracts.
- A first abstracted extract (unit PowerGuard.cpp) over machine ints failed in the frontend with `Could not determine the size of the bit vector for this bitwise operation`. It used `1 << 20`, so it did not verify.
- An abstraction replacing the bignum with int would not correspond to the source arithmetic, so the extract was abandoned rather than weakened.

## Exclusions
All other changed C++ (arith_swine lemma generators, check_model, theory_lra, arith_solver, rewriter, sat_solver, tactics, tests) were excluded. They depend on STL/AST/expr_ref_vector object models, RAII and exceptions, which are unsupported or would need unjustified abstraction. The fstar/ files are covered by other audits.

## Reproduction
`/tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 <abs>/PowerGuard.cpp` (VerCors 2.4.0). An unsupported feature is not evidence of correctness.