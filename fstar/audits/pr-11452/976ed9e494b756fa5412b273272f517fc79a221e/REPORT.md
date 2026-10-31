# F* audit of PR 11452 @ 976ed9e494b756fa5412b273272f517fc79a221e

Base for delta: ee33f5d1c694fde08fd7657c51b5caafb5e46db6 (previous audit). Changed functions: nlsat_opt::can_approach_from_below (guard now reals_only=true), nlsat_opt::check_limit (new early in_nra_fragment(reals_only=true) on purified goal forms plus T), plus doc comment in opt_nlsat.h and tests (opt_bounds.cpp parabola test, opt_nlsat.cpp mixed int test).

## Obligations
- O1 proved: early exit only maps result to l_undef, never flips true/false.
- O2 proved: a definite result from the new code equals the underlying nlsat result and all guards held.
- O3 proved: if all guards hold (no integer terms) behavior is identical to before.

## Correspondence
Model: lbool as 3-valued type; guard booleans abstract the in_nra_fragment calls (semantics of in_nra_fragment verified in earlier audit at ee33f5d); r abstracts the nlsat limit query. Not modelled: whether nlsat actually returns undef on integer variables (stated in comment, assumed), goal/form extraction, rlimit accounting, C++ execution, memory safety.

## Assumptions
None beyond F* core and standard library; no admits/axioms.

## Exclusions
src/opt/opt_curve_certificate.cpp/.h, optsmt.cpp/.h, opt_params.hpp, CMakeLists, test files (not mechanized; quadratic curve test not analysed), unchanged earlier-audited content.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir /tmp/gh-aw/agent/fstar-audit/cache --odir /tmp/gh-aw/agent/fstar-audit/out Z3OptNlsatGuard.fst

F* 2026.09.27, Z3 4.13.3