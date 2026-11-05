# F* audit of PR #11452 at ee33f5d1c694fde08fd7657c51b5caafb5e46db6 (base 1b859b6b)

Incremental scope: changes since previously audited head ed6609bf (already audited: curve certificate obligations). Previous audit covered opt_curve_certificate.cpp.

## Audited function (1 of max 3)
`in_nra_fragment` / `nra_fragment_check` in src/opt/opt_nlsat.cpp (lines ~150-192, sha256 of file 4b025807bc3721071f47fae7ffc05a1931d394a950fcf5bb56ae39b4acdba8d5). New `has_int` flag and `reals_only` parameter.

## Obligations (all proved)
1. `scan_ok`/`old_behavior`: `ok` still equals "every visited node is in the fragment"; with reals_only=false the result is exactly the pre-PR predicate (Int terms do not change behavior of maximize callers).
2. `scan_has`/`main_ok`: when the scan is ok, has_int is true iff some visited Int-sorted node is not a numeral.
3. `loop_eq`: the early exits inside the hard-constraint loop are sound; the result equals one scan over all hard formulas and the objective: ok && !(reals_only && has_int).

## Correspondence
Each visited app is abstracted to {frag_ok (family/arity test), sort kind, is_numeral}. expr_fast_mark1 visited-caching is modeled as visiting every node (caching only skips repeats; has_int is monotone, so this is sound by scan_sticky but the cache itself is not modeled). Mechanised: boolean logic of flag updates and loop. Not mechanised: C++ execution, AST traversal, memory safety, whether nlsat truly gives up on Int variables.

## Exclusions
optsmt.cpp change (removal of is_int guard so Int objectives call prove_unbounded, which now returns l_undef quickly before curve fallback), nlsat_opt::prove_unbounded body, test opt_bounds.cpp, opt_curve_certificate.cpp (audited earlier), opt_params, CMake. Vercors/fstar audit artifacts in the PR ignored.

## Assumptions
Standard F* library (List.Tot, Prims). No admits/axioms.

## Reproduce
fstar.exe --smt z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3OptNraFragment.fst
