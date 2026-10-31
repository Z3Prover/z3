# VerCors C++ audit PR 11452 @ 23c90242283ffad96d5ad8d8a06869423fe17413 (base 1b859b6)
PR open at head; no prior vercors-nfv-audit marker. Source hashes (sha256, decoded from contents API at head): opt_curve_certificate.cpp f323780015d82347129425db178c96c7170b00d313ec908c71b87b410849c82e; opt_curve_certificate.h da43d229e2bfc9b2e0a2383013718310126cc4a12f979d59344a932c557745f6.

## Selected
1. curve_certificate::prove_unbounded, backward-difference loop (cpp ~lines 139-151). Extract Diff.cpp (diff_row).
 - O1 memory safety/permissions of v[i*k+c] reads and row[c] writes, i<=j(m: PROVED for the extract.
 - O2 index bound i*k+c < m*k: PROVED (implicit in array access).
 - O3 arithmetic bounds, no int overflow of the accumulator: PROVED only for the abstracted extract (|v|<=100, k<=8, m<=4, binomial in [0,3], |row|<=300(j+1)); source uses arbitrary-precision rational, so this is not a source-level overflow claim.
 Non-vacuity: main() calls diff_row with concrete v/row (k=2,m=2,j=1) satisfying preconditions.

## Abstractions (manual correspondence, unverified)
rational-)int; vector(vector<rational)> -> flat array; binomial update binomial*(j-i)/(i+1) replaced by a bounded nondeterministic-ish step in [0,3] (the true binomial value is NOT proved here); sign computed as in source. Correctness of difference values, certify(), solver calls, polynomial semantics are NOT verified.

## Exclusions / gaps
certify() (solver calls, fresh consts, expr_safe_replace), is_polynomial, evaluate, collect_constants (Z3 AST/solver/RAII/STL, unsupported object model), optsmt.cpp/.h changes, tests, CMake, fstar audit files. The soundness core (unboundedness certificate) is therefore not covered.

## Verdict: inconclusive (partial scope; one extract proved under heavy abstraction).
Reproduce: mkdir d; cp Diff.cpp d; cd d; /tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 $PWD/Diff.cpp
