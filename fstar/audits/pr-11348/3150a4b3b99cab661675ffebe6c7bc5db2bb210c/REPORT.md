# F* audit PR 11348 @ 3150a4b3 (base aa71a62f)
F* 2026.09.27, Z3 4.13.3 (pinned backend, not PR-built).

## Obligations (all proved)
1. src/cmd_context/basic_cmds.cpp set_option :global-decls: unchanged value never errors; changing value after has_manager errors; otherwise sets the requested value (ob1a-c).
2. src/smt/theory_arith_core.h and src/smt/theory_lra.cpp (3 sites incl. power0): with proofs enabled the underspecified-equality literal is a theory axiom (mk_th_axiom), else assigned as before (ob2a-b).
3. fstar/Z3IntegerDivision.fst lemma_upper_bound/lemma_residual_bound arithmetic facts: x%(n+1)<=n, x%y-y<=-1 for y>0, x-y*(x/y)==x%y>=0 (ob3a-c).

## Correspondence and assumptions
Models are small abstractions of the C++ guards/branches; they do not mechanize C++ execution. Assumed: F* integer % is Euclidean (matches Z3 mod for nonzero divisors); mk_th_axiom yielding a checkable proof step is NOT verified. Base modules not imported. Obligation 2 only models the branch choice, not proof-checker acceptance of the axiom.

## Exclusions (manual review needed)
src/api/ml/CMakeLists.txt linker flags; fstar/Z3ArrayEquality, Z3SortedQuantifier, Z3ArithmeticRewrite, Z3NativeProof, Z3ProofDocument, Z3SortedProof, tests, OCaml/Python tooling, earlier audit files. Full Z3IntegerDivision.fst checking was not re-run.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3Pr11348Audit.fst