## Obligations
1. (smt_tactic) with proofs enabled, success implies proof with fact false attached: PROVED.
2. (smt_tactic) without proofs, no throw and no non-false-fact proof retained: PROVED.
3. (solver2tactic) with proofs enabled, success implies no assumptions (unsat cores) and proof of false: PROVED.

## Correspondence
F* models proof as option bool (null / fact-is-false). Guards mirror smt_tactic_core.cpp ~L257-260 and solver2tactic.cpp ~L109,L140. Assumes m.is_false(m.get_fact(pr)) is the correct test (prior code used pointer compare to mk_false).

## Not covered
The expr_safe_replace substitution of asserted proofs by input proofs (soundness of resulting proof term, hash-consing of mk_asserted), the model-converter condition change, get_consequences test file, C++ execution. Semantic model only, not C++ verification.

## Observation (manual)
Behavior change: proofs+unsat-core now throws in solver2tactic rather than degrading; intended per PR.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out PrGuards.fst (F* 2026.09.27, Z3 4.13.3). Base SHA 605d1d83a4614804d400ce5b23eca1f4a20184dd.