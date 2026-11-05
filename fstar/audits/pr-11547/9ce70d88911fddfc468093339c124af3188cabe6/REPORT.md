# F* audit PR 11547 @ 9ce70d88911fddfc468093339c124af3188cabe6 (base 684853cb)

Semantic source audit of an abstract model; not mechanized C++ verification. The head differs from previously audited c49bfb41 (that audit covered smt_tactic guards).

## Obligations (all proved)
1. dependent_expr_state_tactic.h: proofs on + simplifier lacks supports_proofs => input returned unchanged (o1).
2. Proofs off => behavior identical to running the simplifier (o2); supported simplifier in proof mode still runs (o3).
3. tactical.cpp par_and_then: proof mode delegates to sequential and_then (o4); non-proof path unchanged (o5); parallel path reachable only when proofs disabled (o6). Note: removed fail_if_proof_generation, so soundness relies on and_then_tactical handling proofs correctly (assumed, not proved).
4. then_simplifier::reduce: skipping non-supporting children preserves an invariant if supporting ones do (o7); skipping all is identity (o8).

## Correspondence
goal/tac abstract goals and tactics; supports=supports_proofs(); run=reduce/apply. Soundness of individual tactics is an assumption (all_ok).

## Assumptions
and_then_tactical proof handling, supports_proofs() truthfulness of each simplifier, and F* standard library/base trust.

## Exclusions
smt_tactic_core.cpp l_false guard (covered by prior audit at c49bfb41 only), all other tactic edits, src/test changes, all arithmetic/swine/rewriter/other files in the compare range, memory safety, AST plumbing.

## Reproduce
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out Z3PR11547Guards.fst

F* and Z3 versions in log.