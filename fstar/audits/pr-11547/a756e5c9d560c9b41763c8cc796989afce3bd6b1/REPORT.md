# F* audit PR 11547 @ a756e5c9
Base 840eedc2. F* 2026.09.27, Z3 4.13.3 (pinned independent).

## Functions
1. smt_tactic_core.cpp smt_tactic l_false (~L252-275, file sha256 d1926c1fc3dc...): new throw when proofs enabled and pr null/fact not false; removed fabricated mk_asserted(false). O1: non-throw implies proof is the solver proof with fact false. O1b: proofs off unchanged.
2. then_simplifier.h reduce/supports_proofs: skip non-supporting simplifiers when proofs enabled. O2/O2b.
3. Proofs-enabled bypass (horn, nlqsat, ctx_solver_simplify, add_bounds, eq2bv, ...): returns input goal. O3/O3b.

## Correspondence
Abstract model: proof=option of fact, 0=false. Assumes m.is_false(get_fact(pr)) iff fact=false, and that get_proof returns a valid proof when non-null (trusted solver). Bypass lemma shows only identity on the goal, not that the original tactic was proof-incapable.

## Exclusions
Not checked: remaining ~15 tactic edits (same guard pattern), whitespace/include changes, python test change, prior audit files, docs. Behavioral note (not a soundness finding): skipping simplifiers/tactics reduces completeness and the new throw may turn previously answered queries into exceptions. C++ execution, memory safety, AST plumbing not mechanized.

## Reproduce
(run in the audit dir)
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include /home/runner/work/z3/z3/fstar --cache_dir /tmp/gh-aw/agent/fstar-audit/cache --odir /tmp/gh-aw/agent/fstar-audit/out Z3PR11547Audit.fst

No admit/assume; only F* standard library.