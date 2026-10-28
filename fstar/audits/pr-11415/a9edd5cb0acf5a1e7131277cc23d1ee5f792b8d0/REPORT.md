## Scope
Head a9edd5cb0acf5a1e7131277cc23d1ee5f792b8d0; src/smt/smt_quantifier.cpp at head sha256 bab569d528569b71414d9576aa48eeb0bd5e6fc5faa5e275d33a18c1090d56f8 (1502 lines). Compared to 07e7ff68 (sha256 0754e4bb...ecc, 1437 lines; already audited by a previous comment): diff = arith_project_nested (head lines ~920-979), call at ~1028, boundary scaling at ~1066, offset-loop break at ~1072, and swapped order of self(condition) in get_arith_bounds collect lambda (~728/730).

## Obligations (all in ArithProjectAudit.fst)
- P1 (proved): arith_project_nested rewrite step. Given rule relation c*A+R=0 with c nonzero, replacing k*A in `rest + k*A` by (-k/c)*R preserves the rational value (p1_project_step; ring identities via CanonCommSemiring, no admit).
- P2 (proved): scale 1/(projected+1) is nonzero/well-formed; projected<=8 since the loop has 8 steps; projected=0 leaves pre-PR boundary unchanged.
- P3 (proved): offset loop {0,1,-1}: when projected, only offset 0 is attempted; when not projected, behaviour equals pre-PR (all three offsets if budget>=6); budget never underflows.

## Correspondence / assumptions
F* models rational arithmetic as num/den pairs and the loop as a list recursion; it does not mechanize C++ execution, th_rewriter, var_subst, AST plumbing, memory safety. P1 assumes the rule relation c*A+R=0 holds as an equality; in C++ the rules come from inequality bounds and the code comment states results are candidate instantiation terms, not asserted lemmas, so soundness of the solver does not depend on P1: instances are added via add_instance of the original quantifier (any ground instance of a forall is entailed). That entailment (arity/ordering of bindings) was covered by the earlier audit O2/O3 and is not re-proved here. Standard F* library assumptions inherited.

## Exclusions
Source changes in qi_params.*, smt_params_helper.hpp, CMakeLists, quant_tactics.cpp, test/smt_context.cpp; arith_unify, arith_eliminate, get_arith_bounds, add_arith_instance (unchanged vs. previous audit); termination/performance of projection; completeness/usefulness of heuristic.

## Reproduce
cd fstar-audit dir; fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out ArithProjectAudit.fst (timeout 120). F* 2026.09.27, Z3 4.13.3. Source sha256 3aa93f5ccd35c657ca7bc7477a656f0e2028ac9850f17d80fbd93b1ef8d29ef4.