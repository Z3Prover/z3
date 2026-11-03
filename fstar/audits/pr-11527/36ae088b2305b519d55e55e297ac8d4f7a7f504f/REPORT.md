# F* audit PR #11527 @ 36ae088b2305b519d55e55e297ac8d4f7a7f504f (base 4629738b98b7b98d826833161cefbefdf1aeb928)

## Scope
Only changed file: src/test/opt_bounds.cpp (blob 42dc20b65cbb590473a89801eb0b55d4f9c6f941, sha256 of fetched copy 3a6ac08a8008bfa0db6140aa71070d3c63f346bf298286e10419718079f555ec). Changed function: tst_repeated_ite_objective (lines 1756-1794 at head) and one call at line 2324. No production code changed. Excluded: tst_opt_bounds registration edit (trivial), everything else in the file.

## Obligations (model IteMinRegression.fst)
1. O1 proved: constraints 1<=x<=3, 0<=y<=1, y<>1 force y=0 and objective=x.
2. O2 proved: min of ite(y=0,x,7) is 1, attained at (1,0) and a lower bound for all feasible points.
3. O3 proved: the buggy result from #11517 (x=3, interval 3 1) is feasible but non-optimal; expected model (x=1,y=0) is feasible.

These justify the test oracle strings ((ite (= y 0) x 7) 1), x=1, y=0. No counterexample found.

## Correspondence / assumptions
F* feasible/obj mirror the SMT-LIB assertions and minimize term over mathematical integers. Reset-assertions repetition, MaxSMT cores, arithmetic solvers 0/2/6, and output formatting are NOT modeled; the test passing is not proved. Whether the fix 628fe24 is present on the base is manually unreviewed. Not mechanized: C++ execution, memory safety, solver soundness. No assumptions beyond F* standard library; no admits.

## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir /tmp/gh-aw/agent/fstar-audit/cache --odir /tmp/gh-aw/agent/fstar-audit/out /tmp/gh-aw/agent/fstar-audit/IteMinRegression.fst

F* 2026.09.27, Z3 4.13.3 (pinned independent backend).