# F* audit PR 11722 @ 76f1ec305a663af9588a4e20058aa25e45679b35 (base f46b3c58e41c0f9531cbb7cbab243b8cd2a98250)

Tools: F* 2026.09.27, pinned Z3 4.13.3 (independent backend), --z3rlimit 10, fresh cache.
Sources read via contents API at head SHA: src/opt/opt_solver.cpp (sha256 1ae5e5473044cdf6b2c17996c1285e363a70967496b24a34d6513283bdd69bbe, lines 208-262), src/opt/optsmt.cpp (sha256 c4bafe313b43436903ff7cfbe6718d7615c8f3bfee281188e932d87471b3efd9, lines 107-150, 640-690, 739-750).

## Changed functions (3)
1. opt_solver::maximize_objective_isolated: inside the push scope it now asserts m_assumptions plus the caller assumptions and rechecks (returns false if not l_true) before maximizing.
2. optsmt::update_lower(expr_ref&): failure of maximize_objectives1 now returns false instead of bound=true; geometric_opt maps this to l_undef.
3. optsmt::maximize-with-assumption loop (line ~664): passes (1, vars) to maximize_objectives1.

## Obligations
- O1 (proved, refutation of OLD code): witness list [{x=0,b=true};{x=5,b=false}]: old scope yields Some 5 (overshoot, the unsound unbounded/oversized bound), new yields Some 0. This is a counterexample to the base behaviour, not to the PR.
- O2 (proved): if isolated_new returns Some v, every candidate model satisfying base and the assumption has x <= v (assumption-respecting maximum is an upper bound of the witnessed values).
- O3 (proved): a failed update_lower yields l_undef (never a true/unbounded bound) and an empty feasible scope returns false.

## Correspondence and assumptions
Model: a finite list of candidate models (x,b) stands for the models of the scope; base assertion b=>x=0 mirrors the PR unit test. max_of abstracts the LP/arith maximizer as an exact maximum over candidates. Assumes m_context.check after asserting assumptions is correct (smt::context trusted), that m_assumptions are the pending solver assumptions, and that the recheck result l_undef/l_false correctly maps to returning false. Not verified: C++ execution, push/pop scope balance (on_scope_exit), that m_assumptions is non-stale, performance cost of the extra check per objective per call, the baseline-model floor update_from_baseline_model (which can still raise a value from a model not satisfying assumptions if baseline_model is taken before assumptions — manually reviewed: baseline comes from m_context.get_model at call time, which satisfies assumptions of the last check). One manual note: in the geometric path maximize_objectives1(disj) is called without assumptions, relying on m_assumptions/asserted scope only; this is correct when no check-with-assumptions is pending.

## Reproduce
cd fstar-audit; /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include fstar --cache_dir cache --odir out Pr11722Opt.fst
Exit code: exit 0
