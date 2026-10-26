# F* audit of PR #11356 @ 7dac245e68a3321fbe2328a0d0676d7bc3784503 (base aa71a62fdffbfede37f7558b52da4d52841e04ea)

## Scope
Selected: (A) `theory_seq::can_reduce_eqs` + `solve_eqs` (src/smt/seq_eq_solver.cpp, new lines ~30-48) interacting with `theory_seq::simplify_and_solve_eqs` (src/smt/theory_seq.cpp ~1551-1557) and `theory_seq::propagate` (~2868-2887).
Obligations: O1 fixpoint after budget exhaustion; O2 budget exhaustion from a 2048-equation witness; O3 non-termination of the suspended while loop (model-level).
Excluded (not audited): `canonize(expr*,expr_ref_vector&,...)` and `expand` stack restore (shrink to sz; manual read looks consistent), `new_eq_eh` callers, `solve_eq` internals, src/test/seq_limits.cpp, theory_seq.h member, memory safety, effect of dropping m_new_solution on non-suspended paths.

Source hashes (fetched via contents API at head SHA): theory_seq.cpp sha256 63c6ebd63c9d023e4a8b2b2e40a4b7e0a20f8683a43122e448574166bf59c406; seq_eq_solver.cpp sha256 4e6fdc5aa70a61278050e8058f32316d86c8e8a759e6dab4c73e195d1b31812e.

## C++ facts (manually reviewed)
- `reslimit::inc()` returns `not_canceled()` = `m_suspend || ...`; so `m.inc()` is true whenever suspended (src/util/rlimit.h:80-83).
- `can_reduce_eqs()`: if suspended and counter>=1024 -> sets m_new_solution=true, returns false; else ++counter.
- `solve_eqs`: loop stops when can_reduce_eqs false; afterwards `if (!inconsistent && i<m_eqs.size()) m_new_solution = true`.
- `simplify_and_solve_eqs`: `m_new_solution=true; while (m_new_solution && !ctx.inconsistent() && m.inc()) { m_new_solution=false; solve_eqs(0); }`. No other exit.
- `propagate()` resets counter to 0 at entry then calls `simplify_and_solve_eqs()` if m_new_solution.
- `context::push` (smt_context.cpp ~3165) does `scoped_suspend_rlimit` then `propagate()`, which reaches `propagate_theories()` -> `theory_seq::propagate()` with suspended==true.

## Finding (potential bug; verdict inconclusive because C++ reachability of the suspended-with-pending-equations state is not mechanically established)
In a suspended propagate with more pending equations/normalization steps than 1024 (e.g. the PR's 2048 pending `x_i = unit(i) ++ y_i` equations, left pending after an interrupted check and then a `push`), the first round consumes the 1024 budget; every later round immediately returns from can_reduce_eqs, sets m_new_solution=true, and the loop guard stays true because m.inc() is true while suspended. Counter is reset only at the next propagate() entry, which is never reached: hang (CPU spin), exactly the resource-limit class the PR intends to fix. Suggested fix: make the loop in simplify_and_solve_eqs also stop when the budget is exhausted while suspended (e.g. break if can_reduce_eqs-exhausted / check `m_num_eager_eq_steps`), or do not leave m_new_solution set inside the suspended path.

F* (Z3SeqEagerBudgetPR11356.fst) proves: `loop_exhausts` (O2), `round_fixpoint`/`iter_fixpoint` (O1): from the reset state with 2048 pending equations, after round 1 counter=1024, pending>0, new_sol=true and for every n rounds the state is unchanged (`witness_diverges`, O3). Mapping: `st.counter`=m_num_eager_eq_steps, `new_sol`=m_new_solution, `pending`=m_eqs.size() unsolved; each admitted iteration is assumed to solve one equation (the budget only gets used faster if normalization steps cost extra). ctx.inconsistent() assumed false.

## Assumptions / limits
No axioms/admits; only F* stdlib. Model abstracts solve_eq (assumed to remove at most one equation per budget step) and assumes the suspended push->propagate path reaches theory_seq with a non-empty pending list; that reachability is NOT mechanically verified. This is not a proof about C++ execution; a dynamic reproduction was not run (PR code must not be built). Verdict is "counterexample" at model level; maintainers should confirm with a test (assert 2048+ seq equalities, interrupt check, then push).

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit; /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include (base)/fstar --z3rlimit 10 --cache_dir cache --odir out Z3SeqEagerBudgetPR11356.fst
