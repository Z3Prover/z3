# F* audit PR #11673 @ b0a57dcfb2abe59981fedce2c37ed9013f4fc448 (base d72de58d)
Marker: fstar-nfv-audit:b0a57dcfb2abe59981fedce2c37ed9013f4fc448

Scope (partial): 2 changed functions in src/math/lp/lar_solver.cpp (head blob sha256 741b2742a163445deaf700195d490a9e9a319b7a63fef971404a50e9bd26e189): `maximize_term_on_tableau` (~L720-735) and `maximize_term(unsigned,...)` (~L1018-1040).
Excluded: src/test/opt_pareto.cpp (tests, not production); `adjust_integer_columns` and the whole simplex/pareto cone code; C++ execution, memory safety.

Obligations (all in Pr11673LpHeap.fst):
- O1 PROVED: if the pre-maximization backup is feasible (the SASSERT at maximize_term entry), restore_x + clear_inf_heap satisfies "heap = exactly the infeasible columns" (empty heap, all columns feasible).
- O2 PROVED (witness of pre-PR defect in the model): restore_x without clear can leave a stale inf_heap entry for a feasible assignment (heap invariant violated). It models the mechanism only; it is not a reproduction of the C++ assertion.
- O3 PROVED: on the path where maximize_term_on_tableau returns true (status not UNBOUNDED/CANCELLED) the weakened SASSERT is equivalent to the original, so the assertion is relaxed only for CANCELLED.

Correspondence: heap = m_inf_heap (lp_core_solver_base::clear_inf_heap, lar_solver::clear_inf_heap); x/lo/hi = r_x and column bounds; status enum = lp_status. restore_x also resizes in lar_solver (not modelled). 
Assumptions (manual review): backup_x copies all columns relevant; the backup was feasible and the heap matched it before the call; clearing the heap is sufficient because later feasibility code (find_feasible_solution) re-populates the heap from x (not modelled; the PR's regression test exercises this). Other callers of maximize_term_on_tableau / other CANCELLED exits keeping stale heap not checked.
Counterexample: none established. Verdict is `proved` only for the modelled obligations; the abstraction does not mechanize C++.

Reproduce: fstar.exe --smt z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include fstar --cache_dir cache --odir out Pr11673LpHeap.fst
