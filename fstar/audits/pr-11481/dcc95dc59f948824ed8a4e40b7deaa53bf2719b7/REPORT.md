# F* audit of PR 11481 @ dcc95dc59f948824ed8a4e40b7deaa53bf2719b7 (base d687b6a18d03834ec2bfaa72647890c444748a09)

Source hashes (sha256, fetched via contents API): head inc_sat_solver.cpp 81de82b9...b8e, base 109fed94...e094; head sat2goal.h bc4307bd...c98bcf... (see below), base 555ad202...be5094. Full: head_inc_sat_solver.cpp 81de82b96a333f82c5258f1ffc4347425c54b9eeca74609c17ebdf5575554b8e; base 109fed9429c59541cf804722165f9056a27d18b67735b6f209cad5692e5be094; head sat2goal.h bc4307bd145c8395c6e3b9b63bd09b3b8a7a7353d63dd5685a4b11f768c98bcf; base sat2goal.h 555ad20259447bd6999913da32c054f5cf966211bd0a425e64f8011d9c7228d0.

## Changed behavior
- src/sat/tactic/sat2goal.h (~L64-65): `mc::shrink(n) { if (n < m_var2expr.size()) m_var2expr.shrink(n); }`.
- src/sat/sat_solver/inc_sat_solver.cpp `pop` (~L306-310): after `m_solver.user_pop(n)`, `if (m_sat_mc) m_sat_mc->shrink(m_solver.num_vars());` and `m_internalized_converted = false;` (previously a commented-out `// ? m_internalized_converted = false;`).

## Intended property / assumptions
Property: after pop, no SAT variable numbered >= solver num_vars retains an expression in m_var2expr, so reused variable numbers cannot be read back under stale atoms; lower variables are untouched.
Assumptions (manually reviewed in base source, not mechanized): sat::solver::user_pop calls gc_vars -> shrink_vars(max_var) so num_vars() after user_pop is the new variable bound (src/sat/sat_gc.cpp L400-455); variables < num_vars keep meaning across the pop; sat2goal::mc::insert asserts the slot is empty (SASSERT(!m_var2expr.get(v))), which stale entries would violate in debug builds.

## Obligations (F* module Z3SatPopShrink, model of m_var2expr as seq (option nat))
1. O1 proved: i >= n ==> get (shrink v n) i == None.
2. O2 proved: i < n ==> get (shrink v n) i == get v i (no loss of live mappings).
3. O3 proved: shrink never grows the vector; n >= size gives identity (guard correctness, no out-of-range shrink).
Witness (base behavior): vector with var 2 -> Some 5, new num_vars = 2: without shrink get 2 == Some 5 (the stale-name bug); with shrink get 2 == None. This confirms the described bug mechanism exists in the base and is removed by the head; it is not a counterexample to the PR.

## Not covered / manual review
Excluded: src/test/inc_sat_solver_pop.cpp, src/test/CMakeLists.txt, src/test/main.cpp (tests/plumbing). Not modeled: m_cached_mc / m_mcs interaction (m_mcs.push_back(m_mcs.back()) copies may hold pre-pop converters sharing the m_sat_mc pointer), the unflushed-smc ordering (flush_smc before pop vs. variables created in the popped scope), generic_model_converter hidden decls added via aux insert are not removed by shrink, memory safety, and the whole optimizer effect. m_internalized_converted=false forces re-conversion of cached formulas on next get_assertions; correct by inspection (only affects performance).

## Reproduce
See cmd.txt in verification log; F* 2026.09.27, Z3 4.13.3 (pinned backend).