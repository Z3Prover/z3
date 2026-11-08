# F* audit of PR #11547 at e7df2161bf68b29352f835446549192bc86c9d0f (base 840eedc27e6dd6bf395500b7d78c4e0a304d8172)

Scope: partial. Three changed behaviours, one or two obligations each, modelled as control flow only. This is not verification of C++ execution, memory safety, or the whole solver.

## Obligations (all proved in F*; no counterexample sought succeeded because none was found by inspection)
1. `smt_tactic_core.cpp` l_false branch: with proofs enabled, the tactic throws unless a proof exists and its fact is `false`; so `assert_expr(false, pr)` never receives a null/mismatched proof (the removed fake `mk_asserted(false)` fallback). Proofs off: behaviour unchanged (`o1`, `o1b`).
2. `then_simplifier.h::reduce`: under proofs, unsupported sub-simplifiers are skipped, so every executed step supports proofs; without proofs all steps run (`o2`, `o2b`). `supports_proofs()` now returns true unconditionally, which is consistent with this skipping. `dependent_expr_state_tactic.h` line 133 already guards the same way.
3. No-op guards in `horn_tactic`, `nlqsat`, `ctx_solver_simplify_tactic`, `add_bounds_tactic`: with `proofs_enabled()` goal is returned unchanged; otherwise the implementation runs (`o3`, `o3b`).

## Correspondence / assumptions
Model: option fact for `pr` and `m.get_fact(pr)`; list of steps with a `supports` flag; goal with a proof flag. Assumes `m.is_false(get_fact(pr))` correctly characterizes a proof of false, and that skipping a simplifier preserves equivalence with proofs (identity step). Inherits F* standard library only; no base modules imported.

## Manual review notes
Skipping is sound but silently weakens preprocessing under proofs (completeness/behaviour change, not soundness). The l_false throw also fires on cancellation/clause-proof paths lacking a proof: intended fail-closed behaviour. Source SHA-256 (head, fetched via contents API): smt_tactic_core.cpp (l.250-275) d1926c1f...5977ae7; then_simplifier.h (l.62-80) 4acbf0bc...94d8d; dependent_expr_state_tactic.h (l.127-145) 41d48d4d...8fd355.

## Excluded
Other changed files: sat_tactic, unit_subsumption, diff_neq, qfnra_nlsat (whitespace-only), solver2tactic and further src/tactic files beyond the first patch listing, examples/python/test_real_power.py, fstar docs and prior audit artifacts, remaining no-op guards not named above.

## Reproduce
`fstar.exe --smt z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out --include fstar Z3PR11547Head3.fst` (F* 2026.09.27, Z3 4.13.3). Exit 0.
