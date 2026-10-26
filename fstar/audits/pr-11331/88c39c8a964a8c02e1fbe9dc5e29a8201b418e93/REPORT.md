# F* audit of PR #11331 @ 88c39c8a964a8c02e1fbe9dc5e29a8201b418e93 (base a2fae73358e4a928da63d1c131e9fe2bbac8c855)

Scope (partial): 3 changed behaviors, selected obligations only. Semantic model audit, NOT mechanized verification of C++ execution, memory safety, or the whole solver.

## Selected functions / obligations
1. `seq::axioms::at_axiom` (src/ast/seq/seq_axioms.cpp ~L684): guard `is_numeral && is_unsigned && iv <= 1024`.
   - O1a proved: concrete branch emits <= 1025 units (`o1_bounded`); boundaries 1024 concrete, 1025/UINT_MAX/2^32 symbolic (`o1_boundaries`).
   - O1b proved: the symbolic fallback split s = pre ++ [s[i]] ++ rest, |pre| = i, is valid for any 0<=i<|s| (`split_ok`), so routing large indices there loses no semantics (model of the existing pre/tail skolem axiom, abstracted over lists).
2. `theory_seq::fixed_length` (theory_seq.cpp ~L556-580): `m_fixed` insertion moved after construction loop; loop polls `m.inc()`.
   - O2 proved: cancellation (fuel<lo) leaves the fixed flag unset (retry possible); completion marks it; retry with enough fuel completes (`o2_*`).
3. `theory_seq::solve_eqs` / `propagate` / `new_eq_eh` (seq_eq_solver.cpp L30-41, theory_seq.cpp ~L2862-2880, ~L3450): loops poll `m.inc()`; unprocessed equations raise `m_new_solution`; `new_eq_eh` no longer solves inline.
   - O3a proved: interrupted run neither drops nor invents equations (unsolvable ones are kept; kept set is a subset) (`o3_no_loss`).
   - O3b proved: interruption with remaining work sets the pending flag; sufficient fuel clears it (`o3_flag_on_interrupt`, `o3_complete`).
   - O3c proved: an interrupted run leaves a non-empty equation set, so the `is_solved` gate (`m_eqs.empty()`) in final_check_eh cannot yield FC_DONE/sat from an interrupted solve (`o3_interrupted_not_done`).

## Correspondence
Lists/fuel model `m.inc()` as a bounded poll budget; `run` models the solve_eqs scan (solved eqs erased, others kept; the real erase_and_swap reorders, which the multiset/membership statements do not depend on). `solvable` abstracts solve_eq's result. fixed_length model abstracts the axiom emission.

## Assumptions / manual review (not mechanized)
- solve_eq's own soundness is unchanged by the PR and not re-audited.
- Deferring equation reduction from new_eq_eh to propagate relies on context calling theory propagate (can_propagate returns true when m_new_solution) before final check; final_check_eh also runs simplify_and_solve_eqs. Manual reading found no issue.
- Observation (not a counterexample): `m_new_solution = false` was removed from `propagate()`; `simplify_and_solve_eqs` clears it only when loop completes. If ctx is inconsistent at entry the flag can remain set, causing a harmless extra solve after backtracking. m_new_solution is not trailed.
- Resource-limit behavior after cancellation (unknown results, push/pop reuse) is covered only by the PR's own C++ tests, not here.
- Inherited: F* standard library (FStar.List.Tot, Classical); no base fstar/ modules imported.

## Exclusions
src/test/seq_limits.cpp, src/test/main.cpp, src/test/CMakeLists.txt (tests/build only); `check_fixed_length` and `simplify_and_solve_eqs` loop-condition edits only covered via the O2/O3 models.

## Reproduce
`/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --cache_dir c --odir o --z3rlimit 10 Z3Pr11331SeqCancel.fst`
F* 2026.09.27, Z3 4.13.3 (release backend). Exit 0; no admit/assume. Source sha256 of module recorded by publisher manifest.
