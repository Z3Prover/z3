# F* audit PR 11547 @ 1a44188e62a3b6dc7abf850f1153a1e502be6bd6 (base 840eedc2)

Scope: 3 changed behaviors, abstract model, 6 obligations (proved):
1. smt_tactic_core.cpp l_false (~L253): throw in proof mode unless pr's fact is false (O1, O2).
2. dependent_expr_state_tactic.h (~L133): early return of input when proofs enabled and simplifier lacks proof support (O3, O4).
3. then_simplifier.h reduce: skip children lacking proof support in proof mode; invariant preserved (O5).

Source hashes (sha256, contents API at head): then_simplifier.h 4acbf0bc..., dependent_expr_state_tactic.h 41d48d4d..., smt_tactic_core.cpp d1926c1f..., tactical.cpp 8ca89fb0...
Model .fst sha256 f8596ec9cb1d8fc225452793683b8a3fc9ea7c570a4576fd849dbf0fce8be8af.

Correspondence: goal = (proofs_enabled, id); pr = absent or fact-is-false flag; simplifiers = supports_proofs + step. Not modeled: proof term validity, rewriter exceptions, unsat_preserved/core handling, memory/threads.
Assumptions: per-child invariant preservation (all_ok) for supporting children is assumed in O5 (hypothesis, not proved for C++). Only F* stdlib/prelude inherited; no base modules imported.
Observation (manual, unproved): then_simplifier::supports_proofs() now always returns true, and skipped children in proof mode silently leave goals unchanged (sound for equisatisfiability only; completeness may drop). Also a pure whitespace change in fm_tactic.cpp.
Exclusions: ~45 per-tactic fail_if_proof_generation edits, par_and_then_tactical (tactical.cpp), tests, fstar/audits files, tactic docs, and the base..head compare's many unrelated .github changes.
Versions: F* 2026.09.27, Z3 4.13.3. No counterexample found; C++ execution not verified.
Command: fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include fstar --z3rlimit 10 --cache_dir cache --odir out Z3PR11547Head2.fst (timeout 120; exit 0)
