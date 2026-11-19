## Scope
Head e577ff30d4c408d7a315d3a9bc5338b3c3fb3431 (base 684853cb). Sources read via contents API; sha256 of fetched files: tactic/dependent_expr_state_tactic.h 41d48d4d..., ast/simplifiers/then_simplifier.h 99a11afe..., smt/tactic/smt_tactic_core.cpp d1926c1f..., tactic/tactical.cpp 8ca89fb0....

## Obligations
- smt_tactic_core.cpp L253-254: O1 success in proof mode implies proof of false; O2 no-proof unchanged; O3 missing/non-false proof throws. Proved.
- tactical.cpp L619-628 par_and_then: O4 proof mode always throws; O5 non-proof path unchanged. Proved.
- dependent_expr_state_tactic.h L133: O6 in proof mode only supporting simplifiers modify the goal; O7 unchanged otherwise. Proved.
- then_simplifier.h L74: O8 skipping unsupported children preserves an invariant if supporting children preserve it. Proved.

## Assumptions / correspondence
Goals abstracted to proofs flag + id; simplifier steps are opaque functions; proof validity of supporting simplifiers and of the smt proof object is assumed, not verified. Throw models tactic_exception. Only F* standard library assumed; no admit/assume.

## Exclusions
Per-tactic fail_if_proof_generation migrations (~45 files), src/test changes, examples, docs. Not verified: C++ execution, memory safety, AST plumbing, the whole solver.

## Reproduce
See verification log.