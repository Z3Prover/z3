# F* audit of PR 11547 (head c49bfb41ade57932b9f49b416b9f6a701ffbfde9, base c79e8787949d31c3559371ba307f2dda2d2b3018)

Partial scope: 53 files changed; audited 3 behaviors: (1) smt_tactic l_false case (src/smt/tactic/smt_tactic_core.cpp, head sha256 8029c32c...a370, ~L250-275), (2) then_simplifier::reduce skip of non-proof children (then_simplifier.h), (3) dependent_expr_state_tactic early no-op (dependent_expr_state_tactic.h).

Obligations (abstract model in Z3ProofModeNoop.fst):
- O1 PROVED: in proof mode a goal is closed to false only with a proof whose fact is false (or already closed).
- O2 PROVED: absent / non-false certificate leaves goal unchanged (no fabricated 'asserted false').
- O3 PROVED: without proofs, behavior unchanged.
- O4 PROVED: skipping unsupported children preserves any invariant preserved by supported children.
No counterexample searched-for was established.

Assumptions: the model abstracts goals/proofs to flags; proof validity of Proof(...) is an input hypothesis; m.is_false(get_fact(pr)) is modeled as fact_is_false. Not mechanized: C++ execution, AST plumbing, memory safety, dependency/model-converter handling, unsat-core handling, the m_fail_if_inconclusive checks, the l_undef branch, and whether if_no_proofs wrappers preserve goal state in the other ~50 files. Behavior concern noted manually only: in l_false with proofs enabled but missing proof, the goal is returned unchanged and unsat_core/dependencies are untouched (sound, but possibly less simplification).
Excluded: all other changed tactic files (dt2bv, bit_blaster, fpa2bv, purify_arith, horn, nlsat, qsat, etc.), tests, and docs.

Reproduce: see verification_log. Tools: F* 2026.09.27, Z3 4.13.3 (pinned independent backend).