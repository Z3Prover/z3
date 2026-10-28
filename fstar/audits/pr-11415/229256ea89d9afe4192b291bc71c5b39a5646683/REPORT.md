# F* audit PR 11415 @ 229256ea89d9afe4192b291bc71c5b39a5646683 (base c698bae8)

PARTIAL scope: delta since previously audited head a9edd5ce, src/smt/smt_quantifier.cpp only (patch fetched via compare API; full function bodies not mechanically re-read). Three abstract obligations, each proved. No counterexample found.

Obligations (ArithWitnessAudit.fst):
- W1 witness merge: the fold ite(value<=v, value, v) in arith_quantifier_match over witnesses yields the minimum of candidates and is one of them (w1_min). PROVED.
- W2 add_arith_instance dedup+budget: budget never underflows (guarded by !budget), decrements only on a fresh emission, duplicates are free, idempotent (w2_budget, w2_idempotent). PROVED.
- W3 new guard `projected && is_zero(boundary)` returns before any instance; non-projected path unchanged (w3_no_zero_projected). PROVED.

Correspondence: ints model arithmetic values; lists model the instances/witnesses vectors; pointer equality of exprs modeled as equality. Assumptions: hash-consed expr equality is pointer equality; rewriter preserves value (not checked).
Excluded: get_arith_definitions, definition expansion in get_arith_bounds, the recursive chain transfer in arith_match (depth<4, chain_budget termination), deferred-witness bookkeeping, src/test/smt_context.cpp, and prior audit files. Soundness of substitution/transfer is manually unreviewed. Not verification of C++ execution or memory safety.
Reproduce: see verification log (fresh cache).