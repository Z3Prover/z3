# F* audit PR #11562 @ e04a0074c29f877855649d6b2710349cb78f5503 (base 5bab89972dc48c2d5560b1e6e0df8297bd85e2ea)

PR open at this SHA; no `fstar-nfv-audit:e04a0074...` marker existed (earlier SHAs audited only). Head sources fetched via contents API; sha256: smt_internalizer.cpp 08f9e3293f316aaf15b9dc01f870c26a8b4ee3c889372a97e2fe2be67416bebc; smt_context.cpp 21c4658e496c90569a8cf4893b2b3cb0b016b3555c7f48576c8a70fab81dbd94.

## Scope (partial)
Audited: `context::internalize_quantifier` (smt_internalizer.cpp L655-676) and `context::undo_mk_bool_var` (L1106-1122), interaction with `quantifier_manager::add/del` (base src/smt/smt_quantifier.cpp L166-203, `del` does `m_quantifiers.pop_back()`). The latest commit ("Fix polarity check for forall quantifiers") changed registration to `is_forall(q) && polarity != l_false`, inside `if (!b_internalized(q))`.

## Obligations
- O1 (intended: a forall that occurs positively is registered with the quantifier manager and flagged for instantiation): **COUNTEREXAMPLE (model)**. Q first internalized with polarity l_false (e.g. via not-gate flip `~l_true` in a clause `(or (not Q) c)`), creating a bool var but no add/flag. A later internalization with l_true hits `b_internalized(q)` and skips the whole registration block; `set_quantifier_flag` is only called there (single site), so `assign_quantifier` is never invoked when Q is assigned true; Q is never instantiated. Verified as `w1` in the F* model.
- O2 (intended: undo of bool var keeps manager in sync): **COUNTEREXAMPLE (model)**. `undo_mk_bool_var` calls `m_qmanager->del` for every forall, but `del` pops the last element of m_quantifiers; negative-only foralls were never added. Scope: Q1 positive in base scope, Q2 negative-only in a pushed scope, pop: Q2's undo pops Q1's entry (`w2`: mgr=[] while Q1 stays internalized). Then `has_quantifiers()` can be false (smt_context.cpp ~L4104 skips quantifier checks on l_true), risking an unsound `sat`. On an empty vector, pop_back is UB (`w3_pre`).
- O3: not attempted (budget); ordering/trail of m_quantifier_positive/negative left unchecked.

## Correspondence and assumptions
F* `internalize_forall` mirrors the branch guards `!b_internalized(q)`, `is_forall && polarity != l_false`; `undo` mirrors `del` pop_back. bvars list models m_b_internalized_stack (scope undo), mgr models m_quantifiers. Reachability of the polarity orders relies on manual reading that not-gates under gate_ctx pass `~polarity` and gate args pass l_undef/l_true; not mechanized. A real Z3 run was NOT performed (PR code not built per policy); a regression test on the C++ is recommended (e.g. `(assert (or (not (forall ...)) c))` then `(assert (or (forall ...) b))`, and push/pop variant). Suggested fix: set registration also when a forall later gains a non-false polarity (track registration separately from bool var existence), and guard `del` in undo with registration state.

## Exclusions
Call-site edits (arith_eq_adapter, seq_regex, smt_context.cpp, smt_model_finder, theory_array_base, theory_ff, theory_lra), nnf-based `internalize_quantifier_polarity`, proof terms, src/test/smt_context.cpp, prior audit artifacts in the PR. Semantic model only; not verification of C++ execution or the solver.
