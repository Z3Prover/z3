# F* audit PR 11675 @ a9ecfe6d8582aa2c1b43ee46806e6d0c7c458015 (base d72de58d9e36009f1397377cd185342474c8ecfb)

Sources fetched via the contents API: src/math/lp/nla_core.cpp, head sha256 ea8ed3e05fe1f6d2a8ba3fb7b944360cc591ee9d579bd679e3d9812b4510bcfd (1343 lines), base sha256 bf9833a3bc296691e46d0f2b0a6eeb43152a877424990a7831b8a9a239f2dd5c (1351 lines).

## Changes audited
1. core::check_monic (head lines 170-181): the previously disabled guard `if (!is_relevant(m.var())) return true;` is now live. is_relevant(v) = !m_relevant || m_relevant(v) (nla_core.h:249).
2. core::check (head lines ~1095-1097): the final fallback under `no_effect() && arith_nl_nra() && level>=2` now calls bounded_nlsat() (lines 1122-1158: max_conflicts=100, rlimit 100000, backoff update) instead of an unbounded m_nra.check().

## Obligations (PR11675_NlaCore.fst)
- O1 proved: irrelevant monics always pass check_monic.
- O2 proved: for relevant monics the result equals the old one; the new check accepts a superset of the old one.
- O3 proved under assumption A: the bounded result is the unbounded result or l_undef; l_undef only on budget exhaustion.
- Incompleteness witness (model level, not a soundness counterexample): a definite old answer can become l_undef.

## Assumptions / not proved
- A: nlsat cutoffs never fabricate sat/unsat. This was justified by reading bounded_nlsat; it is NOT mechanized.
- The new call is no longer gated by should_run_bounded_nlsat(); the backoff only updates after the call, so every level>=2 call runs with budget.
- With O1, nla may accept a model where an irrelevant monic violates its product. This is sound only if the SMT core's relevancy contract guarantees irrelevant monic vars are unconstrained; NOT verified.
- Callers' handling of l_undef without lemma was not reviewed.

## Mapping
F* booleans model relevant, int_nonint, prod_eq; lbool models nlsat results. Memory safety, AST plumbing, m_nra internals are not covered.

## Exclusions
src/test/nla_intervals.cpp (test_irrelevant_monic_is_ignored) not audited. Full PR coverage is not claimed.

## Reproduce
fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out PR11675_NlaCore.fst
