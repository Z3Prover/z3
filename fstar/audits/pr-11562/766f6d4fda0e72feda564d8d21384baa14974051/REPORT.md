# F* audit PR #11562 @ 766f6d4fda0e72feda564d8d21384baa14974051 (base 5bab89972dc48c2d5560b1e6e0df8297bd85e2ea)

Scope (partial): one changed function, `asserted_formulas::reduce()` (src/solver/assertions/asserted_formulas.cpp, new line after `m_reduce_asserted_formulas`): `if (has_quantifiers() && !invoke(m_nnf_cnf)) return;` before `m_flatten_clauses`. Excluded: the regression tests in src/test/smt_context.cpp (not executed), the array/lambda rewriter and ITE lifting themselves, nnf_cnf_fn's C++ implementation (skolemization, CNF, definitions), pattern/macros interplay, and performance.

Property: if a semantics-preserving rewrite introduces negated quantifiers after the first NNF pass, re-running NNF yields an equivalent formula in negation normal form. Assumption: the rewrite step is semantics preserving (the bug in #11556 is a form/NNF issue, not a semantic one); the first-order model uses abstract atoms and quantifiers over a Boolean domain; C++ nnf is modeled by the textbook NNF transform.

Obligations (all proved, NnfRestore.fst):
1. nnf_is_nnf: output of nnf is NNF (no negated quantifier/compound).
2. nnf_sound / restore: nnf preserves truth in every environment; applied after any equivalence-preserving rewrite r gives an equivalent NNF formula.
3. nnf_idem: on already-NNF input the extra pass is the identity (no regression on formulas not disturbed).

Not established: that m_nnf_cnf's should_apply/C++ behavior equals the model; that later passes (flatten_clauses) don't reintroduce negative quantifiers; that this fixes #11556 in the real solver; no counterexample was sought for C++ execution. Semantic model only; not mechanized verification of C++, memory safety, or whole solver. Also note: the pass runs after m_reduce_asserted_formulas with eliminate_and=true, so nnf_cnf may behave differently from the first call; unmodeled.

Versions: F* 2026.09.27; Z3 4.13.3 (pinned independent backend). Command (fresh cache): `timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out NnfRestore.fst`. Exit 0. No admit/assume. Only inherited trust: F* core/standard library (FStar.Classical).
