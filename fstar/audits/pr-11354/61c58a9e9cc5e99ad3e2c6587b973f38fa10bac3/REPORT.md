# F* audit of PR 11354 at 61c58a9e9cc5e99ad3e2c6587b973f38fa10bac3 (partial scope)

Source: `src/ast/rewriter/array_map_coherence.h` at head (blob d1d69e44, decoded sha256 f575315f...cee5cce), lines 157-175 (domain-size guard in `check_array_map_coherence`). Base 9dbe8c83. Tools: F* 2026.09.27, Z3 4.13.3 (pinned independent backend).

Obligations (all in AmcGuard.fst):
1. step_exact: `s > n || ds > n/s` is equivalent to `ds*s > n` (proved).
2. no_overflow_step: an accepted step yields `ds*s <= n`, so the uint64 product cannot wrap when n is a vector size (proved).
3. loop_correct: the loop returns the exact product of finite domain sizes iff it is <= n, otherwise `exceeds` is set only when the product truly exceeds n (proved).

Refutation: no counterexample sought beyond these arithmetic properties; none found. The earlier audit of head 6eb4f3f5 (coverage-guard witness) is a separate revision and is not reused.

Correspondence: n = indices.size(); sizes = finite domain->get_num_elements() (assumed >= 1); non-finite or size > n sets exceeds (modelled as exceeding, which is the C++ behaviour; the model covers only the finite, `s <= n` branch plus the `s > n` clause). Uninterpreted domains are skipped as in C++. Unbounded nat models uint64; obligation 2 justifies no wrap.

Excluded / not verified: collect() store-index collection and its equality explanation soundness; definition propagation and e-graph root handling; the internalize/propagate/select callbacks; array_axioms.cpp, array_solver.cpp/.h, theory_array_full.cpp/.h, src/test/smt_context.cpp; whether `domain_size <= n` branch (select instantiation at store indices) is semantically sufficient for coherence (not proved: requires index-distinctness modelling); memory safety and C++ execution; prior audit artifacts in the PR.

Verdict is inconclusive overall: arithmetic of the guard proved, semantic coherence property not covered.

Reproduce: `cd fstar-audit && timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out AmcGuard.fst`
