fstar-nfv-audit:2355f51d73dd72cffe2ae4e19e0ddde91e9b7e7b

PR 11334, base ac71ae716c0e6d14aef5529c21006260c57d3784, head 2355f51d73dd72cffe2ae4e19e0ddde91e9b7e7b. Source: src/solver/assertions/asserted_formulas.cpp (head sha256 of decoded content 6bfcf1bda3c602b8828d0382896ae1aa4fa254a66156a81c153cde2e2d75d19b), flatten_clauses lines 411-466, can_distribute lambda lines 434-438.

Change: can_distribute(e) now also requires m.is_not(e,d) && d->get_ref_count()==1 in addition to occurrence count == 1.

Obligations (all proved):
1. distribute_sound: (or a (not (or b1..bn))) is equivalent to the conjunction over i of (or a (mk_not bi)), matching the C++ rewrite loop.
2. rewrite_sound: replacing one clause by its distributed clauses inside a clause set preserves the conjunction (semantic equivalence of the asserted set).
3. guard_refines / guard_pass / guard_reject_shared: new guard implies old guard (rewrites performed are a subset of the base ones); an unshared negated disjunction (rc 1) still passes, and a shared one (rc 2) is rejected.

Correspondence: form models Boolean AST (V atoms, Not, n-ary Or); mk_not mirrors the lambda; ref count is modeled as a natural number parameter.

Assumptions: the reference count of d is an accurate over-approximation of sharing (C++ AST manager invariant, not verified); the m.is_or binary-or arguments are modeled as the two-element Or; the symmetric disjunct-order branch follows from commutativity of ||; proofs disabled (m.proofs_enabled() early return). Standard F* library only, no base modules imported.

Not established: that rc==1 captures all sharing (e.g. rewriter caches, smt::context internalization), the O(N+K) clause-count claims, memory safety, the tests in src/test/flatten_clauses.cpp, and C++ execution. Soundness of the PR is independent of these since only a restriction of an equivalence-preserving rewrite was added; a wrong rc can only affect performance.

Excluded changes: src/test/flatten_clauses.cpp, src/test/CMakeLists.txt, src/test/main.cpp (tests/plumbing), comment edits. The simplifier variant src/ast/simplifiers/flatten_clauses.h is unchanged by the PR.

Reproduce: cd fstar-audit; fstar.exe --smt z3 --z3version 4.13.3 --z3rlimit 10 --include fstar --cache_dir cache --odir out FlattenClausesPR11334.fst
Tools: F* 2026.09.27, Z3 4.13.3 (pinned release).