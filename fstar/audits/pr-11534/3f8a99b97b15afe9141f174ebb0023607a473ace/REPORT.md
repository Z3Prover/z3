# F* audit PR 11534 @ 3f8a99b97b15afe9141f174ebb0023607a473ace (base 605d1d83)
Scope (partial): src/solver/solver2tactic.cpp operator() (changed guards: line 109, l_false 140-154, l_undef 173). Source sha256 head 1ddcd93a..., base b35a6b8b....
Obligations (all proved, abstract guard model):
- O1: with proofs enabled, UNSAT success implies non-null backend proof with false fact and every input assertion proof present with fact == form; otherwise throw.
- O2: proof-mode UNKNOWN leaves goal unmodified.
- O3: with proofs disabled, UNSAT never throws and UNKNOWN behaves as before (reset iff !core).
Also: line 109 throws before the solver runs when proofs and assumptions coexist (entry model, not separately lemma'd).
Correspondence: proofs are abstracted to booleans (null / fact-is-false / input-proof-matches); outcomes abstract goal mutation.
Assumptions: m.get_fact, m.is_false, is_false correctness; none inherited from base F* modules beyond FStar.List.Tot.
Not verified: expr_safe_replace substitution correctness (a backend proof leaf not matching any clause, e.g. rewritten by backend, stays unsubstituted and is not checked here), 1-1 goal/clause correspondence (SASSERT only, absent in release builds), memory safety/refcounting, get_consequences.cpp test, other tactic files, audit-file changes in PR. No counterexample found; this is not a proof of C++ execution.
Reproduce: see verification.log.
