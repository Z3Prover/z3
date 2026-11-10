# F* audit, PR 11638 at %s (base 8927ff98ea8eae56021f8e8ea874a9465ea6a257)

Verdict: inconclusive. No F* proof was attempted or checked; no counterexample was established.

## Scope
The PR reverts #11562 ("Handle quantifier polarity during SMT internalization"). It also deletes the F* audit bundle fstar/audits/pr-11562/f66a77aec068354a90307d8aba41468e0b757cba/.
Changed C++ (partial coverage only): src/smt/smt_context.cpp (assign_quantifiers ignores quantifiers assigned false; internalize/internalize_formula calls drop the l_true/l_false polarity argument; m_cached_generation now also inserted for non-forall quantifiers), src/smt/seq_regex.cpp, src/smt/arith_eq_adapter.cpp, src/smt/smt_conflict_resolution.cpp (to_app(fact) cast, debug trace only).

## Obligations considered (all inconclusive)
1. Negatively-assigned quantifiers are safe to ignore (the restored comment says all universal quantifiers have positive polarity in the input). The revert's own premise is that this was insufficient, which is why #11562 was a fix for "unsat reported as sat". Without the polarity argument, a negative occurrence of a forall/exists is not Skolemized during internalization. Checking this needs an F* model of the quantifier-polarity invariant and a reachable input; none was built.
2. Dropping the polarity argument in the reinternalization paths (reassert units, init_clause, restored atoms) leaves the polarity unknown. No model was built.
3. The cached generation change in smt_context.cpp. No model was built.

## Assessment
This is a revert of a soundness fix. The reintroduced assumption (quantifiers assigned false can be ignored) is a plausible regression risk. Reviewers should confirm that the original issue's regression test still passes after the revert, or that the issue is otherwise fixed. This is a manual-review flag, not a checked result. A reachable witness was not constructed or run, because executing PR code is forbidden.

## Not covered
All other files in the diff (the deleted audit artifacts) and C++ execution semantics, AST plumbing, and memory safety. Semantic F* models are not mechanized verification of C++.

## Assumptions
None used; no proof modules were published. Tool versions were not recorded because fstar.exe was not run.
