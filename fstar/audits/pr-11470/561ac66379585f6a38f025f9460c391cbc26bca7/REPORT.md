# F* audit of PR 11470 at 561ac66379585f6a38f025f9460c391cbc26bca7 (base 710b259c)

Scope (partial): 3 changed functions, selected from src/opt/opt_context.cpp, src/opt/opt_nlsat.cpp.
1. context::maximize_in_cone / maximize_objective_in_cone: Pareto soundness. The final model dominates the model passed in on every objective, and any failure keeps the previous model.
2. nlsat_opt::search_models step loop: the `for(;;)` halving loop that picks `best+step < sup` terminates and satisfies the guard when best < sup.
3. Minimization orientation (term negation): order is preserved.

Obligations: all three **proved** in Pr11470ConeAudit.fst (F* 2026.09.27, Z3 4.13.3 pinned backend, z3rlimit 10). No counterexample was sought-and-found; no witness was established.

Mapping: models are abstracted to vectors of objective values oriented for maximization (`vals`). `run` mirrors the break-on-failure loop in maximize_in_cone. `step` takes the candidate only if it is at least cur in every coordinate; the C++ guarantees this by adding mk_ge(i, mdl) for all i to the hard constraints, plus a separate check that candidate satisfies all assertions. Obligation 2 models step/gap as positive rationals n/d and p/q; the halving loop doubles d.

Assumptions (not proved): nlsat_opt::maximize returns a model satisfying its hard constraints (the cone constraints) when it returns l_true with m_attained. The C++ re-checks the original assertions on the candidate but not the cone constraints themselves. Exactness of algebraic comparisons in mk_ge, rlimit and cancellation handling, and the in-fragment (NRA) check are not modeled.

Exclusions (not audited): the rest of the search_models changes (the doubling-step/refutation interplay `refuted`/`attained` state machine, soundness of `s.check(probe)` assumption literals and the claim that l_false only refutes the step), probe_unbounded plumbing, the rlimit scope/cancel re-raise logic, opt_pareto.cpp loop integration (num_improvements==1 trigger), opt_params.hpp, opt_context.h, and the tests in src/test/opt_pareto.cpp.

Not mechanized: C++ execution, memory safety, AST plumbing, nlsat correctness. This is a semantic source audit of a model, not verification of the C++.

Reproduce:
/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir c2 --odir o2 Pr11470ConeAudit.fst
