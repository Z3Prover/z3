# VerCors C++ audit, PR 11477, head abaaa27abbb0c3b942ae72e02f18d871741f5f3a (base 02d9a80f429b81d423bf137bca870dc01b39187c)

## Changed files
- src/opt/opt_context.cpp (+112/-8)
- src/opt/opt_context.h (+1)
- src/opt/opt_params.hpp (+1/-1)
- src/test/opt_pareto.cpp (+112/-1), test code, excluded

## Candidate functions
1. context::maximize_objective_in_cone_smt (new): inconclusive. It uses lambdas capturing by reference, solver::scoped_push RAII, virtual calls on opt_solver, rational/inf_eps arithmetic, model_ref reference counting, expr_ref temporaries and exceptions. Candidate obligations were: (a) best_value never decreases, (b) mdl is replaced only by a model that satisfies every assertion, (c) the loop on improvement terminates or returns. None can be stated over the real types in VerCors C++ without invented contracts for the changed callees (s.check_sat, s.maximize_objective, model evaluation). Inventing those contracts would assume the desired result, so I abstained.
2. context::maximize_in_cone (changed guard and loop): inconclusive. Same dependence on Z3 object model, scoped_rlimit RAII, try/catch of z3_exception and `any_of` with lambdas. VerCors does not support these.
3. Excluded: the opt_params.hpp parameter description change (no logic), the opt_context.h declaration, and the test file.

## Source evidence
Full-source snapshots at the head/base SHAs were not extracted into standalone units. No source hashes were recorded because no extract was produced.

## Non-vacuity, arithmetic correspondence
Not applicable: no unit was produced. The arithmetic uses unbounded rationals, so a machine-integer comparison does not apply, but this was not checked.

## Observation (unverified, not a finding)
In the loop, an `improvement` that is non-strict (f >= supremum) is re-asserted without a push, so constraints accumulate within the scoped_push. This is intended as a monotone strengthening, and I did not check it.

## Reproduction
/tmp/gh-aw/vercors/vercors --lang cpp --backend silicon --dev-total-timeout 60 (unit.cpp). No unit was run.