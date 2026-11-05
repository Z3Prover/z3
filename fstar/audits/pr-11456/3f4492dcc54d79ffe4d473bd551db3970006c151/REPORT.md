# F* audit PR 11456 @ 3f4492dcc54d79ffe4d473bd551db3970006c151 (base dad37c85122de03ec838d3d8528de1f341ead036)

Tools: F* 2026.09.27, independent Z3 4.13.3 (pinned release backend; no PR-built Z3).

## Scope
Audited: `theory_finite_set::are_forced_distinct` and the new guard in `new_diseq_eh` (src/smt/theory_finite_set.cpp, ~lines 276-330; file sha256 65e7a22f...a7ed30 of the contents-API snapshot at head).

Obligations (all proved, 0 counterexamples):
1. a's class contains set.empty and a relevant assigned atom `(x in b)` is true => a != b (`ob_empty`, `ob_empty_sym`).
2. Same element root, opposite assigned truth values for membership in a and b => a != b (`ob_conflict`).
3. In case 2 the skipped extensionality axiom's existential witness exists (`ob_witness_extensional`), so skipping loses no consequence for the current assignment.
(plus a sanity lemma showing a false fact is not a witness for rule 1.)

## Correspondence
`fset` from base `Z3FiniteSetTheory` models sets as membership predicates; `fact` models a relevant assigned `set.in` atom whose set argument has the root of a or b; element-root equality is modelled as element equality (congruence). `sound` states the assignment is consistent with a model.

## Assumptions / not mechanized
- Assigned atoms and e-graph equalities are consistent with a model (standard CDCL(T) invariant).
- Not proved: C++ execution, enode iteration, memory safety, relevancy handling.
- Manually reviewed only: when the check skips the axiom, `is_new_axiom` suppresses re-emission; both m_clauses and m_diseqs are trailed at the current scope, so backtracking undoes both together. The witness literals could in principle be undone only by backtracking past the current scope, which also undoes the suppression record; no unsound case found, but not mechanized. The skip is gated by the finite_set_reuse_witness param (I did not verify the param's definition/default in params since smt_params_helper.hpp is generated).

## Excluded (not audited)
theory_finite_set.cpp setop-parent change (`is_singleton` skip and `add_membership_axioms(..., n->get_expr())`), `is_beta_redex`, theory_array_full.cpp `instantiate_lambda_defaults` (lazy lambda default axiom, locality heuristic), finite_set_simplifier.cpp/.h, finite_set_tactic, smt_params_helper.hpp, tests, python scripts and result JSONs. The array lambda-default deferral is the highest-risk unaudited change (completeness/soundness of omitting default axioms for 'local' lambdas).

## Reproduce
See verification_log. Run from a directory containing the module, with --include fstar at the base checkout.