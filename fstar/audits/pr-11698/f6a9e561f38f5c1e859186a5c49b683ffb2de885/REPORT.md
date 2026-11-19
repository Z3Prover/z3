## Scope
Base 1a1d88dd, head f6a9e561. Changed function audited: arith_rewriter::mk_le_ge_eq_core (src/ast/rewriter/arith_rewriter.cpp, lines ~764-772 and ~896). Excluded: src/test/arith_rewriter.cpp, examples/python/test_division_congruence.py, .github/workflows/ci.yml, and downstream behavior of cancel_monomials/is_neg_poly.

## Change
Old guard: m_arith_ineq_lhs || m_arith_lhs for all kinds. New: arith_lhs = m_arith_lhs || (kind != EQ && m_arith_ineq_lhs), used in cancel_monomials and the is_neg_poly branch.

## Obligations (all proved)
1. For EQ, new guard == m_arith_lhs.
2. For LE/GE, new guard == old guard (no regression).
3. The only differing inputs are EQ with ineq_lhs && !arith_lhs, where the new guard is false.

Intended property: arith_ineq_lhs applies only to inequalities. Environment assumption: kind is one of LE/GE/EQ and the flags are constant during the call. Note: the PR title says WIP and mentions division instability; this change does not address any division-specific behavior, which was not audited. Behavior change: equalities previously normalized with arith_ineq_lhs alone no longer are; this is the intended fix, but its effect on solver completeness/performance is not verified.

## Correspondence
F* op_kind/bool model the C++ enum and flags; manual review only for C++ semantics. No assumptions beyond the F* stdlib and Z3 4.13.3 backend.

## Reproduce
See verification log.