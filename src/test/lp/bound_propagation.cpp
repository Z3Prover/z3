/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    bound_propagation.cpp

Abstract:

    Unit tests for the Farkas coefficients that lar_solver attaches to the
    premises of LP bound propagation (lar_solver::explain_implied_bound).

--*/
#include <map>
#include <iostream>
#include "util/debug.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_bound_propagator.h"

namespace lp {

// Receives the weighted premises that lar_solver::explain_implied_bound delivers
// through lp_bound_propagator::consume.
struct farkas_explanation_collector {
    lar_solver& m_solver;
    vector<std::pair<mpq, constraint_index>> m_premises;
    farkas_explanation_collector(lar_solver& s) : m_solver(s) {}
    lar_solver& lp() { return m_solver; }
    const lar_solver& lp() const { return m_solver; }
    bool bound_is_interesting(unsigned, lconstraint_kind, const mpq&) const { return true; }
    void consume(const mpq& a, constraint_index ci) { m_premises.push_back({a, ci}); }
    bool add_eq(lpvar, lpvar, const explanation&, bool) { return false; }
    bool is_equal(lpvar u, lpvar v) const { return u == v; }
};

typedef vector<std::pair<mpq, constraint_index>> premises_t;

// Returns the coefficient recorded for constraint ci; fails if ci is not a premise.
static mpq farkas_coeff_of(premises_t const& premises, constraint_index ci) {
    for (auto const& [a, c] : premises)
        if (c == ci)
            return a;
    ENSURE(false);
    return mpq(0);
}

// The weighted premises must form a Farkas certificate of the implied bound:
// orienting every premise as lhs <= rhs (GE constraints are multiplied by -1)
// and adding them with their coefficients must give
//     x_j <= bound     for an upper bound, or
//    -x_j <= -bound    for a lower bound.
static void check_farkas_certificate(lar_solver const& ls, implied_bound const& ib, premises_t const& premises) {
    std::map<lpvar, mpq> lhs;
    mpq rhs(0);
    ENSURE(!premises.empty());
    for (auto const& [a, ci] : premises) {
        ENSURE(a.is_pos());
        auto const& c = ls.constraints()[ci];
        ENSURE(c.kind() == LE || c.kind() == GE);
        mpq sign = c.kind() == LE ? a : -a;
        for (auto const& [coeff, j] : c.coeffs())
            lhs[j] += sign * coeff;
        rhs += sign * c.rhs();
    }
    for (auto it = lhs.begin(); it != lhs.end();) {
        if (it->second.is_zero())
            it = lhs.erase(it);
        else
            ++it;
    }
    ENSURE(lhs.size() == 1);
    ENSURE(lhs.begin()->first == ib.m_j);
    mpq expected_coeff = ib.m_is_lower_bound ? mpq(-1) : mpq(1);
    ENSURE(lhs.begin()->second == expected_coeff);
    ENSURE(rhs == expected_coeff * ib.m_bound);
}

static implied_bound const& find_implied_bound(std_vector<implied_bound> const& ibounds, lpvar j, bool is_lower) {
    for (auto const& ib : ibounds)
        if (ib.m_j == j && ib.m_is_lower_bound == is_lower)
            return ib;
    ENSURE(false);
    return ibounds[0];
}

// A bound propagated from a row sum_k a_k x_k = 0 onto column j uses the bound of
// every other column k with Farkas coefficient |a_k / a_j|. Before the weighted
// explanation was added every premise was reported with coefficient 1, which the
// proof checker rejected for rows with coefficients other than +-1.
static void test_row_farkas_coefficients() {
    lar_solver ls;
    lpvar x = ls.add_var(0, false);
    lpvar y = ls.add_var(1, false);
    lpvar z = ls.add_var(2, false);
    lpvar w = ls.add_var(3, false);

    // z = 2x + 3y, encoded as the term t1 = 2x + 3y - z with t1 in [0, 0]
    vector<std::pair<mpq, lpvar>> coeffs;
    coeffs.push_back({mpq(2), x});
    coeffs.push_back({mpq(3), y});
    coeffs.push_back({mpq(-1), z});
    lpvar t1 = ls.add_term(coeffs, 4);
    constraint_index t1_ge = ls.add_var_bound(t1, GE, mpq(0));
    constraint_index t1_le = ls.add_var_bound(t1, LE, mpq(0));

    // 2w = x + 3y, encoded as the term t2 = x + 3y - 2w with t2 in [0, 0].
    // The bounded column w has |a_j| = 2, so the coefficients are fractional.
    coeffs.clear();
    coeffs.push_back({mpq(1), x});
    coeffs.push_back({mpq(3), y});
    coeffs.push_back({mpq(-2), w});
    lpvar t2 = ls.add_term(coeffs, 5);
    constraint_index t2_ge = ls.add_var_bound(t2, GE, mpq(0));
    constraint_index t2_le = ls.add_var_bound(t2, LE, mpq(0));

    constraint_index x_le = ls.add_var_bound(x, LE, mpq(1));
    constraint_index y_le = ls.add_var_bound(y, LE, mpq(2));

    ENSURE(ls.find_feasible_solution() != lp_status::INFEASIBLE);

    farkas_explanation_collector imp(ls);
    std_vector<implied_bound> ibounds;
    lp_bound_propagator<farkas_explanation_collector> bp(imp, ibounds);
    bp.init();
    ls.add_column_rows_to_touched_rows(x);
    ls.add_column_rows_to_touched_rows(y);
    ls.propagate_bounds_for_touched_rows(bp);

    // z <= 2*1 + 3*2 = 8: coefficient 2 for x <= 1, 3 for y <= 2, 1 for the row constraint
    {
        implied_bound const& ib = find_implied_bound(bp.ibounds(), z, false);
        ENSURE(ib.m_bound == mpq(8));
        ENSURE(!ib.m_strict);
        imp.m_premises.clear();
        ls.explain_implied_bound(ib, bp);
        ENSURE(imp.m_premises.size() == 3);
        ENSURE(farkas_coeff_of(imp.m_premises, x_le) == mpq(2));
        ENSURE(farkas_coeff_of(imp.m_premises, y_le) == mpq(3));
        bool uses_t1 = false;
        for (auto const& [a, ci] : imp.m_premises) {
            if (ci == t1_ge || ci == t1_le) {
                uses_t1 = true;
                ENSURE(a == mpq(1));
            }
        }
        ENSURE(uses_t1);
        check_farkas_certificate(ls, ib, imp.m_premises);
    }

    // w <= (1 + 3*2) / 2 = 7/2: coefficient 1/2 for x <= 1, 3/2 for y <= 2, 1/2 for the row constraint
    {
        implied_bound const& ib = find_implied_bound(bp.ibounds(), w, false);
        ENSURE(ib.m_bound == mpq(7, 2));
        ENSURE(!ib.m_strict);
        imp.m_premises.clear();
        ls.explain_implied_bound(ib, bp);
        ENSURE(imp.m_premises.size() == 3);
        ENSURE(farkas_coeff_of(imp.m_premises, x_le) == mpq(1, 2));
        ENSURE(farkas_coeff_of(imp.m_premises, y_le) == mpq(3, 2));
        bool uses_t2 = false;
        for (auto const& [a, ci] : imp.m_premises) {
            if (ci == t2_ge || ci == t2_le) {
                uses_t2 = true;
                ENSURE(a == mpq(1, 2));
            }
        }
        ENSURE(uses_t2);
        check_farkas_certificate(ls, ib, imp.m_premises);
    }

    // every implied bound the propagator produced must carry a valid certificate
    for (auto const& ib : bp.ibounds()) {
        imp.m_premises.clear();
        ls.explain_implied_bound(ib, bp);
        check_farkas_certificate(ls, ib, imp.m_premises);
    }
    std::cout << "bound propagation: " << bp.ibounds().size() << " implied bounds certified\n";
}

}  // namespace lp

void tst_lp_bound_propagation() {
    lp::test_row_farkas_coefficients();
}
