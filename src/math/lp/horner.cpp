/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/

#include "math/lp/horner.h"
#include "math/lp/nla_core.h"
#include "math/lp/lp_utils.h"
#include "math/lp/cross_nested.h"

namespace nla {
typedef intervals::interval interv;
horner::horner(core * c) : common(c), m_row_sum(m_nex_creator) {}

template <typename T>
bool horner::row_has_monomial_to_refine(const T& row) const {
    for (const auto& p : row) {
        if (c().m_to_refine.contains(p.var()))
            return true;
    }
    return false;
}

// Returns true if the row has at least two monomials sharing a variable
template <typename T>
bool horner::row_is_interesting(const T& row) const {
    TRACE(nla_solver_details, c().print_row(row, tout););
    if (row.size() > c().params().arith_nl_horner_row_length_limit()) {
        TRACE(nla_solver_details, tout << "disregard\n";);
        return false;
    }
    SASSERT(row_has_monomial_to_refine(row));
    c().clear_active_var_set();
    for (const auto& p : row) {
        lpvar j = p.var();
        if (!c().is_monic_var(j)) {
            if (c().active_var_set_contains(j))
                return true;
            c().insert_to_active_var_set(j);
            continue;
        }
        auto & m = c().emons()[j];
        
        for (lpvar k : m.vars()) {
            if (c().active_var_set_contains(k))
                return true;
        }
        for (lpvar k : m.vars()) {
            c().insert_to_active_var_set(k);
        }
    }
    return false;
}

bool horner::lemmas_on_expr(cross_nested& cn, nex_sum* e) {
    TRACE(nla_horner, tout << "e = " << *e << "\n";);
    cn.run(e);
    return cn.done();
}

template <typename T> 
bool horner::lemmas_on_row(const T& row) {
    SASSERT (row_is_interesting(row));
    c().clear_active_var_set();
    u_dependency* dep = nullptr;
    create_sum_from_row(row, m_nex_creator, m_row_sum, dep);
    c().set_active_vars_weights(m_nex_creator); // without this call the comparisons will be incorrect
    nex* e =  m_nex_creator.simplify(m_row_sum.mk());
    TRACE(nla_horner, tout << "e = " << * e << "\n";);
    if (e->get_degree() < 2)
        return false;
    if (!e->is_sum())
        return false;
    
    cross_nested cn(
        [this, dep](const nex* n) { return c().m_intervals.check_nex(n, dep); },
        [this](unsigned j)   { return c().var_is_fixed(j); },
        c().reslim(),
        c().random(),
        m_nex_creator);
    bool ret = lemmas_on_expr(cn, to_sum(e));
    c().m_intervals.get_dep_intervals().reset(); // clean the memory allocated by the interval bound dependencies
    return ret;

}

// Find the binary monomial y*v in emonics, return its variable or null_lpvar.
static lpvar find_binary_monic(emonics const& emons, lpvar y, lpvar v) {
    if (!emons.is_used_in_monic(v))
        return null_lpvar;
    for (auto const& m : emons.get_use_list(v))
        if (m.size() == 2 && (m.vars()[0] == y || m.vars()[1] == y))
            return m.var();
    return null_lpvar;
}

// Recover named intermediates destroyed by solve-eqs.
//
// When solve-eqs eliminates x = sum(c_i * v_i), product x*y splits into
// sum(c_i * v_i * y). Horner's cross-nested factoring recovers y*sum(c_i*v_i)
// and interval_from_term finds the LP term column tc := sum(c_i * v_i)
// with tight bounds [L, U].
//
// We do two things:
// 1. Create monomial m := y*tc, add LP row m - sum(c_i * mon(y,v_i)) = 0
// 2. If variable x with monomial x*y exists and val(x) = val(tc),
//    propagate: tc in [L,U] => x in [L,U]
void horner::introduce_monomials_from_term_columns() {
    if (c().params().arith_nl_horner_max_new_monomials() == 0)
        return;
    auto const& term_cols = c().m_intervals.term_columns();
    if (term_cols.empty())
        return;

    unsigned added = 0;
    for (lpvar tc : term_cols) {
        if (!c().lra.column_has_lower_bound(tc) || !c().lra.column_has_upper_bound(tc))
            continue;
        if (!c().lra.column_has_term(tc))
            continue;

        auto const& term = c().lra.get_term(tc);

        for (auto const& ti : term) {
            lpvar vi = ti.j();
            if (!c().m_emons.is_used_in_monic(vi))
                continue;

            for (auto const& m : c().m_emons.get_use_list(vi)) {
                if (m.size() != 2)
                    continue;
                lpvar y = (m.vars()[0] == vi) ? m.vars()[1] : m.vars()[0];

                auto key = std::make_pair(std::min(y, tc), std::max(y, tc));
                if (m_introduced_monomials.contains(key))
                    continue;

                // Check that mon(y, v_i) exists for every v_i in tc
                lp::lar_term eq_term;
                bool complete = true;
                for (auto const& tj : term) {
                    lpvar yv = find_binary_monic(c().m_emons, y, tj.j());
                    if (yv == null_lpvar) { complete = false; break; }
                    eq_term.add_monomial(-tj.coeff(), yv);
                }
                if (!complete)
                    continue;

                m_introduced_monomials.push_back(key);

                // (1) m := y * tc, with LP row: m - sum(c_i * mon(y,v_i)) = 0
                lpvar factors[2] = { y, tc };
                lpvar new_mon = c().add_mul_def(2, factors);
                eq_term.add_monomial(rational::one(), new_mon);
                lp::lpvar eq_col = c().lra.add_term(eq_term.coeffs_as_vector(), UINT_MAX);
                c().lra.update_column_type_and_bound(eq_col, llc::EQ, rational::zero(), nullptr);
                c().m_check_feasible = true;
                TRACE(nla_solver, tout << "introduced monomial j" << new_mon
                      << " := j" << y << " * j" << tc << "\n";);

                // (2) Propagate tc's bounds to variable x where mon(x, y) exists
                //     and val(x) = val(tc), i.e., x equals tc in current model.
                for (auto const& m2 : c().m_emons.get_use_list(y)) {
                    if (m2.size() != 2)
                        continue;
                    lpvar x = (m2.vars()[0] == y) ? m2.vars()[1] : m2.vars()[0];
                    if (x == tc || c().lra.column_has_term(x))
                        continue;
                    if (c().lra.get_column_value(x) != c().lra.get_column_value(tc))
                        continue;
                    if (c().lra.column_has_lower_bound(tc)) {
                        c().lra.update_column_type_and_bound(
                            x, llc::GE, c().lra.get_lower_bound(tc).x,
                            c().lra.get_column_lower_bound_witness(tc));
                        c().m_check_feasible = true;
                        TRACE(nla_solver, tout << "bound j" << x << " >= "
                              << c().lra.get_lower_bound(tc).x << " from j" << tc << "\n";);
                    }
                    if (c().lra.column_has_upper_bound(tc)) {
                        c().lra.update_column_type_and_bound(
                            x, llc::LE, c().lra.get_upper_bound(tc).x,
                            c().lra.get_column_upper_bound_witness(tc));
                        c().m_check_feasible = true;
                        TRACE(nla_solver, tout << "bound j" << x << " <= "
                              << c().lra.get_upper_bound(tc).x << " from j" << tc << "\n";);
                    }
                }

                if (++added >= c().params().arith_nl_horner_max_new_monomials())
                    return;
            }
        }
    }
}

bool horner::horner_lemmas() {
    if (!c().params().arith_nl_horner()) {
        TRACE(nla_solver, tout << "not generating horner lemmas\n";);
        return false;
    }
    c().lp_settings().stats().m_horner_calls++;
    c().m_intervals.clear_term_columns();
    const auto& matrix = c().lra.A_r();
    // choose only rows that depend on m_to_refine variables
    std::set<unsigned> rows_to_check;
    for (lpvar j : c().m_to_refine) {
        for (auto & s : matrix.m_columns[j])
            rows_to_check.insert(s.var());
    }
    c().clear_active_var_set();
    svector<unsigned> rows;
    for (unsigned i : rows_to_check) {
        if (row_is_interesting(matrix.m_rows[i]))
            rows.push_back(i);
    }

    unsigned r = c().random();
    unsigned sz = rows.size();
    bool conflict = false;
    for (unsigned i = 0; i < sz && !conflict; ++i) {
        m_row_index = rows[(i + r) % sz];
        if (lemmas_on_row(matrix.m_rows[m_row_index])) {
            c().lp_settings().stats().m_horner_conflicts++;
            conflict = true;
        }
    }

    if (!conflict)
        introduce_monomials_from_term_columns();

    return conflict;
}
}

