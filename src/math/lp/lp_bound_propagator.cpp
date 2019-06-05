/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "math/lp/lar_solver.h"
#include "math/lp/nla_solver.h"
namespace lp {

lp_bound_propagator::lp_bound_propagator(lar_solver & ls, nla::solver* nla):
    m_lar_solver(ls), m_nla_solver(nla) {}

column_type lp_bound_propagator::get_column_type(unsigned j) const {
    return m_lar_solver.m_mpq_lar_core_solver.m_column_types()[j];
}

bool lp_bound_propagator::lower_bound_is_available(unsigned j) const {
    if (lower_bound_is_available_for_column(j))
        return true;
    if (!m_nla_solver->is_monomial_var(j))
        return false;
    return m_nla_solver->monomial_has_lower_bound(j);
}

bool lp_bound_propagator::upper_bound_is_available_for_column(unsigned j) const {
    switch (get_column_type(j)) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::upper_bound:
        return true;
    default:
        return false;
    }
}

bool lp_bound_propagator::lower_bound_is_available_for_column(unsigned j) const {
    switch (get_column_type(j)) {
    case column_type::fixed:
    case column_type::boxed:
    case column_type::lower_bound:
        return true;
    default:
        return false;
    }
}
bool lp_bound_propagator::upper_bound_is_available(unsigned j) const {
    if (upper_bound_is_available_for_column(j))
        return true;
    if (!m_nla_solver->is_monomial_var(j))
        return false;
    return m_nla_solver->monomial_has_upper_bound(j);
}

impq lp_bound_propagator::get_lower_bound(unsigned j) const {
    lp_assert(lower_bound_is_available(j));
    if (lower_bound_is_available_for_column(j)) {
        const impq& l = m_lar_solver.m_mpq_lar_core_solver.m_r_lower_bounds()[j];
        if (!(m_nla_solver && m_nla_solver->is_monomial_var(j)))
            return l;
        if (! m_nla_solver->monomial_has_lower_bound(j))
            return std::max(l,  m_nla_solver->get_lower_bound(j));
    }
    return m_nla_solver->get_lower_bound(j);
}

impq lp_bound_propagator::get_upper_bound(unsigned j) const {
    lp_assert(upper_bound_is_available(j));
    if (upper_bound_is_available_for_column(j)) {
        const impq& l = m_lar_solver.m_mpq_lar_core_solver.m_r_upper_bounds()[j];
        if (!(m_nla_solver && m_nla_solver->is_monomial_var(j)))
            return l;
        if (! m_nla_solver->monomial_has_upper_bound(j))
            return std::min(l, m_nla_solver->get_upper_bound(j));
    }
    return m_nla_solver->get_upper_bound(j);
}

void lp_bound_propagator::try_add_bound(mpq  v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned row_or_term_index, bool strict) {
    CTRACE("nla_solver", m_nla_solver && m_nla_solver->is_monomial_var(j), tout << "mon_var = " << j << "\n"; );
    j = m_lar_solver.adjust_column_index_to_term_index(j);    

    lconstraint_kind kind = is_low? GE : LE;
    if (strict)
        kind = static_cast<lconstraint_kind>(kind / 2);
    
    if (!bound_is_interesting(j, kind, v))
        return;
     unsigned k; // index to ibounds
     if (is_low) {
         if (try_get_value(m_improved_lower_bounds, j, k)) {
             auto & found_bound = m_ibounds[k];
             if (v > found_bound.m_bound || (v == found_bound.m_bound && found_bound.m_strict == false && strict)) {
                 found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                 TRACE("try_add_bound", m_lar_solver.print_implied_bound(found_bound, tout););
             }
         } else {
             m_improved_lower_bounds[j] = m_ibounds.size();
             m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
             TRACE("try_add_bound", m_lar_solver.print_implied_bound(m_ibounds.back(), tout););
         }
     } else { // the upper bound case
         if (try_get_value(m_improved_upper_bounds, j, k)) {
             auto & found_bound = m_ibounds[k];
             if (v < found_bound.m_bound || (v == found_bound.m_bound && found_bound.m_strict == false && strict)) {
                 found_bound = implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
                 TRACE("try_add_bound", m_lar_solver.print_implied_bound(found_bound, tout););
             }
         } else {
             m_improved_upper_bounds[j] = m_ibounds.size();
             m_ibounds.push_back(implied_bound(v, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
             TRACE("try_add_bound", m_lar_solver.print_implied_bound(m_ibounds.back(), tout););
        }
     }
}
}
