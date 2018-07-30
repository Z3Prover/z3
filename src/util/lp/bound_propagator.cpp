/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/lar_solver.h"
namespace lp {
bound_propagator::bound_propagator(lar_solver & ls):
    m_lar_solver(ls) {}
column_type bound_propagator::get_column_type(unsigned j) const {
    return m_lar_solver.m_mpq_lar_core_solver.m_column_types()[j];
}
const impq & bound_propagator::get_lower_bound(unsigned j) const {
    return m_lar_solver.m_mpq_lar_core_solver.m_r_lower_bounds()[j];
}
const impq & bound_propagator::get_upper_bound(unsigned j) const {
    return m_lar_solver.m_mpq_lar_core_solver.m_r_upper_bounds()[j];
}
void bound_propagator::try_add_bound(mpq  v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned row_or_term_index, bool strict) {
    j = m_lar_solver.adjust_column_index_to_term_index(j);    
    if (m_lar_solver.is_term(j)) {
        // lp treats terms as not having a free coefficient, restoring it below for the outside consumption
        v += m_lar_solver.get_term(j).m_v;
    }

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
