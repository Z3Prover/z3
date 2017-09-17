/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#include "util/lp/lar_solver.h"
namespace lp {
    lp_bound_propagator::lp_bound_propagator(lar_solver & ls):
    m_lar_solver(ls) {}
column_type lp_bound_propagator::get_column_type(unsigned j) const {
    return m_lar_solver.m_mpq_lar_core_solver.m_column_types()[j];
}
const impq & lp_bound_propagator::get_low_bound(unsigned j) const {
    return m_lar_solver.m_mpq_lar_core_solver.m_r_low_bounds()[j];
}
const impq & lp_bound_propagator::get_upper_bound(unsigned j) const {
    return m_lar_solver.m_mpq_lar_core_solver.m_r_upper_bounds()[j];
}
void lp_bound_propagator::try_add_bound(const mpq & v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned row_or_term_index, bool strict) {
    unsigned term_j = m_lar_solver.adjust_column_index_to_term_index(j);
    mpq w = v;
    if (term_j != j) {
        j = term_j;
        w += m_lar_solver.get_term(term_j).m_v; // when terms are turned into the columns they "lose" the right side, at this moment they aquire it back
    }
    lconstraint_kind kind = is_low? GE : LE;
    if (strict)
        kind = static_cast<lconstraint_kind>(kind / 2);

    if (!bound_is_interesting(j, kind, w))
        return;
     unsigned k; // index to ibounds
     if (is_low) {
         if (try_get_val(m_improved_low_bounds, j, k)) {
             auto & found_bound = m_ibounds[k];
             if (w > found_bound.m_bound || (w == found_bound.m_bound && found_bound.m_strict == false && strict))
                 found_bound = implied_bound(w, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
         } else {
             m_improved_low_bounds[j] = m_ibounds.size();
             m_ibounds.push_back(implied_bound(w, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
         }
     } else { // the upper bound case
         if (try_get_val(m_improved_upper_bounds, j, k)) {
             auto & found_bound = m_ibounds[k];
             if (w < found_bound.m_bound || (w == found_bound.m_bound && found_bound.m_strict == false && strict))
                 found_bound = implied_bound(w, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict);
         } else {
             m_improved_upper_bounds[j] = m_ibounds.size();
             m_ibounds.push_back(implied_bound(w, j, is_low, coeff_before_j_is_pos, row_or_term_index, strict));
        }
     }
}
}
