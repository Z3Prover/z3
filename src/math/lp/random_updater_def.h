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
#include "math/lp/random_updater.h"
#include "math/lp/static_matrix.h"
#include "math/lp/lar_solver.h"
#include "util/vector.h"
namespace lp {



random_updater::random_updater(
                               lar_solver & lar_solver,
                               const vector<unsigned> & column_indices) :
    m_lar_solver(lar_solver),
    m_range(100000) {
    m_var_set.resize(m_lar_solver.number_of_vars());
    for (unsigned j : column_indices)
        m_var_set.insert(j);
    TRACE("lar_solver_rand", tout << "size = " << m_var_set.size() << "\n";);
}


bool random_updater::shift_var(unsigned j) {
    SASSERT(!m_lar_solver.column_is_fixed(j) && !m_lar_solver.is_base(j));
    bool ret = m_lar_solver.get_int_solver()->shift_var(j, m_range);
    if (ret) {
        const auto & A = m_lar_solver.A_r();
        for (const auto& c : A.m_columns[j]) {
            unsigned row_index = c.var();
            unsigned changed_basic = m_lar_solver.get_core_solver().m_r_basis[row_index];
            m_var_set.erase(changed_basic);
        }
    }
    return ret;
}


void random_updater::update() {
    auto columns = m_var_set.index();  // m_var_set is going to change during the loop
    for (auto j : columns) {
        if (!m_var_set.contains(j)) {
            TRACE("lar_solver_rand", tout << "skipped " << j << "\n";);
            continue;
        }
        if (!m_lar_solver.is_base(j)) {
            shift_var(j);
        } else {
            unsigned row = m_lar_solver.get_core_solver().m_r_heading[j];
            for (auto & row_c : m_lar_solver.get_core_solver().m_r_A.m_rows[row]) {
                unsigned cj = row_c.var();
                if (!m_lar_solver.is_base(cj) &&
                    !m_lar_solver.column_is_fixed(cj)
                    &&
                    shift_var(cj)
                    ) {
                    break; // done with the basic var j
                }
            }
        }            
    }
    TRACE("lar_solver_rand", tout << "m_var_set.size() = " << m_var_set.size() << "\n";);
}

}
