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
    for (unsigned j : column_indices)
        add_column_to_sets(j);
}


bool random_updater::shift_var(unsigned v) {
    return m_lar_solver.get_int_solver()->shift_var(v, m_range);
}


void random_updater::update() {
    for (auto j : m_var_set) {
        if (m_var_set.size() <= m_values.size()) {
            break; // we are done
        }
        auto old_x = m_lar_solver.get_column_value(j);
        if (shift_var(j)) {
            remove_value(old_x);
            add_value(m_lar_solver.get_column_value(j));
        }
    }
}

void random_updater::add_value(const numeric_pair<mpq>& v) {
    auto it = m_values.find(v);
    if (it == m_values.end()) {
        m_values[v] = 1;
    } else {
        it->second++;
    }
}

void random_updater::remove_value(const numeric_pair<mpq>& v) {
    std::unordered_map<numeric_pair<mpq>, unsigned>::iterator it = m_values.find(v);
    lp_assert(it != m_values.end());
    it->second--;
    if (it->second == 0)
        m_values.erase((std::unordered_map<numeric_pair<mpq>, unsigned>::const_iterator)it);
}

void random_updater::add_column_to_sets(unsigned j) {
    if (m_lar_solver.get_core_solver().m_r_heading[j] < 0) {
        m_var_set.insert(j);
        add_value(m_lar_solver.get_core_solver().m_r_x[j]);
    } else {
        unsigned row = m_lar_solver.get_core_solver().m_r_heading[j];
        for (auto & row_c : m_lar_solver.get_core_solver().m_r_A.m_rows[row]) {
            unsigned cj = row_c.var();
            if (m_lar_solver.get_core_solver().m_r_heading[cj] < 0) {
                m_var_set.insert(cj);
                add_value(m_lar_solver.get_core_solver().m_r_x[cj]);
            }
        }
    }
}
}
