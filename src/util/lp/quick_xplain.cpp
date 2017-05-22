/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/lar_solver.h"
namespace lean {
quick_xplain::quick_xplain(vector<std::pair<mpq, constraint_index>> & explanation, const lar_solver & ls, lar_solver & qsol) :
    m_explanation(explanation),
    m_parent_solver(ls),
    m_qsol(qsol) {
}
void quick_xplain::add_constraint_to_qsol(unsigned j) {
    auto & lar_c = m_constraints_in_local_vars[j];
    auto ls = lar_c.get_left_side_coefficients();
    auto ci = m_qsol.add_constraint(ls, lar_c.m_kind, lar_c.m_right_side);
    m_local_ci_to_constraint_offsets[ci] = j;
}
    
void quick_xplain::copy_constraint_and_add_constraint_vars(const lar_constraint& lar_c) {
    vector < std::pair<mpq, unsigned>> ls;
    for (auto & p : lar_c.get_left_side_coefficients()) {
        unsigned j = p.second;
        unsigned lj = m_qsol.add_var(j);
        ls.push_back(std::make_pair(p.first, lj));
    }
    m_constraints_in_local_vars.push_back(lar_constraint(ls, lar_c.m_kind, lar_c.m_right_side));

}

bool quick_xplain::infeasible() {
    m_qsol.solve();
    return m_qsol.get_status() == INFEASIBLE;
}

// u - unexplored constraints
// c and x are assumed, in other words, all constrains of x and c are already added to m_qsol
void quick_xplain::minimize(const vector<unsigned>& u) {
    unsigned k = 0;
    unsigned initial_stack_size = m_qsol.constraint_stack_size();
    for (; k < u.size();k++) {
        m_qsol.push();
        add_constraint_to_qsol(u[k]);
        if (infeasible())
            break;
    }
    m_x.insert(u[k]);
    unsigned m = k / 2; // the split
    if (m < k) {
        m_qsol.pop(k + 1 - m);
        add_constraint_to_qsol(u[k]);
        if (!infeasible()) {
            vector<unsigned> un;
            for (unsigned j = m; j < k; j++)
                un.push_back(u[j]);
            minimize(un);
        }
    }
    if (m > 0) {
        lean_assert(m_qsol.constraint_stack_size() >= initial_stack_size);
        m_qsol.pop(m_qsol.constraint_stack_size() - initial_stack_size);
        for (auto j : m_x) 
            add_constraint_to_qsol(j);
        if (!infeasible()) {
            vector<unsigned> un;
            for (unsigned j = 0; j < m; j++)
                un.push_back(u[j]);
            minimize(un);
        }
    }
}

    
void quick_xplain::run(vector<std::pair<mpq, constraint_index>> & explanation, const lar_solver & ls){
    if (explanation.size() <= 2) return;
    lar_solver qsol;
    lean_assert(ls.explanation_is_correct(explanation));
    quick_xplain q(explanation, ls, qsol);
    q.solve();
}

void quick_xplain::copy_constraints_to_local_constraints() {
    for (auto & p : m_explanation) {
        const auto & lar_c = m_parent_solver.get_constraint(p.second);
        m_local_constraint_offset_to_external_ci.push_back(p.second);
        copy_constraint_and_add_constraint_vars(lar_c);
    }
}

bool quick_xplain::is_feasible(const vector<unsigned> & x, unsigned k) const {
    lar_solver l;
    for (unsigned i : x) {
        if (i == k)
            continue;
        vector < std::pair<mpq, unsigned>> ls;
        const lar_constraint & c = m_constraints_in_local_vars[i];
        for (auto & p : c.get_left_side_coefficients()) {
            unsigned lj = l.add_var(p.second);
            ls.push_back(std::make_pair(p.first, lj));
        }
        l.add_constraint(ls, c.m_kind, c.m_right_side);
    }
    l.solve();
    return l.get_status() != INFEASIBLE;
}

bool quick_xplain::x_is_minimal() const {
    vector<unsigned> x;
    for (auto j : m_x)
        x.push_back(j);

    for (unsigned k = 0; k < x.size(); k++) {
        lean_assert(is_feasible(x, x[k]));
    }
    return true;
}

void quick_xplain::solve() {
    copy_constraints_to_local_constraints();
    m_qsol.push();
    lean_assert(m_qsol.constraint_count() == 0)
        vector<unsigned> u;
    for (unsigned k = 0; k < m_constraints_in_local_vars.size(); k++)
        u.push_back(k);
    minimize(u);
    while (m_qsol.constraint_count() > 0)
        m_qsol.pop();
    for (unsigned i : m_x)
        add_constraint_to_qsol(i);
    m_qsol.solve();
    lean_assert(m_qsol.get_status() == INFEASIBLE);
    m_qsol.get_infeasibility_explanation(m_explanation);
    lean_assert(m_qsol.explanation_is_correct(m_explanation));
    lean_assert(x_is_minimal());
    for (auto & p : m_explanation) {
        p.second = this->m_local_constraint_offset_to_external_ci[m_local_ci_to_constraint_offsets[p.second]];
    }
}
}
