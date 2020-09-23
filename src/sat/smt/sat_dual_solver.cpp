/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_dual_solver.cpp

Abstract:

    Solver for obtaining implicant.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once
#include "sat/smt/sat_dual_solver.h"

namespace sat {

    dual_solver::dual_solver(reslimit& l):
        m_solver(params_ref(), l)
    {}

    void dual_solver::push() {
        m_solver.user_push(); 
        m_roots_lim.push_back(m_roots.size());     
        m_tracked_lim.push_back(m_tracked_stack.size());
    }

    void dual_solver::pop(unsigned num_scopes) {
        m_solver.user_pop(num_scopes);
        unsigned old_sz = m_roots_lim.size() - num_scopes;
        m_roots.shrink(m_roots_lim[old_sz]);
        m_roots_lim.shrink(old_sz);
        for (unsigned v = m_tracked_stack.size(); v-- > m_tracked_lim[old_sz]; ) 
            m_is_tracked[v] = false; 
        m_tracked_stack.shrink(m_tracked_lim[old_sz]);
        m_tracked_lim.shrink(old_sz);
    }

    void dual_solver::track_relevancy(bool_var v) {
        if (!m_is_tracked.get(v, false)) {
            m_is_tracked.setx(v, true, false);
            m_tracked_stack.push_back(v);
        }
    }

    void dual_solver::add_literal(literal lit) {
        bool_var v = lit.var();
        while (m_solver.num_vars() <= v)
            m_solver.mk_var();
    }

    void dual_solver::add_root(literal lit, unsigned sz, literal const* clause) {
        add_literal(lit);
        for (unsigned i = 0; i < sz; ++i) 
            add_literal(clause[i]);
        for (unsigned i = 0; i < sz; ++i)
            m_solver.mk_clause(lit, ~clause[i], status::input());
        m_roots.push_back(~lit);
    }

    void dual_solver::add_aux(unsigned sz, literal const* clause) {
        for (unsigned i = 0; i < sz; ++i) 
            add_literal(clause[i]);
        m_lits.init(sz, clause);
        m_solver.mk_clause(sz, m_lits.c_ptr(), status::input());
    }

    bool dual_solver::operator()(solver const& s) {
        m_solver.user_push();
        m_solver.add_clause(m_roots.size(), m_roots.c_ptr(), status::input());
        m_lits.reset();
        for (bool_var v : m_tracked_stack)
            m_lits.push_back(literal(v, l_false == s.value(v)));
        lbool is_sat = m_solver.check(m_lits.size(), m_lits.c_ptr());
        if (is_sat == l_false)
            m_core.init(m_solver.get_core());
        TRACE("euf", m_solver.display(tout << m_core << "\n"););
        m_solver.user_pop(1);
        return is_sat == l_false;
    }
}
