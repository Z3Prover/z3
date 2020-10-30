/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_dual_solver.cpp

Abstract:

    Solver for obtaining implicant.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#include "sat/smt/sat_dual_solver.h"

namespace sat {

    dual_solver::no_drat_params::no_drat_params() {
        set_sym("drat.file", symbol());
    }

    dual_solver::dual_solver(reslimit& l):
        m_solver(m_params, l)
    {
        SASSERT(!m_solver.get_config().m_drat);
    }

    void dual_solver::push() {
        m_solver.user_push(); 
        m_roots.push_scope();
        m_tracked_vars.push_scope();
        m_units.push_scope();
    }

    void dual_solver::pop(unsigned num_scopes) {
        m_solver.user_pop(num_scopes);
        unsigned old_sz = m_tracked_vars.old_size(num_scopes);
        for (unsigned i = m_tracked_vars.size(); i-- > old_sz; )
            m_is_tracked[m_tracked_vars[i]] = false; 
        m_units.pop_scope(num_scopes);
        m_roots.pop_scope(num_scopes);
        m_tracked_vars.pop_scope(num_scopes);
    }

    bool_var dual_solver::ext2var(bool_var v) {
        bool_var w = m_ext2var.get(v, null_bool_var);
        if (null_bool_var == w) {
            w = m_solver.mk_var();
            m_ext2var.setx(v, w, null_bool_var);
            m_var2ext.setx(w, v, null_bool_var);
        }
        return w;
    }

    void dual_solver::track_relevancy(bool_var v) {
        v = ext2var(v);
        if (!m_is_tracked.get(v, false)) {
            m_is_tracked.setx(v, true, false);
            m_tracked_vars.push_back(v);
        }
    }

    literal dual_solver::ext2lit(literal lit) {
        return literal(ext2var(lit.var()), lit.sign());
    }

    literal dual_solver::lit2ext(literal lit) {
        return literal(m_var2ext[lit.var()], lit.sign());
    }

    void dual_solver::add_root(unsigned sz, literal const* clause) {
        if (sz == 1) {
            m_units.push_back(clause[0]);
            return;
        }
        literal root(m_solver.mk_var(), false);
        for (unsigned i = 0; i < sz; ++i)
            m_solver.mk_clause(root, ~ext2lit(clause[i]), status::input());
        m_roots.push_back(~root);
    }

    void dual_solver::add_aux(unsigned sz, literal const* clause) {
        m_lits.reset();
        for (unsigned i = 0; i < sz; ++i) 
            m_lits.push_back(ext2lit(clause[i]));
        m_solver.mk_clause(sz, m_lits.c_ptr(), status::input());
    }

    bool dual_solver::operator()(solver const& s) {
        m_solver.user_push();
        m_solver.add_clause(m_roots.size(), m_roots.c_ptr(), status::input());
        m_lits.reset();
        for (bool_var v : m_tracked_vars)
            m_lits.push_back(literal(v, l_false == s.value(m_var2ext[v])));
        lbool is_sat = m_solver.check(m_lits.size(), m_lits.c_ptr());
        m_core.reset();
        m_core.append(m_units);
        if (is_sat == l_false) 
            for (literal lit : m_solver.get_core())
                m_core.push_back(lit2ext(lit));
        TRACE("euf", m_solver.display(tout << "is-sat: " << is_sat << " core: " << m_core << "\n"););
        m_solver.user_pop(1);
        return is_sat == l_false;
    }
}
