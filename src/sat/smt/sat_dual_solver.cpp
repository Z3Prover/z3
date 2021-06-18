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
        m_vars.push_scope();
    }

    void dual_solver::pop(unsigned num_scopes) {
        m_solver.user_pop(num_scopes);
        unsigned old_sz = m_tracked_vars.old_size(num_scopes);
        for (unsigned i = m_tracked_vars.size(); i-- > old_sz; )
            m_is_tracked[m_tracked_vars[i]] = false; 
        old_sz = m_vars.old_size(num_scopes);
        for (unsigned i = m_vars.size(); i-- > old_sz; ) {
            unsigned v = m_vars[i];
            unsigned w = m_ext2var[v];
            m_ext2var[v] = null_bool_var;
            m_var2ext[w] = null_bool_var;
        }
        m_vars.pop_scope(num_scopes);
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
            m_vars.push_back(v);
        }
        return w;
    }

    void dual_solver::track_relevancy(bool_var w) {
        bool_var v = ext2var(w);
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
        TRACE("dual", tout << "root: " << literal_vector(sz, clause) << "\n";);
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
        TRACE("dual", tout << "aux: " << literal_vector(sz, clause) << "\n";);
        m_lits.reset();
        for (unsigned i = 0; i < sz; ++i) 
            m_lits.push_back(ext2lit(clause[i]));
        m_solver.mk_clause(sz, m_lits.data(), status::input());
    }

    void dual_solver::add_assumptions(solver const& s) {
        m_lits.reset();
        for (bool_var v : m_tracked_vars)
            m_lits.push_back(literal(v, l_false == s.value(m_var2ext[v])));
        for (auto lit : m_units) {
            bool_var w = m_ext2var.get(lit.var(), null_bool_var);
            if (w != null_bool_var)
                m_lits.push_back(ext2lit(lit));            
        }
    }

    bool dual_solver::operator()(solver const& s) {
        m_core.reset();
        m_core.append(m_units);
        if (m_roots.empty())
            return true;
        m_solver.user_push();
        m_solver.add_clause(m_roots.size(), m_roots.data(), status::input());
        add_assumptions(s);
        lbool is_sat = m_solver.check(m_lits.size(), m_lits.data());
        if (is_sat == l_false) 
            for (literal lit : m_solver.get_core())
                m_core.push_back(lit2ext(lit));        
        if (is_sat == l_true) {
            TRACE("dual", display(s, tout); s.display(tout););
            IF_VERBOSE(0, verbose_stream() << "unexpected SAT\n");
            UNREACHABLE();
            return false;
        }
        TRACE("dual", m_solver.display(tout << "is-sat: " << is_sat << " core: " << m_core << "\n"););
        m_solver.user_pop(1);
        return is_sat == l_false;
    }

    std::ostream& dual_solver::display(solver const& s, std::ostream& out) const {        
        for (unsigned v = 0; v < m_solver.num_vars(); ++v) {
            bool_var w = m_var2ext.get(v, null_bool_var);
            if (w == null_bool_var)
                continue;
            lbool v1 = m_solver.value(v);
            lbool v2 = s.value(w);
            if (v1 == v2 || v2 == l_undef)
                continue;
            out << "ext: " << w << " " << v2 << "\n";
            out << "int: " << v << " " << v1 << "\n";
        }
        literal_vector lits;
        for (bool_var v : m_tracked_vars) 
            lits.push_back(literal(m_var2ext[v], l_false == s.value(m_var2ext[v])));
        out << "tracked: " << lits << "\n";  
        lits.reset();
        for (literal r : m_roots) 
            if (m_solver.value(r) == l_true)
                lits.push_back(r);
        out << "roots: " << lits << "\n";
        m_solver.display(out);

        return out;
    }
}
