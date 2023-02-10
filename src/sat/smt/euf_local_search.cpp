/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_local_search.cpp

Abstract:

    Local search dispatch for SMT

Author:

    Nikolaj Bjorner (nbjorner) 2023-02-07

--*/
#include "sat/sat_solver.h"
#include "sat/sat_ddfw.h"
#include "sat/smt/euf_solver.h"


namespace euf {
    
    void solver::local_search(bool_vector& phase) {
        scoped_limits scoped_rl(m.limit());
        sat::ddfw bool_search;
        bool_search.add(s());
        bool_search.updt_params(s().params());
        bool_search.set_seed(rand());
        scoped_rl.push_child(&(bool_search.rlimit()));

        unsigned max_rounds = 30;

        for (unsigned rounds = 0; m.inc() && rounds < max_rounds; ++rounds) {
            setup_bounds(phase);
            bool_search.reinit(s(), phase);

            // Non-boolean literals are assumptions to Boolean search
            literal_vector _lits;
            for (unsigned v = 0; v < phase.size(); ++v)
                if (!is_propositional(literal(v)))
                    _lits.push_back(literal(v, !phase[v]));

            bool_search.rlimit().push(m_max_bool_steps);
            
            lbool r = bool_search.check(_lits.size(), _lits.data(), nullptr);


            auto const& mdl = bool_search.get_model();
            for (unsigned i = 0; i < mdl.size(); ++i)
                phase[i] = mdl[i] == l_true;

            for (auto* th : m_solvers) 
                th->local_search(phase);
            // if is_sat break;
        }
              
    }

    bool solver::is_propositional(sat::literal lit) {
        expr* e = m_bool_var2expr.get(lit.var(), nullptr);
        return !e || is_uninterp_const(e) || !m_egraph.find(e);
    }

    void solver::setup_bounds(bool_vector const& phase) {
        unsigned num_literals = 0;
        unsigned num_bool = 0;
        for (auto* th : m_solvers)
            th->set_bounds_begin();

        auto init_literal = [&](sat::literal l) {
            if (is_propositional(l)) {
                ++num_bool;
                return;
            }
            euf::enode* n = m_egraph.find(m_bool_var2expr.get(l.var(), nullptr));
            for (auto const& thv : enode_th_vars(n)) {
                auto* th = m_id2solver.get(thv.get_id(), nullptr);
                if (th)
                    th->set_bounds(n);
            }
        };

        auto is_true = [&](auto lit) {
            return phase[lit.var()] == !lit.sign();
        };

        svector<sat::solver::bin_clause> bin_clauses;
        s().collect_bin_clauses(bin_clauses, false, false);
        for (auto* cp : s().clauses()) {
            if (any_of(*cp, [&](auto lit) { return is_true(lit); })) 
                continue;
            num_literals += cp->size();
            for (auto l : *cp) 
                init_literal(l);            
        }

        for (auto [l1, l2] : bin_clauses) {
            if (is_true(l1) || is_true(l2))
                continue;
            num_literals += 2;
            init_literal(l1);
            init_literal(l2);
        };

        m_max_bool_steps = (m_ls_config.L * num_bool) / num_literals;

        for (auto* th : m_solvers)
            th->set_bounds_end(num_literals);
    }
}
