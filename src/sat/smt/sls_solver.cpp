/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_solver

Abstract:

    Interface to Concurrent SLS solver
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-02-21

--*/

#include "sat/smt/sls_solver.h"
#include "sat/smt/euf_solver.h"



namespace sls {

    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("sls"), ctx.get_manager().mk_family_id("sls")) {}

    solver::~solver() {
        if (m_bvsls) {
            m_bvsls->cancel();            
            m_thread.join();
        }
    }

    void solver::push_core() {
        if (s().scope_lvl() == s().search_lvl() + 1)
            init_local_search();
    }
    
    void solver::pop_core(unsigned n) {
        if (s().scope_lvl() - n <= s().search_lvl())
            sample_local_search();
    }

    void solver::simplify() {
    
    }
        

    void solver::init_local_search() {
        if (m_bvsls) {
            m_bvsls->cancel();
            m_thread.join();
            if (m_result == l_true) {
                verbose_stream() << "Found model using local search - INIT\n";
                exit(1);
            }
        }
        // set up state for local search solver here

        m_m = alloc(ast_manager, m);
        ast_translation tr(m, *m_m);
        
        m_completed = false;
        m_result = l_undef;
        m_bvsls = alloc(bv::sls, *m_m);
        // walk clauses, add them
        // walk trail stack until search level, add units
        // encapsulate bvsls within the arguments of run-local-search.
        // ensure bvsls does not touch ast-manager.

        unsigned trail_sz = s().trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            auto lit = s().trail_literal(i);
            if (s().lvl(lit) > s().search_lvl())
                break;
            expr_ref fml = literal2expr(lit);
            m_bvsls->assert_expr(tr(fml.get()));
        }
        unsigned num_vars = s().num_vars();
        for (unsigned i = 0; i < 2*num_vars; ++i) {
            auto l1 = ~sat::to_literal(i);
            auto const& wlist = s().get_wlist(l1);
            for (sat::watched const& w : wlist) {
                if (!w.is_binary_non_learned_clause())
                    continue;
                sat::literal l2 = w.get_literal();
                if (l1.index() > l2.index())
                    continue;
                expr_ref fml(m.mk_or(literal2expr(l1), literal2expr(l2)), m);
                m_bvsls->assert_expr(tr(fml.get()));
            }
        }
        for (auto clause : s().clauses()) {
            expr_ref_vector cls(m);
            for (auto lit : *clause)
                cls.push_back(literal2expr(lit));
            expr_ref fml(m.mk_or(cls), m);
            m_bvsls->assert_expr(tr(fml.get()));
        }

        // use phase assignment from literals?
        std::function<bool(expr*, unsigned)> eval = [&](expr* e, unsigned r) {
            return false;
        };

        m_bvsls->init();
        m_bvsls->init_eval(eval);
        m_bvsls->updt_params(s().params());

        m_thread = std::thread([this]() { run_local_search(); });        
    }

    void solver::sample_local_search() {
        if (m_completed) {
            m_thread.join();
            if (m_result == l_true) {
                verbose_stream() << "Found model using local search\n";
                exit(1);
            }
        }
    }

    void solver::run_local_search() {
        lbool r = (*m_bvsls)();
        m_result = r;
        m_completed = true;
    }

}
