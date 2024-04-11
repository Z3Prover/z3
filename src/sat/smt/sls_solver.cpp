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
        th_euf_solver(ctx, symbol("sls"), ctx.get_manager().mk_family_id("sls")),
        m_units(m) {}

    solver::~solver() {
        finalize();
    }

    void solver::finalize() {
        if (!m_completed && m_bvsls) {
            m_bvsls->cancel();
            m_thread.join();
            m_bvsls->collect_statistics(m_st);
            m_bvsls = nullptr;
        }
    }

    sat::check_result solver::check() { 

        return sat::check_result::CR_DONE; 
    }

    void solver::simplify() {    
    }

    bool solver::unit_propagate() {
        force_push();
        sample_local_search();
        return false;
    }

    bool solver::is_unit(expr* e) {
        if (!e)
            return false;
        m.is_not(e, e);
        if (is_uninterp_const(e))
            return true;
        bv_util bu(m);
        expr* s;
        if (bu.is_bit2bool(e, s))
            return is_uninterp_const(s);
        return false;
    }

    void solver::push_core() {

    }

    void solver::pop_core(unsigned n) {
        for (; m_trail_lim < s().init_trail_size(); ++m_trail_lim) {
            auto lit = s().trail_literal(m_trail_lim);
            auto e = ctx.literal2expr(lit);
            if (is_unit(e)) {
                // IF_VERBOSE(1, verbose_stream() << "add unit " << mk_pp(e, m) << "\n");
                std::lock_guard<std::mutex> lock(m_mutex);
                m_units.push_back(e);
                m_has_units = true;
            }
        }
    }
        
    void solver::init_search() {
        init_local_search();
    }

    void solver::init_local_search() {
        if (m_bvsls) {
            m_bvsls->cancel();
            m_thread.join();
            m_result = l_undef;
            m_completed = false;
            m_has_units = false;
            m_model = nullptr;
            m_units.reset();
        }
        // set up state for local search solver here

        m_m = alloc(ast_manager, m);
        ast_translation tr(m, *m_m);
        
        params_ref p;
        m_completed = false;
        m_result = l_undef;
        m_model = nullptr;
        m_bvsls = alloc(bv::sls, *m_m, p);
        
        for (expr* a : ctx.get_assertions())
            m_bvsls->assert_expr(tr(a));

        std::function<bool(expr*, unsigned)> eval = [&](expr* e, unsigned r) {
            return false;
        };

        m_bvsls->init();
        m_bvsls->init_eval(eval);
        m_bvsls->updt_params(s().params());
        m_bvsls->init_unit([&]() { 
            if (!m_has_units)
                return expr_ref(*m_m);
            expr_ref e(m);
            {
                std::lock_guard<std::mutex> lock(m_mutex);
                if (m_units.empty())
                    return expr_ref(*m_m);
                e = m_units.back();
                m_units.pop_back();
            }
            ast_translation tr(m, *m_m);
            return expr_ref(tr(e.get()), *m_m); 
        });
                                     
        m_thread = std::thread([this]() { run_local_search(); });        
    }

    void solver::sample_local_search() {
        if (!m_completed)
            return;        
        m_thread.join();
        m_completed = false;
        m_bvsls->collect_statistics(m_st);
        if (m_result == l_true) {
            IF_VERBOSE(2, verbose_stream() << "(sat.sls :model-completed)\n";);
            auto mdl = m_bvsls->get_model();
            ast_translation tr(*m_m, m);
            m_model = mdl->translate(tr);
            s().set_canceled();
        }
        m_bvsls = nullptr;
    }

    void solver::run_local_search() {
        m_result = (*m_bvsls)();
        m_completed = true;
    }

}
