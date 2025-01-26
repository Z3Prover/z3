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
#include "ast/sls/sls_context.h"
#include "ast/for_each_expr.h"

namespace sls {


    solver::solver(euf::solver& ctx) :
        th_euf_solver(ctx, symbol("sls"), ctx.get_manager().mk_family_id("sls"))
    {}

#ifdef SINGLE_THREAD

#else

    solver::~solver() {
        finalize();
    }

    params_ref solver::get_params() {
        return s().params();
    }

    void solver::set_value(expr* t, expr* v) {
        ctx.user_propagate_initialize_value(t, v);
    }

    void solver::force_phase(sat::literal lit) {
        ctx.s().set_phase(lit);
    }

    void solver::set_has_new_best_phase(bool b) {

    }

    bool solver::get_best_phase(sat::bool_var v) {
        return false;
    }

    expr* solver::bool_var2expr(sat::bool_var v) {
        return ctx.bool_var2expr(v);
    }

    void solver::set_finished() {
        ctx.s().set_canceled();
    }

    unsigned solver::get_num_bool_vars() const {
        return s().num_vars();
    }

    void solver::finalize() {
        if (!m_smt_plugin)
            return;
        
        m_smt_plugin->finalize(m_model, m_st);
        m_model = nullptr;
        m_smt_plugin = nullptr;
    }

    bool solver::unit_propagate() {
        force_push();
        if (m_smt_plugin && !m_checking) {
            expr_ref_vector fmls(m);
            m_checking = true;
            m_smt_plugin->check(fmls, ctx.top_level_clauses());
            return true;
        }
        if (!m_smt_plugin)
            return false;
        if (!m_smt_plugin->completed())
            return false;
        m_smt_plugin->finalize(m_model, m_st);
        m_smt_plugin = nullptr;
        return true;
    }

    void solver::pop_core(unsigned n) {
        if (!m_smt_plugin)
            return;

        unsigned scope_lvl = s().scope_lvl();
        if (s().search_lvl() == scope_lvl - n) {
            for (; m_trail_lim < s().init_trail_size(); ++m_trail_lim) {
                auto lit = s().trail_literal(m_trail_lim);
                m_smt_plugin->add_unit(lit);
            }
        }

        m_smt_plugin->import_from_sls();
    }

    void solver::init_search() {
        if (m_smt_plugin)
            finalize();
        m_smt_plugin = alloc(sls::smt_plugin, *this);
        m_checking = false;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out << "theory-sls\n";
    }
     

#endif
}
