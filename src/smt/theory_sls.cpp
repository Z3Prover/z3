/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    theory_sls
    
Abstract:

    Interface to Concurrent SLS solver
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-24

--*/


#include "smt/smt_context.h"
#include "ast/sls/sls_context.h"
#include "ast/for_each_expr.h"
#include "smt/theory_sls.h"

namespace smt {

    theory_sls::theory_sls(smt::context& ctx) :
        theory(ctx, ctx.get_manager().mk_family_id("sls"))
    {}

#ifndef SINGLE_THREAD

    theory_sls::~theory_sls() {
        finalize();
    }
    
    params_ref theory_sls::get_params() {
        return ctx.get_params();
    }
    
    void theory_sls::set_value(expr* t, expr* v) {
        ctx.user_propagate_initialize_value(t, v);
    }
    
    void theory_sls::force_phase(sat::literal lit) {
        ctx.force_phase(lit);
    }
    
    void theory_sls::set_has_new_best_phase(bool b) {
        
    }
    
    bool theory_sls::get_best_phase(sat::bool_var v) {
        return ctx.get_assignment(v) == l_true;        
    }
    
    expr* theory_sls::bool_var2expr(sat::bool_var v) {
        return ctx.bool_var2expr(v);
    }
    
    void theory_sls::set_finished() {
        ctx.set_sls_completed();     
    }

    bool theory_sls::get_value(expr* v, expr_ref& value) {
        auto* n = ctx.get_enode(v);
        return n && ctx.get_value(n, value);
    }

    void theory_sls::inc_activity(sat::bool_var v, double inc) {
        ctx.inc_bvar_activity(v, inc);
    }
    
    unsigned theory_sls::get_num_bool_vars() const {
        return ctx.get_num_bool_vars();
    }

    void theory_sls::finalize() {
        if (!m_smt_plugin)
            return;

        m_smt_plugin->finalize(m_model, m_st);
        m_model = nullptr;
        m_smt_plugin = nullptr;        
    }

    void theory_sls::propagate() {
        if (m_smt_plugin && !m_checking) {
            expr_ref_vector fmls(m);
            for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i)
                fmls.push_back(ctx.get_asserted_formula(i));
            m_checking = true;
            vector<sat::literal_vector> clauses;
            m_smt_plugin->check(fmls, clauses);
            return;
        }
        if (!m_smt_plugin || !m_parallel_mode)
            return;
        if (!m_smt_plugin->completed())
            return;
        m_smt_plugin->finalize(m_model, m_st);
        m_smt_plugin = nullptr;
    }    

    void theory_sls::pop_scope_eh(unsigned n) {
        if (!m_smt_plugin)
            return;
        
        unsigned scope_lvl = ctx.get_scope_level();
        if (ctx.get_search_level() == scope_lvl - n) {
            auto& lits = ctx.assigned_literals();
            for (; m_trail_lim < lits.size() && ctx.get_assign_level(lits[m_trail_lim]) == scope_lvl; ++m_trail_lim) 
                m_smt_plugin->add_unit(lits[m_trail_lim]);            
        }

        ++m_difference_score; // blindly assume we backtrack over initial clauses.
#if 0
        if (ctx.has_new_best_phase())
            m_smt_plugin->import_phase_from_smt();

#endif        
    }       

    void theory_sls::init() {
        if (m_smt_plugin) 
            finalize();
        smt_params p(ctx.get_fparams());
        m_parallel_mode = p.m_sls_parallel;
        m_smt_plugin = alloc(sls::smt_plugin, *this);    
        m_checking = false;
    }

    void theory_sls::collect_statistics(::statistics& st) const {
        st.copy(m_st);
    }

    void theory_sls::restart_eh() {
        if (m_parallel_mode || !m_smt_plugin)
            return;

        if (ctx.m_stats.m_num_restarts >= m_threshold + 5) {                      
            m_threshold *= 2;
            bounded_run(m_restart_ls_steps);
            m_smt_plugin->sls_activity_to_smt();
        }
        m_difference_score = 0;
        m_difference_score_threshold = 1;
    }

    void theory_sls::bounded_run(unsigned num_steps) {       
        m_smt_plugin->bounded_run(num_steps);
        if (m_smt_plugin->result() == l_true) {
            m_smt_plugin->finalize(m_model, m_st);
            m_smt_plugin = nullptr;
        }
    }

    final_check_status theory_sls::final_check_eh() {
        if (m_parallel_mode || !m_smt_plugin)
            return FC_DONE;
        if (m_difference_score < m_difference_score_threshold + 100)
            return FC_DONE;

        ++m_difference_score_threshold;
        m_difference_score = 0;
        ++m_num_guided_sls;

        m_smt_plugin->smt_phase_to_sls();
        m_smt_plugin->smt_values_to_sls();
        bounded_run(m_final_check_ls_steps);
        dec_final_check_ls_steps();
        m_smt_plugin->sls_phase_to_smt();
        m_smt_plugin->sls_values_to_smt();
        if (m_num_guided_sls % 20 == 0) 
            m_smt_plugin->sls_activity_to_smt();

        return FC_DONE;
    }

    void theory_sls::display(std::ostream& out) const {
        out << "theory-sls\n";
    } 

#endif
}
