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
        ctx.set_internal_completed();     
    }

    bool theory_sls::get_smt_value(expr* v, expr_ref& value) {
        if (!ctx.e_internalized(v))
            return false;
        auto* n = ctx.get_enode(v);
        return n && ctx.get_value(n, value);
    }

    void theory_sls::inc_activity(sat::bool_var v, double inc) {
        ctx.inc_bvar_activity(v, inc);
    }
    
    unsigned theory_sls::get_num_bool_vars() const {
        return ctx.get_num_bool_vars();
    }

    void theory_sls::init_search_eh() {
        m_init_search = true;
    }

    void theory_sls::finalize() const {
        if (!m_smt_plugin)
            return;
        m_smt_plugin->finalize(m_model, m_st);
        m_model = nullptr;
        m_smt_plugin = nullptr;        
        m_init_search = false;
    }

    void theory_sls::propagate() {
        if (!m_init_search)
            return;
        if (!m_smt_plugin)
            m_smt_plugin = alloc(sls::smt_plugin, * this);
        if (!m_checking) {
            expr_ref_vector fmls(m);
            for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i)
                fmls.push_back(ctx.get_asserted_formula(i));
            m_checking = true;
            vector<sat::literal_vector> clauses;
            m_smt_plugin->check(fmls, clauses);
            m_smt_plugin->get_shared_clauses(m_shared_clauses);
        }
        else if (m_parallel_mode && m_smt_plugin->completed()) {
            m_smt_plugin->finalize(m_model, m_st);
            m_smt_plugin = nullptr;
            m_init_search = false;
        }
        else 
            propagate_local_search();
        
    }    

    void theory_sls::pop_scope_eh(unsigned n) {
        if (!m_smt_plugin)
            return;
        
        if (ctx.get_search_level() == ctx.get_scope_level() - n) {
            auto& lits = ctx.assigned_literals();
            for (; m_trail_lim < lits.size() && ctx.get_assign_level(lits[m_trail_lim]) == ctx.get_search_level(); ++m_trail_lim) 
                m_smt_plugin->add_unit(lits[m_trail_lim]);            
        }

        check_for_unassigned_clause_after_resolve();
#if 0
        if (ctx.has_new_best_phase())
            m_smt_plugin->import_phase_from_smt();

#endif            
    }       

    //
    // hybrid-smt uses a heuristic to determine when to restart local search.
    // it is based on when the assignment to shared clauses has a change in literal assignment.
    //
    void theory_sls::check_for_unassigned_clause_after_resolve() {
        if (m_has_unassigned_clause_after_resolve) {
            m_after_resolve_decide_count = 0;
            if (m_after_resolve_decide_gap >= 16)
                m_after_resolve_decide_gap /= 4;
        }
        else if (!shared_clauses_are_true()) {
            m_resolve_count++;
            if (m_resolve_count > m_resolve_gap) {
                m_resolve_gap++;
                m_has_unassigned_clause_after_resolve = true;
                m_resolve_count = 0;
                m_after_resolve_decide_count = 0;
                m_after_resolve_decide_gap = 4;
            }
        }    
    }

    void theory_sls::update_propagation_scope() {
        if (m_propagation_scope > ctx.get_scope_level() && m_propagation_scope == m_max_propagation_scope) {
            m_smt_plugin->smt_values_to_sls();
        }
        m_propagation_scope = ctx.get_scope_level();
        m_max_propagation_scope = std::max(m_max_propagation_scope, m_propagation_scope);
    }

    void theory_sls::propagate_local_search() {
        if (!m_has_unassigned_clause_after_resolve)
            return;
        if (!m_smt_plugin)
            return;
        ++m_after_resolve_decide_count;
        if (100 + m_after_resolve_decide_gap > m_after_resolve_decide_count) {
            //update_propagation_scope();
            return;
        }
        m_after_resolve_decide_gap *= 2;
        if (!shared_clauses_are_true()) {
            update_propagation_scope();
            return;
        }
        m_resolve_count = 0;
        m_has_unassigned_clause_after_resolve = false;
        run_guided_sls();
    }

    void theory_sls::run_guided_sls() {
        m_smt_plugin->smt_values_to_sls();
        if (m_parallel_mode) 
            return;
        
        ++m_stats.m_num_guided_sls;
        m_smt_plugin->smt_phase_to_sls();
        m_smt_plugin->smt_units_to_sls();

        bounded_run(m_final_check_ls_steps);
        dec_final_check_ls_steps();
        if (m_smt_plugin) {
            m_smt_plugin->sls_phase_to_smt();
            m_smt_plugin->sls_values_to_smt();
            if (m_stats.m_num_guided_sls % 20 == 0)
                m_smt_plugin->sls_activity_to_smt();
        }
    }

    void theory_sls::init() {
        if (m_smt_plugin) 
            finalize();
        smt_params p(ctx.get_fparams());
        m_parallel_mode = p.m_sls_parallel;
        m_smt_plugin = nullptr;
        m_checking = false;
        m_init_search = false;
    }

    void theory_sls::collect_statistics(::statistics& st) const {
        finalize();
        st.copy(m_st);
        st.update("sls-num-guided-search", m_stats.m_num_guided_sls);
        st.update("sls-num-restart-search", m_stats.m_num_restart_sls);
    }

    void theory_sls::restart_eh() {
        if (m_parallel_mode || !m_smt_plugin)
            return;

        if (ctx.m_stats.m_num_restarts >= m_restart_gap + 5) {                      
            m_restart_gap *= 2;
            m_smt_plugin->smt_units_to_sls();
            ++m_stats.m_num_restart_sls;
            bounded_run(m_restart_ls_steps);
            inc_restart_ls_steps();
            if (m_smt_plugin)
                m_smt_plugin->sls_activity_to_smt();
        }
    }

    void theory_sls::bounded_run(unsigned num_steps) {       
        m_smt_plugin->bounded_run(num_steps);
        if (m_smt_plugin->result() == l_true) {
            m_smt_plugin->finalize(m_model, m_st);
            m_smt_plugin = nullptr;
            m_init_search = false;
        }
    }

    final_check_status theory_sls::final_check_eh() {
        if (!m_smt_plugin)
            return FC_DONE;
        ++m_after_resolve_decide_count;
        if (m_after_resolve_decide_gap > m_after_resolve_decide_count)
            return FC_DONE;
        m_after_resolve_decide_gap *= 2;
        run_guided_sls();
        return FC_DONE;
    }

    bool theory_sls::shared_clauses_are_true() const {
#if 0
        for (auto const& cl : m_shared_clauses) {
            for (auto lit : cl)
                verbose_stream() << lit << " : " << ctx.get_assignment(lit);
            verbose_stream() << "\n";
        }
#endif
        for (auto const& cl : m_shared_clauses)
            if (all_of(cl, [this](sat::literal lit) { return ctx.get_assignment(lit) != l_true; }))
                return false;
        return true;
    }

    void theory_sls::display(std::ostream& out) const {
        out << "theory-sls\n";
    } 

#endif
}
