/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    theory_sls
    
Abstract:

    Interface to Concurrent SLS solver
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-24

--*/

#include "smt/theory_sls.h"
#include "smt/smt_context.h"
#include "ast/sls/sls_context.h"
#include "ast/for_each_expr.h"

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
    
    void theory_sls::initialize_value(expr* t, expr* v) {
        ctx.user_propagate_initialize_value(t, v);
    }
    
    void theory_sls::force_phase(sat::literal lit) {
        ctx.force_phase(lit);
    }
    
    void theory_sls::set_has_new_best_phase(bool b) {
        
    }
    
    bool theory_sls::get_best_phase(sat::bool_var v) {
        return false;
    }
    
    expr* theory_sls::bool_var2expr(sat::bool_var v) {
        return ctx.bool_var2expr(v);
    }
    
    void theory_sls::set_finished() {
        m.limit().cancel();
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
        if (!m_smt_plugin)
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
#if 0
        if (ctx.has_new_best_phase())
            m_smt_plugin->import_phase_from_smt();

#endif
        
        m_smt_plugin->import_from_sls();        
    }       

    void theory_sls::init() {
        if (m_smt_plugin) 
            finalize();
        m_smt_plugin = alloc(sls::smt_plugin, *this);    
        m_checking = false;
    }

    void theory_sls::collect_statistics(::statistics& st) const {
        st.copy(m_st);
    }

    void theory_sls::display(std::ostream& out) const {
        out << "theory-sls\n";
    }



#endif
}
