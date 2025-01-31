/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_smt_plugin.cpp

Abstract:

    A Stochastic Local Search (SLS) Plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-10
    
--*/


#include "ast/sls/sls_smt_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "smt/params/smt_params_helper.hpp"

namespace sls {

    smt_plugin::smt_plugin(smt_context& ctx) :
        ctx(ctx),
        m(ctx.get_manager()),
        m_sls(),
        m_sync(),
        m_smt2sync_tr(m, m_sync),
        m_smt2sls_tr(m, m_sls),
        m_sls2sync_tr(m_sls, m_sync),
        m_sls2smt_tr(m_sls, m),
        m_sync2sls_tr(m_sync, m_sls),
        m_sync_uninterp(m_sync),
        m_sls_uninterp(m_sls),
        m_sync_values(m_sync),
        m_context(m_sls, *this)
    {
    }
    
    smt_plugin::~smt_plugin() {
        SASSERT(!m_ddfw);
    }
    
    void smt_plugin::check(expr_ref_vector const& fmls, vector <sat::literal_vector> const& clauses) {
        SASSERT(!m_ddfw);
        // set up state for local search theory_sls here
        
        m_result = l_undef;
        m_completed = false;
        m_units.reset();
        m_has_units = false;
        m_sls_model = nullptr;
        m_ddfw = alloc(sat::ddfw);
        m_ddfw->set_plugin(this);
        m_ddfw->updt_params(ctx.get_params());
        m_context.updt_params(ctx.get_params());

        for (auto const& clause : clauses) {
            m_ddfw->add(clause.size(), clause.data());
            for (auto lit : clause) 
                add_shared_var(lit.var(), lit.var());
        }

        for (auto v : m_shared_bool_vars) {
            expr* e = ctx.bool_var2expr(v);
            if (!e)
                continue;
            m_context.register_atom(v, m_smt2sls_tr(e));
            for (auto t : subterms::all(expr_ref(e, m)))
                add_shared_term(t);
        }

        for (auto fml : fmls) 
            m_context.add_input_assertion(m_smt2sls_tr(fml));     

        for (unsigned v = 0; v < ctx.get_num_bool_vars(); ++v) {
            expr* e = ctx.bool_var2expr(v);
            if (!e)
                continue;

            expr_ref sls_e(m_sls);
            sls_e = m_smt2sls_tr(e);
            auto w = m_context.atom2bool_var(sls_e);            
            if (w == sat::null_bool_var)
                continue;
            add_shared_var(v, w); 
            for (auto t : subterms::all(expr_ref(e, m)))
                add_shared_term(t);
        }

        if (ctx.parallel_mode())
            m_thread = std::thread([this]() { run(); });
        else
            m_completed = true;
    }

    void smt_plugin::run() {
        if (!m_ddfw)
            return;
        try {
            m_result = m_ddfw->check(0, nullptr);
        }
        catch (std::exception& ex) {
            IF_VERBOSE(0, verbose_stream() << "sls-exception " << ex.what() << "\n");
            m_result = l_undef;
        }
        IF_VERBOSE(3, verbose_stream() << "sls-result " << m_result << "\n");
        for (auto v : m_shared_bool_vars) {
            auto w = m_smt_bool_var2sls_bool_var[v];
            m_rewards[v] = m_ddfw->get_reward_avg(w);
        }
        m_completed = true;   
    }

    void smt_plugin::bounded_run(unsigned max_iterations) {
        IF_VERBOSE(3, verbose_stream() << "(sls-bounded :" << max_iterations << ")\n");
        m_ddfw->rlimit().reset_count();
        m_ddfw->rlimit().push(max_iterations);
        {
            scoped_limits _sl(m.limit());
            _sl.push_child(&m_ddfw->rlimit());
            run();
        }
        m_ddfw->rlimit().pop();
    }
    
    void smt_plugin::finalize(model_ref& mdl, ::statistics& st) {
        auto* d = m_ddfw;
        if (!d)
            return;
        bool canceled = !m_completed;
        IF_VERBOSE(3, verbose_stream() << "finalize\n");
        if (!m_completed) 
            d->rlimit().cancel();  
        if (m_thread.joinable())
            m_thread.join();
        SASSERT(m_completed);
        mdl = nullptr;
        m_ddfw->collect_statistics(st);
        m_context.collect_statistics(st);
        if (m_result == l_true && m_sls_model) {
            ast_translation tr(m_sls, m);
            mdl = m_sls_model->translate(tr);
            TRACE("sls", tout << "model: " << *m_sls_model << "\n";);
            if (!canceled)
                ctx.set_finished();
        }
        m_ddfw = nullptr;
        // m_ddfw owns the pointer to smt_plugin and destructs it.
        dealloc(d); 
    }

    void smt_plugin::get_shared_clauses(vector<sat::literal_vector>& _clauses) {
        _clauses.reset();
        for (auto const& clause : clauses()) {
            if (!all_of(clause.m_clause, [&](sat::literal lit) { 
                return m_sls_bool_var2smt_bool_var.get(lit.var(), sat::null_bool_var) != sat::null_bool_var; 
                }))
                continue;
            sat::literal_vector cl;
            for (auto lit : clause) 
                cl.push_back(sat::literal(m_sls_bool_var2smt_bool_var[lit.var()], lit.sign()));           
            _clauses.push_back(cl);
        }
    }
        
    std::ostream& smt_plugin::display(std::ostream& out) {
        m_ddfw->display(out);
        m_context.display(out);
        return out;
    }
        
    bool smt_plugin::is_shared(sat::literal lit) {
        auto w = m_smt_bool_var2sls_bool_var.get(lit.var(), sat::null_bool_var);
        if (w != sat::null_bool_var)
            return true;
        auto e = ctx.bool_var2expr(lit.var());
        expr* t = nullptr;
        if (!e)
            return false;
        bv_util bv(m);
        if (bv.is_bit2bool(e, t) && m_shared_terms.contains(t->get_id())) 
            return true;        
        
        // if arith.is_le(e, s, t) && t is a numeral, s is shared-term....
        return false;
    }

    void smt_plugin::add_shared_var(sat::bool_var v, sat::bool_var w) {
        m_smt_bool_var2sls_bool_var.setx(v, w, sat::null_bool_var);
        m_sls_bool_var2smt_bool_var.setx(w, v, sat::null_bool_var);
        m_sls_phase.reserve(v + 1);
        m_sat_phase.reserve(v + 1);
        m_rewards.reserve(v + 1);
        m_shared_bool_vars.insert(v);
    }

    void smt_plugin::add_unit(sat::literal lit) {
        if (!is_shared(lit))
            return;
        std::lock_guard<std::mutex> lock(m_mutex);
        m_units.push_back(lit);
        m_has_units = true;        
    }
    
    void smt_plugin::import_phase_from_smt() {
        if (m_has_new_sat_phase)
            return;
        m_has_new_sat_phase = true;
        IF_VERBOSE(3, verbose_stream() << "new SMT -> SLS phase\n");
        ctx.set_has_new_best_phase(false);
        std::lock_guard<std::mutex> lock(m_mutex);
        for (auto v : m_shared_bool_vars) 
            m_sat_phase[v] = ctx.get_best_phase(v);
    }

    bool smt_plugin::export_to_sls() {    
        bool updated = false;
        if (m_has_units) {            
            std::lock_guard<std::mutex> lock(m_mutex);
            smt_units_to_sls();
            m_has_units = false;
            updated = true;
        }
        if (m_has_new_sat_phase) {
            std::lock_guard<std::mutex> lock(m_mutex);
            export_phase_to_sls();
            m_has_new_sat_phase = false;
            updated = true;
        }
        if (m_has_new_smt_values) {
            std::lock_guard<std::mutex> lock(m_mutex);
            export_values_to_sls();
            m_has_new_smt_values = false;
            updated = true;
        }
        return updated;
    }
    
    void smt_plugin::export_phase_to_sls() {
#if 0
        IF_VERBOSE(2, verbose_stream() << "SMT -> SLS phase\n");
        for (auto v : m_shared_bool_vars) {
            auto w = m_smt_bool_var2sls_bool_var[v];
            if (m_sat_phase[v] != is_true(sat::literal(w, false))) 
                flip(w);            
            m_ddfw->bias(w) = m_sat_phase[v] ? 1 : -1;
        }
#endif
    }

    void smt_plugin::export_values_to_sls() {
        IF_VERBOSE(2, verbose_stream() << "SMT -> SLS values\n");
        for (auto [var, value] : m_sync_var_values) {
            expr_ref var1(m_sls), value1(m_sls);
            var1 = m_sync2sls_tr(var.get());
            value1 = m_sync2sls_tr(value.get());
            if (!var1 || !value1)
                continue;
            m_context.set_value(var1, value1);
        }
    }

    void smt_plugin::smt_phase_to_sls() {
#if 0
        IF_VERBOSE(2, verbose_stream() << "SMT -> SLS phase\n");
        for (auto v : m_shared_bool_vars) {
            auto w = m_smt_bool_var2sls_bool_var[v];
            auto phase = ctx.get_best_phase(v);
            if (phase != is_true(sat::literal(w, false))) 
                flip(w);            
            m_ddfw->bias(w) = phase ? 1 : -1;
        }
#endif
    }

    void smt_plugin::smt_values_to_sls() {

        if (true || ctx.parallel_mode()) {
            std::scoped_lock lock(m_mutex);
            m_sync_var_values.reset();
            for (auto const& [t, t_sync] : m_smt2sync_uninterp) {
                expr_ref val_t(m);
                if (!ctx.get_smt_value(t, val_t))
                    continue;
                auto t_sync_ref = expr_ref(t_sync, m_sync);
                auto val_sync = expr_ref(m_smt2sync_tr(val_t.get()), m_sync);
                m_sync_var_values.push_back({ t_sync_ref, val_sync });
            }
            m_has_new_smt_values = true;
            return;
        }
#if 0
        if (m_value_smt2sls_delay < m_value_smt2sls_delay_threshold) {
            m_value_smt2sls_delay++;
            return;
        }
        m_value_smt2sls_delay_threshold += m_value_smt2sls_delay_threshold/3;
        m_value_smt2sls_delay = 0;
#endif
        IF_VERBOSE(2, verbose_stream() << "SMT -> SLS values\n");
        for (auto const& [t, t_sync] : m_smt2sync_uninterp) {
            expr_ref val_t(m);
            if (!ctx.get_smt_value(t, val_t))
                continue;
            auto t_sls = expr_ref(m_smt2sls_tr(t), m_sls);
            auto val_sls = expr_ref(m_smt2sls_tr(val_t.get()), m_sls);            
            m_context.set_value(t_sls, val_sls);
        }
    }

    void smt_plugin::sls_phase_to_smt() {
        if (!m_has_new_sls_phase)
            return;
#if 0
        IF_VERBOSE(2, verbose_stream() << "SLS -> SMT phase. unsat size: " << m_min_unsat_size << "\n");
        for (auto v : m_shared_bool_vars) 
            ctx.force_phase(sat::literal(v, !m_sls_phase[v]));
#endif
        m_has_new_sls_phase = false;
    }

    void smt_plugin::sls_activity_to_smt() {
        IF_VERBOSE(2, verbose_stream() << "SLS -> SMT activity\n");
        for (auto v : m_shared_bool_vars) 
            ctx.inc_activity(v, 200 * m_rewards[v]);        
    }

    void smt_plugin::smt_units_to_sls() {
        IF_VERBOSE(2, if (!m_units.empty()) verbose_stream() << "SMT -> SLS units " << m_units << "\n");
        for (auto lit : m_units) {
            auto v = lit.var();
            if (m_shared_bool_vars.contains(v)) {
                auto w = m_smt_bool_var2sls_bool_var[v];
                sat::literal sls_lit(w, lit.sign());
                if (m_context.is_unit(sls_lit))
                    continue;
                IF_VERBOSE(3, verbose_stream() << "unit " << sls_lit << "\n");
                m_ddfw->add(1, &sls_lit);
            }
            else {
                IF_VERBOSE(4, verbose_stream() << "value restriction " << lit << " "
                           << mk_bounded_pp(ctx.bool_var2expr(lit.var()), m) << "\n");
            }
        }                
        m_units.reset();
    }

    void smt_plugin::export_from_sls() {
        if (unsat().size() > m_min_unsat_size)
            return;
        m_min_unsat_size = unsat().size();
        export_phase_from_sls();
        export_values_from_sls();
    }

    void smt_plugin::export_phase_from_sls() {
        std::lock_guard<std::mutex> lock(m_mutex);
        for (auto v : m_shared_bool_vars) {
            auto w = m_smt_bool_var2sls_bool_var[v];
            m_rewards[v] = m_ddfw->get_reward_avg(w);
            VERIFY(m_ddfw->get_model().size() > w);
            VERIFY(m_sls_phase.size() > v);
            m_sls_phase[v] = l_true == m_ddfw->get_model()[w];
        }
        m_has_new_sls_phase = true;
    }

    void smt_plugin::export_values_from_sls() {
        IF_VERBOSE(3, verbose_stream() << "export values from sls\n");
        std::lock_guard<std::mutex> lock(m_mutex);
        for (auto const& [t, t_sync] : m_sls2sync_uninterp) {
            expr_ref val_t = m_context.get_value(t);
            auto sync_val = m_sls2sync_tr(val_t.get());
            m_sync_values.setx(t_sync->get_id(), sync_val);
        }
        m_has_new_sls_values = true;
    }        

    void smt_plugin::import_from_sls() {
        export_activity_to_smt();
        if (m_has_new_sls_values) {
            std::lock_guard<std::mutex> lock(m_mutex);
            sls_values_to_smt();
            m_has_new_sls_values = false;
        }
        if (m_has_new_sls_phase) {
            std::lock_guard<std::mutex> lock(m_mutex);
            sls_phase_to_smt();
            m_has_new_sls_phase = false;
        }
    }
    
    void smt_plugin::export_activity_to_smt() {

    }
    
    void smt_plugin::sls_values_to_smt() {
        if (!m_has_new_sls_values)
            return;
        IF_VERBOSE(2, verbose_stream() << "SLS -> SMT values\n");
        ast_translation tr(m_sync, m);
        for (auto const& [t, t_sync] : m_smt2sync_uninterp) {
            expr* sync_val = m_sync_values.get(t_sync->get_id(), nullptr);
            if (!sync_val)
                continue;
            expr_ref val(tr(sync_val), m);
            ctx.set_value(t, val);
        }
        m_has_new_sls_values = false;
    }

    void smt_plugin::add_shared_term(expr* t) {
        m_shared_terms.insert(t->get_id());
        if (is_uninterp(t))
            add_uninterp(t);
    }

    void smt_plugin::add_uninterp(expr* smt_t) {
        auto sync_t = m_smt2sync_tr(smt_t);
        auto sls_t = m_smt2sls_tr(smt_t);
        m_sync_uninterp.push_back(sync_t);
        m_sls_uninterp.push_back(sls_t);
        m_smt2sync_uninterp.insert(smt_t, sync_t);
        m_sls2sync_uninterp.insert(sls_t, sync_t);
    }

    lbool smt_plugin::on_save_model()  {
        TRACE("sls", display(tout));
        lbool r = l_true;
        while (unsat().empty()) {
            r = m_context.check();
            if (!m_new_clause_added)
                break;
            m_ddfw->reinit();
            m_new_clause_added = false;
        }
        export_from_sls();
        return r;
    }
}
