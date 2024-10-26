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

namespace sls {

    smt_plugin::smt_plugin(smt_context& ctx) :
        ctx(ctx),
        m(ctx.get_manager()),
        m_sls(),
        m_sync(),
        m_smt2sync_tr(m, m_sync),
        m_smt2sls_tr(m, m_sls),
        m_sync_uninterp(m_sync),
        m_sls_uninterp(m_sls),
        m_sync_values(m_sync),
        m_context(m_sls, *this)
    {
    }
    
    smt_plugin::~smt_plugin() {
        SASSERT(!m_ddfw);
    }

    
    void smt_plugin::check(expr_ref_vector const& fmls) {
        SASSERT(!m_ddfw);
        // set up state for local search theory_sls here
        m_result = l_undef;
        m_completed = false;
        m_units.reset();
        m_has_units = false;
        m_model = nullptr;
        m_sls_model = nullptr;
        m_ddfw = alloc(sat::ddfw);
        m_ddfw->set_plugin(this);
        m_ddfw->updt_params(ctx.get_params());

        for (auto fml : fmls) 
            m_context.add_constraint(m_smt2sls_tr(fml));     

        // m_context.display(verbose_stream());

        for (unsigned v = 0; v < ctx.get_num_bool_vars(); ++v) {
            expr* e = ctx.bool_var2expr(v);
            if (!e)
                continue;
            for (auto t : subterms::all(expr_ref(e, m))) 
                add_shared_term(e);            

            expr_ref sls_e(m_sls);
            sls_e = m_smt2sls_tr(e);
            auto w = m_context.atom2bool_var(sls_e);            
            if (w != sat::null_bool_var) {
                verbose_stream() << mk_bounded_pp(e, m) << ": " << v << " -> " << w << "\n";
                m_smt_bool_var2sls_bool_var.setx(v, w, sat::null_bool_var);
                m_sls_bool_var2smt_bool_var.setx(w, v, sat::null_bool_var);
                
                add_shared_var(w);            
            }
        }

        m_thread = std::thread([this]() { run(); });
    }

    void smt_plugin::run() {
        if (!m_ddfw)
            return;
        m_result = m_ddfw->check(0, nullptr);
        IF_VERBOSE(1, verbose_stream() << "sls-result " << m_result << "\n");
        m_completed = true;   
    }
    
    void smt_plugin::finalize(model_ref& mdl, ::statistics& st) {
        auto* d = m_ddfw;
        if (!d)
            return;
        bool canceled = !m_completed;
        IF_VERBOSE(0, verbose_stream() << "finalize\n");
        mdl = m_model;
        if (!m_completed) {
            d->rlimit().cancel();
            if (m_thread.joinable())
                m_thread.join();    
        }
        if (m_result == l_true && m_sls_model) {
            ast_translation tr(m_sls, m);
            m_model = m_sls_model->translate(tr);
            TRACE("sls", tout << "model: " << *m_sls_model << "\n";);
            if (!canceled)
                ctx.set_finished();
        }
        m_ddfw = nullptr;
        // m_ddfw owns the pointer to smt_plugin and destructs it.
        dealloc(d); 
    }
        
    void smt_plugin::collect_statistics(statistics& st) {

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
        if (bv.is_bit2bool(e, t) && m_shared_terms.contains(t->get_id())) {
            verbose_stream() << "shared bit2bool " << mk_bounded_pp(e, ctx.get_manager()) << "\n";
            return true;
        }
        
        // if arith.is_le(e, s, t) && t is a numeral, s is shared-term....
        return false;
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
        if (export_units_to_sls())
            updated = true;
        if (export_phase_to_sls())
            updated = true;
        return updated;
    }
    
    bool smt_plugin::export_phase_to_sls() {
        if (!m_has_new_sat_phase)
            return false;
        std::lock_guard<std::mutex> lock(m_mutex);
        IF_VERBOSE(3, verbose_stream() << "SMT -> SLS phase\n");
        for (auto i : m_shared_bool_vars) {
            auto v = m_smt_bool_var2sls_bool_var[i];
            if (m_sat_phase[v] != is_true(sat::literal(v, false))) 
                flip(v);
            m_ddfw->bias(v) = m_sat_phase[v] ? 1 : -1;
        }
        m_has_new_sat_phase = false;
        return true;
    }

    bool smt_plugin::export_units_to_sls() {
        if (!m_has_units)
            return false;
        std::lock_guard<std::mutex> lock(m_mutex);
        IF_VERBOSE(2, verbose_stream() << "SMT -> SLS units " << m_units << "\n");
        for (auto lit : m_units) {
            if (m_shared_bool_vars.contains(lit.var())) {
                sat::literal sls_lit(m_smt_bool_var2sls_bool_var[lit.var()], false);
                IF_VERBOSE(10, verbose_stream() << "unit " << sls_lit << "\n");
                m_ddfw->add(1, &sls_lit);
            }
            else {
                IF_VERBOSE(0, verbose_stream() << "value restriction " << lit << " "
                           << mk_bounded_pp(ctx.bool_var2expr(lit.var()), m) << "\n");
            }
        }        
        m_has_units = false;
        m_units.reset();
        return true;
    }

    void smt_plugin::import_from_sls() {
        if (unsat().size() > m_min_unsat_size)
            return;
        m_min_unsat_size = unsat().size();
        std::lock_guard<std::mutex> lock(m_mutex);            
        for (auto v : m_shared_bool_vars) {
            m_rewards[v] = m_ddfw->get_reward_avg(v);
            m_sls_phase[v] = l_true == m_ddfw->get_model()[v];
            m_has_new_sls_phase = true;
        }
        // import_values_from_sls();
    }

    void smt_plugin::import_values_from_sls() {
        IF_VERBOSE(3, verbose_stream() << "import values from sls\n");
        std::lock_guard<std::mutex> lock(m_mutex);
        for (auto const& [t, t_sync] : m_sls2sync_uninterp) {
            expr_ref val_t = m_context.get_value(t);
            m_sync_values.set(t_sync->get_id(), m_smt2sync_tr(val_t.get()));
        }
        m_has_new_sls_values = true;
    }        


    
    void smt_plugin::export_activity_to_smt() {

    }
    
    void smt_plugin::export_values_to_smt() {

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

    void smt_plugin::add_shared_var(sat::bool_var v) {
        m_sls_phase.reserve(v + 1);
        m_sat_phase.reserve(v + 1);
        m_rewards.reserve(v + 1);
        m_shared_bool_vars.insert(v);
    }

}
