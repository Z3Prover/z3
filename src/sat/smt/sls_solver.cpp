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

#ifdef SINGLE_THREAD

    solver::solver(euf::solver& ctx) :
        th_euf_solver(ctx, symbol("sls"), ctx.get_manager().mk_family_id("sls"))
        {}

#else
    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("sls"), ctx.get_manager().mk_family_id("sls"))
        {}

    solver::~solver() {
        finalize();
    }


    class solver::smt_plugin : public sat::local_search_plugin, public sls::sat_solver_context {
        ast_manager& m;
        solver& s;
        sat::ddfw* m_ddfw;
        sls::context m_context;
        bool m_new_clause_added = false; 
        unsigned m_min_unsat_size = UINT_MAX;
        ast_manager m_sync_manager;
        obj_map<expr, expr*> m_sls2sync_uninterp; // hashtable from sls-uninterp to sync uninterp
        obj_map<expr, expr*> m_smt2sync_uninterp; // hashtable from external uninterp to sync uninterp
        ast_translation m_smt2sync_tr, m_smt2sls_tr;
        expr_ref_vector m_sync_uninterp; 
        expr_ref_vector m_sync_values;
        std::atomic<bool> m_has_new_sls_values = false;     
        
        // export from SAT to SLS:
        // - unit literals
        // - phase

        bool export_units_to_sls() {
            if (!s.m_has_units)
                return false;
            std::lock_guard<std::mutex> lock(s.m_mutex);
            IF_VERBOSE(3, verbose_stream() << "SMT -> SLS units " << s.m_units << "\n");
            for (auto lit : s.m_units)
                if (m_shared_vars.contains(lit.var())) {
                    IF_VERBOSE(10, verbose_stream() << "unit " << lit << "\n");                        
                    m_ddfw->add(1, &lit);
                }
            s.m_has_units = false;
            s.m_units.reset();
            return true;
        }

        bool export_phase_to_sls() {
            if (!m_has_new_sat_phase)
                return false;
            std::lock_guard<std::mutex> lock(s.m_mutex);
            IF_VERBOSE(3, verbose_stream() << "SMT -> SLS phase\n");
            for (auto i : m_shared_vars) {
                if (m_sat_phase[i] != is_true(sat::literal(i, false))) 
                    flip(i);
                m_ddfw->bias(i) = m_sat_phase[i] ? 1 : -1;
            }
            m_has_new_sat_phase = false;
            return true;
        }

        bool export_to_sls() {
            bool updated = false;
            if (export_units_to_sls())
                updated = true;
            if (export_phase_to_sls())
                updated = true;
            return updated;
        }
        
        // import from SLS:
        // - phase
        // - values
        // - activity
        void import_from_sls() {
            if (unsat().size() > m_min_unsat_size)
                return;
            m_min_unsat_size = unsat().size();
            std::lock_guard<std::mutex> lock(s.m_mutex);            
            for (auto v : m_shared_vars) {
                m_rewards[v] = m_ddfw->get_reward_avg(v);
                m_sls_phase[v] = l_true == m_ddfw->get_model()[v];
                m_has_new_sls_phase = true;
            }
            // import_values_from_sls();
        }

        void import_values_from_sls() {
            IF_VERBOSE(3, verbose_stream() << "import values from sls\n");
            std::lock_guard<std::mutex> lock(s.m_mutex);
            ast_translation tr(m, m_sync_manager);
            for (auto const& [t, t_sync] : m_sls2sync_uninterp) {
                expr_ref val_t = m_context.get_value(t);
                m_sync_values.set(t_sync->get_id(), tr(val_t.get()));
            }
            m_has_new_sls_values = true;
        }        
        

    public:
        smt_plugin(ast_manager& m, solver& s, sat::ddfw* d) : 
	    m(m), s(s), m_ddfw(d), m_context(m, *this),
            m_sync_uninterp(m_sync_manager),
            m_sync_values(m_sync_manager),
            m_smt2sync_tr(s.ctx.get_manager(), m_sync_manager),
            m_smt2sls_tr(s.ctx.get_manager(), m)
        {            
        }

        uint_set m_shared_vars;
        svector<bool> m_sat_phase;
        std::atomic<bool> m_has_new_sat_phase = false;

        std::atomic<bool> m_has_new_sls_phase = false;
        svector<bool> m_sls_phase;

        svector<double> m_rewards;

        void add_uninterp(expr* smt_t) {
            auto sync_t = m_smt2sync_tr(smt_t);
            auto sls_t = m_smt2sls_tr(smt_t);
            m_sync_uninterp.push_back(sync_t);
            m_smt2sync_uninterp.insert(smt_t, sync_t);
            m_sls2sync_uninterp.insert(sls_t, sync_t);
        }

        void add_shared_var(sat::bool_var v) {
            m_sls_phase.reserve(v + 1);
            m_sat_phase.reserve(v + 1);
            m_rewards.reserve(v + 1);
            m_shared_vars.insert(v);
        }
        
        void init_search() override {}

        void finish_search() override {}

        void on_rescale() override {}

        void on_restart() override {
            if (export_to_sls())
                m_ddfw->reinit();
        }

        void on_save_model() override {
            TRACE("sls", display(tout));
            while (unsat().empty()) {
                m_context.check();
                if (!m_new_clause_added)
                    break;
                m_ddfw->reinit();
                m_new_clause_added = false;
            }
            //import_from_sls();
        }

        void on_model(model_ref& mdl) override {
            IF_VERBOSE(3, verbose_stream() << "on-model " << "\n");
            s.m_sls_model = mdl;
        }

        void register_atom(sat::bool_var v, expr* e) {
            m_context.register_atom(v, e);
        }

        std::ostream& display(std::ostream& out) {
            m_ddfw->display(out);
            m_context.display(out);
            return out;
        }

        vector<sat::clause_info> const& clauses() const override { return m_ddfw->clauses(); }
        sat::clause_info const& get_clause(unsigned idx) const override { return m_ddfw->get_clause_info(idx); }
        ptr_iterator<unsigned> get_use_list(sat::literal lit) override { return m_ddfw->use_list(lit); }
        void flip(sat::bool_var v) override { 
            m_ddfw->flip(v);
        }
        double reward(sat::bool_var v) override { return m_ddfw->get_reward(v); }
        double get_weigth(unsigned clause_idx) override { return m_ddfw->get_clause_info(clause_idx).m_weight; }
        bool is_true(sat::literal lit) override { 
                return m_ddfw->get_value(lit.var()) != lit.sign(); 
        }
        unsigned num_vars() const override { return m_ddfw->num_vars(); }
        indexed_uint_set const& unsat() const override { return m_ddfw->unsat_set(); }
        sat::bool_var add_var() override { 
            return m_ddfw->add_var(); 
        }
        void add_clause(unsigned n, sat::literal const* lits) override { 
            m_ddfw->add(n, lits);
            m_new_clause_added = true;
        }
        void force_restart() override { m_ddfw->force_restart(); }

        void export_values_to_smt() {
            if (!m_has_new_sls_values)
                return;
            IF_VERBOSE(3, verbose_stream() << "SLS -> SMT values\n");
            std::lock_guard<std::mutex> lock(s.m_mutex);
            ast_translation tr(m_sync_manager, s.ctx.get_manager());
            for (auto const& [t, t_sync] : m_smt2sync_uninterp) {
                expr* sync_val = m_sync_values.get(t_sync->get_id(), nullptr);
                if (sync_val) 
                    s.ctx.user_propagate_initialize_value(t, tr(sync_val));
            }
            m_has_new_sls_values = false;
        }

        void export_phase_to_smt() {
            if (!m_has_new_sls_phase)
                return;
            IF_VERBOSE(3, verbose_stream() << "new SLS -> SMT phase\n");
            std::lock_guard<std::mutex> lock(s.m_mutex);
            for (unsigned i = 0; i < m_sls_phase.size(); ++i)
                s.s().set_phase(sat::literal(i, !m_sls_phase[i]));
            m_has_new_sls_phase = false;
        }

        void import_phase_from_smt() {
            if (m_has_new_sat_phase)
                return;
            m_has_new_sat_phase = true;
            IF_VERBOSE(3, verbose_stream() << "new SMT -> SLS phase\n");
            s.s().set_has_new_best_phase(false);
            std::lock_guard<std::mutex> lock(s.m_mutex);
            for (auto v : m_shared_vars) 
                m_sat_phase[v] = s.s().get_best_phase(v);            
        }

        void export_activity_to_smt() {
            // TODO
        }

    };

    void solver::finalize() {
        if (!m_completed && m_ddfw) {
            m_ddfw->rlimit().cancel();
            m_thread.join();            
            m_ddfw->collect_statistics(m_st);
            m_ddfw = nullptr;
            m_slsm = nullptr;
            m_smt_plugin = nullptr;
            m_units.reset();
        }
    }

    sat::check_result solver::check() { 
        return sat::check_result::CR_DONE; 
    }

    bool solver::unit_propagate() {
        force_push();
        sample_local_search();
        return false;
    }

    void solver::pop_core(unsigned n) {
        if (!m_smt_plugin)
            return;
        for (; m_trail_lim < s().init_trail_size(); ++m_trail_lim) {
            auto lit = s().trail_literal(m_trail_lim);
            if (!m_smt_plugin->m_shared_vars.contains(lit.var()))
                continue;
            IF_VERBOSE(10, verbose_stream() << "push unit " << lit << " " << mk_bounded_pp(ctx.literal2expr(lit), m) << "\n");
            std::lock_guard<std::mutex> lock(m_mutex);
            m_units.push_back(lit);
            m_has_units = true;
        }        
        if (s().has_new_best_phase())
            m_smt_plugin->import_phase_from_smt();
        
        m_smt_plugin->export_phase_to_smt();
        m_smt_plugin->export_activity_to_smt();        
        m_smt_plugin->export_values_to_smt();
    }       


    void solver::init_search() {
        if (m_ddfw) {
            m_ddfw->rlimit().cancel();
            m_thread.join();
        }
        // set up state for local search solver here
        m_result = l_undef;
        m_completed = false;
        m_slsm = alloc(ast_manager);
        m_units.reset();
        m_has_units = false;
        m_model = nullptr;
        m_sls_model = nullptr;
        m_ddfw = alloc(sat::ddfw);
        ast_translation tr(m, *m_slsm);
        scoped_limits scoped_limits(m.limit());
        scoped_limits.push_child(&m_slsm->limit());
        scoped_limits.push_child(&m_ddfw->rlimit());
        m_smt_plugin = alloc(smt_plugin, *m_slsm, *this, m_ddfw.get());
        m_ddfw->set_plugin(m_smt_plugin);
        m_ddfw->updt_params(s().params());
        for (auto const& clause : ctx.top_level_clauses()) {
            m_ddfw->add(clause.size(), clause.data());
            for (auto lit : clause)
                m_smt_plugin->add_shared_var(lit.var());
        }
        for (auto v : m_smt_plugin->m_shared_vars) {
            expr* e = ctx.bool_var2expr(v);
            if (!e)
                continue;
            m_smt_plugin->register_atom(v, tr(e));
            for (auto t : subterms::all(expr_ref(e, m))) {
                if (is_uninterp(t))                    
                    m_smt_plugin->add_uninterp(t);                
            }
        }

        m_thread = std::thread([this]() { run_local_search_async(); });        
    }

    void solver::sample_local_search() {
        if (!m_completed)
            return;        
        m_thread.join();
        local_search_done();
    }

    void solver::local_search_done() {
        IF_VERBOSE(1, verbose_stream() << "local-search-done\n");
        m_completed = false;

        CTRACE("sls", m_smt_plugin, m_smt_plugin->display(tout));
        if (m_ddfw)
            m_ddfw->collect_statistics(m_st);

        TRACE("sls", tout << "result " << m_result << "\n");

        if (m_result == l_true && m_sls_model) {
            ast_translation tr(*m_slsm, m);
            m_model = m_sls_model->translate(tr);
            TRACE("sls", tout << "model: " << *m_sls_model << "\n";);
            s().set_canceled();
        }
        m_ddfw = nullptr;
        m_smt_plugin = nullptr;
        m_sls_model = nullptr;
    }

    void solver::run_local_search_async() {
        if (m_ddfw) {
            m_result = m_ddfw->check(0, nullptr);
            IF_VERBOSE(1, verbose_stream() << "sls-result " << m_result << "\n");
            m_completed = true;
        }
    }

    void solver::run_local_search_sync() {
        m_result = m_ddfw->check(0, nullptr);
        local_search_done();
    }

    std::ostream& solver::display(std::ostream& out) const {
        out << "sls-solver\n";
        return out;
    }
#endif
}
