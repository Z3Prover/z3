/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_smt_plugin.h

Abstract:

    A Stochastic Local Search (SLS) Plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-10
    
--*/

#pragma once

#include "ast/sls/sls_context.h"
#include "ast/sls/sat_ddfw.h"
#include "util/statistics.h"
#include <thread>
#include <mutex>

namespace sls {

    class smt_context {
    public:
        virtual ~smt_context() {}
        virtual ast_manager& get_manager() = 0;
        virtual params_ref get_params() = 0;
        virtual void initialize_value(expr* t, expr* v) = 0;
        virtual void force_phase(sat::literal lit) = 0;
        virtual void set_has_new_best_phase(bool b) = 0;
        virtual bool get_best_phase(sat::bool_var v) = 0;
        virtual expr* bool_var2expr(sat::bool_var v) = 0;
        virtual void set_finished() = 0;
        virtual unsigned get_num_bool_vars() const = 0;
    };


    //
    // m is accessed by the main thread
    // m_sls  is accessed by the sls thread
    // m_sync is accessed by both
    //
    class smt_plugin : public sat::local_search_plugin, public sat_solver_context {
        smt_context& ctx;
        ast_manager& m;
        ast_manager  m_sls;
        ast_manager  m_sync;
        ast_translation m_smt2sync_tr, m_smt2sls_tr;
        expr_ref_vector m_sync_uninterp, m_sls_uninterp; 
        expr_ref_vector m_sync_values;
        sat::ddfw* m_ddfw = nullptr;
        sls::context m_context;
        std::atomic<lbool> m_result;
        std::atomic<bool> m_completed, m_has_units;
        std::thread m_thread;
        std::mutex  m_mutex;

        sat::literal_vector m_units;
        model_ref m_sls_model;
        ::statistics m_st;
        bool m_new_clause_added = false; 
        unsigned m_min_unsat_size = UINT_MAX;
        obj_map<expr, expr*> m_sls2sync_uninterp; // hashtable from sls-uninterp to sync uninterp
        obj_map<expr, expr*> m_smt2sync_uninterp; // hashtable from external uninterp to sync uninterp
        std::atomic<bool> m_has_new_sls_values = false;
        uint_set m_shared_bool_vars, m_shared_terms;
        svector<bool> m_sat_phase;
        std::atomic<bool> m_has_new_sat_phase = false;
        std::atomic<bool> m_has_new_sls_phase = false;
        svector<bool> m_sls_phase;
        svector<double> m_rewards;
        svector<sat::bool_var> m_smt_bool_var2sls_bool_var, m_sls_bool_var2smt_bool_var;
        
        bool is_shared(sat::literal lit);
        void run();
        void add_shared_term(expr* t);
        void add_uninterp(expr* smt_t);
        void add_shared_var(sat::bool_var v, sat::bool_var w);

        void import_phase_from_smt();
        void import_values_from_sls();
        void export_values_from_sls();
        void import_activity_from_sls();
        bool export_phase_to_sls();
        bool export_units_to_sls();
        void export_values_to_smt();
        void export_activity_to_smt();
        void export_phase_to_smt();

        void export_from_sls();

        friend class sat::ddfw;
        ~smt_plugin();

    public:
        smt_plugin(smt_context& ctx);

        // interface to calling solver:
        void check(expr_ref_vector const& fmls, vector <sat::literal_vector> const& clauses);
        void finalize(model_ref& md, ::statistics& st);
        void updt_params(params_ref& p) {}
        std::ostream& display(std::ostream& out) override;

        bool export_to_sls();
        void import_from_sls();
        bool completed() { return m_completed; }
        void add_unit(sat::literal lit);

        // local_search_plugin:
        void on_restart() override {
            if (export_to_sls())
                m_ddfw->reinit();
        }

        void on_save_model() override;

        void on_model(model_ref& mdl) override {
            IF_VERBOSE(3, verbose_stream() << "on-model " << "\n");
            m_sls_model = mdl;
        }

        void init_search() override {}

        void finish_search() override {}

        void on_rescale() override {}


        
        // sat_solver_context:
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
    };
}
