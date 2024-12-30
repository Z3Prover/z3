/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_lookahead.h

Abstract:

    Lookahead solver for BV, modeled after sls_engine/sls_tracker/sls_evaluator.

Author:

    Nikolaj Bjorner (nbjorner) 2024-12-26

--*/
#pragma once

#include "ast/bv_decl_plugin.h"
#include "ast/sls/sls_context.h"
#include "ast/sls/sls_bv_valuation.h"

namespace sls {
    class bv_eval;

    class bv_lookahead {

        struct config {
            double cb = 2.85;
            unsigned paws_init = 40;
            unsigned paws_sp = 52;
            bool paws = true;
            bool walksat = true;
            bool walksat_repick = false;
            unsigned wp = 100;
            unsigned restart_base = 1000;
            unsigned restart_next = 1000;
            unsigned restart_init = 1000;
            bool early_prune = true;
            unsigned max_moves = 0;
            unsigned max_moves_base = 800;
            unsigned propagation_base = 10000;
            bool ucb = true;
            double ucb_constant = 1.0;
            double ucb_forget = 0.1;
            bool ucb_init = false;
            double ucb_noise = 0.1;
        };

        struct stats {
            unsigned m_num_lookahead = 0;
            unsigned m_num_updates = 0;
            unsigned m_moves = 0;
            unsigned m_restarts = 0;
            unsigned m_num_propagations = 0;
        };

        struct bool_info {
            unsigned weight = 40;
            double score = 0;
            unsigned touched = 1;
        };

        bv_util bv;
        bv_eval& m_ev;
        context& ctx;
        ast_manager& m;
        config m_config;
        stats m_stats;
        bvect m_v_saved, m_v_updated;
        ptr_vector<expr> m_restore;
        vector<ptr_vector<app>> m_update_stack;
        expr_mark m_on_restore, m_in_update_stack;
        double m_best_score = 0, m_top_score = 0;
        bvect m_best_value;
        expr* m_best_expr = nullptr;
        ptr_vector<expr> m_empty_vars;
        obj_map<expr, bool_info> m_bool_info;
        expr_mark m_is_root;
        unsigned m_touched = 1;

        std::ostream& display_weights(std::ostream& out);

        bv_valuation& wval(expr* e) const;

        void insert_update_stack(expr* e);
        bool insert_update(expr* e);        
        void restore_lookahead();

        bool_info& get_bool_info(expr* e);
        double lookahead_update(expr* u, bvect const& new_value);
        double old_score(app* c) { return get_bool_info(c).score; }
        void   set_score(app* c, double d) { get_bool_info(c).score = d; }
        double new_score(app* c);

        void rescore();

        unsigned get_weight(expr* e) { return get_bool_info(e).weight; }
        void     inc_weight(expr* e) { ++get_bool_info(e).weight; }
        void     dec_weight(expr* e);
        void     recalibrate_weights();
        bool     is_root(expr* e) { return m_is_root.is_marked(e); }

        void ucb_forget();
        unsigned get_touched(app* e) { return get_bool_info(e).touched; }
        void set_touched(app* e, unsigned t) { get_bool_info(e).touched = t; }
        void inc_touched(app* e) { ++get_bool_info(e).touched; }

        void try_set(expr* u, bvect const& new_value);
        void add_updates(expr* u);
        void apply_update(expr* e, bvect const& new_value, char const* reason);
        bool apply_random_move(ptr_vector<expr> const& vars);
        bool apply_guided_move(ptr_vector<expr> const& vars);
        bool apply_random_update(ptr_vector<expr> const& vars);
        ptr_vector<expr> const& get_candidate_uninterp();

        void check_restart();
        void reset_uninterp_in_false_literals();
        bool is_bv_literal(sat::literal lit);
        bool is_false_bv_literal(sat::literal lit);

        void search();



    public:
        bv_lookahead(bv_eval& ev);

        void updt_params(params_ref const& p);

        void start_propagation();

        bool on_restore(expr* e) const;

        void collect_statistics(statistics& st) const;

    };
}