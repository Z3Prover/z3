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
            bool   config_initialized = false;
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
            unsigned propagation_base = 1000;
            bool ucb = true;
            double ucb_constant = 1.0;
            double ucb_forget = 0.1;
            bool ucb_init = false;
            double ucb_noise = 0.1;
            bool   use_top_level_assertions = true;
            bool   use_lookahead_bv = true;
            bool   allow_rotation = true;
        };

        struct stats {
            unsigned m_lookaheads = 0;
            unsigned m_moves = 0;
            unsigned m_restarts = 0;
            unsigned m_propagations = 0;
            unsigned m_random_flips = 0;
            unsigned m_rotations = 0;
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
        ptr_vector<expr> m_bv_restore;
        svector<std::pair<expr*, bool>> m_bool_restore;
        vector<vector<std::pair<app*, bool>>> m_update_stack;
        expr_mark m_in_update_stack;
        double m_best_score = 0, m_top_score = 0;
        bvect m_best_value;
        expr* m_best_expr = nullptr;
        expr* m_last_atom = nullptr;
        ptr_vector<expr> m_empty_vars;
        vector<bool_info> m_bool_info;
        expr_mark m_is_root;
        unsigned m_touched = 1;
        sat::bool_var_set m_rotated;            

        std::ostream& display_weights(std::ostream& out);

        bv_valuation& wval(expr* e) const;

        unsigned m_max_depth = 0, m_min_depth = 0;
        void populate_update_stack(expr* e);
        void clear_update_stack();
        bool insert_update_stack(expr* e);
        void insert_update(expr* e, bool is_bv);        

        bool_info& get_bool_info(expr* e);
        double lookahead_update(expr* u, bvect const& new_value);
        double old_score(expr* c) { return get_bool_info(c).score; }
        void   set_score(expr* c, double d) { get_bool_info(c).score = d; }
        double new_score(expr* c, bool is_true);
        double new_score(expr* c);

        double lookahead_flip(sat::bool_var v);

        void rescore();

        unsigned get_weight(expr* e) { return get_bool_info(e).weight; }
        void     inc_weight(expr* e) { ++get_bool_info(e).weight; }
        void     dec_weight(expr* e);
        void     recalibrate_weights();
        bool     is_root(expr* e) { return m_is_root.is_marked(e); }

        void ucb_forget();
        unsigned get_touched(expr* e) { return get_bool_info(e).touched; }
        void set_touched(expr* e, unsigned t) { get_bool_info(e).touched = t; }
        void inc_touched(expr* e) { ++get_bool_info(e).touched; }

        enum class move_type { random_t, guided_t, move_t, reset_t };
        friend std::ostream& operator<<(std::ostream& out, move_type mt);


        bool allow_costly_flips(move_type mt);
        void try_set(expr* u, bvect const& new_value);
        void try_flip(expr* u);
        void add_updates(expr* u);
        bool apply_update(expr* p, expr* t, bvect const& new_value, move_type mt);
        bool apply_random_move(ptr_vector<expr> const& vars);
        bool apply_guided_move(ptr_vector<expr> const& vars);
        bool apply_random_update(ptr_vector<expr> const& vars);
        ptr_vector<expr> const& get_candidate_uninterp();

        void check_restart();
        void reset_uninterp_in_false_literals();
        bool is_bv_literal(sat::literal lit);

        void search();

        class root_assertions {
            bv_lookahead& m_la;
            unsigned idx = 0;
            void next();
        public:
            root_assertions(bv_lookahead& la, bool start);

            expr* operator*() const;

            root_assertions& operator++() {
                ++idx;
                next();
                return *this;
            }

            bool operator!=(root_assertions const& other) const {
                return idx != other.idx;
            }

            bool operator==(root_assertions const& other) const {
                return idx == other.idx;
            }
        };
        class root_assertion_iterator {
            bv_lookahead& m_la;

        public:
            root_assertion_iterator(bv_lookahead& la) : m_la(la) {}
            root_assertions begin() { return root_assertions(m_la, true); }
            root_assertions end() { return root_assertions(m_la, false); }
        };

        root_assertion_iterator get_root_assertions() {
            return root_assertion_iterator(*this);
        }

        bool assertion_is_true(expr* a);

        void initialize_bool_values();

        void finalize_bool_values();

        void updt_params(params_ref const& p);

    public:
        bv_lookahead(bv_eval& ev);

        void start_propagation();

        void collect_statistics(statistics& st) const;

    };
}