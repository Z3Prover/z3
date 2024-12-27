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
        };

        struct update {
            expr* e;
            double score;
            bvect value;
        };

        struct stats {
            unsigned m_num_lookahead = 0;
            unsigned m_num_updates = 0;
        };


        bv_util bv;
        bv_eval& m_ev;
        context& ctx;
        ast_manager& m;
        config m_config;
        stats m_stats;
        bvect m_v_saved, m_v_updated;
        svector<double> m_prob_break;
        ptr_vector<expr> m_restore;
        vector<ptr_vector<app>> m_update_stack;
        expr_mark m_on_restore, m_in_update_stack;
        vector<update> m_updates;
        unsigned m_num_updates = 0;

        void reset_updates() { m_num_updates = 0; }

        void add_update(double score, expr* e, bvect const& value) { 
            if (m_num_updates == m_updates.size())
                m_updates.push_back({ e, score, value });
            else {
                auto& u = m_updates[m_num_updates];
                u.e = e;
                u.score = score;
                u.value = value;
            }
            m_num_updates++;
        }
        

        bv_valuation& wval(expr* e) const;

        void insert_update_stack(expr* e);
        bool insert_update(expr* e);        
        void restore_lookahead();
        double lookahead(expr* e, bvect const& new_value);

        void try_set(expr* e, bvect const& new_value);
        void add_updates(expr* e);
        void apply_update(expr* e, bvect const& new_value);
        bool apply_update();
        bool apply_random_update(ptr_vector<expr> const& vars);

        void display_updates(std::ostream& out);

    public:
        bv_lookahead(bv_eval& ev);

        bool on_restore(expr* e) const;

        bool try_repair_down(app* e);

        void collect_statistics(statistics& st) const;

    };
}