/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_bv_plugin.h

Abstract:

    Theory plugin for bit-vector local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/bv_decl_plugin.h"
#include "ast/sls/sls_bv_terms.h"
#include "ast/sls/sls_bv_eval.h"

namespace sls {

    class bv_plugin : public plugin {
        bv_util             bv;
        bv_terms       m_terms;
        bv_eval        m_eval;
        bv::sls_stats       m_stats;
        bool                m_initialized = false;

        std::ostream& trace_repair(bool down, expr* e);
        void trace();
        bool is_bv_predicate(expr* e);

        void log(expr* e, bool up_down, bool success); 

    public:
        bv_plugin(context& ctx);
        ~bv_plugin() override {}
        void register_term(expr* e) override;
        expr_ref get_value(expr* e) override;
        void start_propagation() override;
        void initialize() override;
        void propagate_literal(sat::literal lit) override;
        bool propagate() override;
        bool repair_down(app* e) override;
        void repair_up(app* e) override;
        void repair_literal(sat::literal lit) override;
        bool is_sat() override;

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override;
        bool set_value(expr* e, expr* v) override;
        void collect_statistics(statistics& st) const override;
        void reset_statistics() override {}
    };

}
