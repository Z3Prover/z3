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
#include "ast/sls/bv_sls_terms.h"
#include "ast/sls/bv_sls_eval.h"

namespace sls {

    class bv_plugin : public plugin {
        bv_util             bv;
        bv::sls_terms       m_terms;
        bv::sls_eval        m_eval;
        bv::sls_stats       m_stats;
        bool                m_initialized = false;

        void init_bool_var_assignment(sat::bool_var v);
        std::ostream& trace_repair(bool down, expr* e);
        void trace();
        bool can_propagate();

    public:
        bv_plugin(context& ctx);
        ~bv_plugin() override {}
        void register_term(expr* e) override;
        expr_ref get_value(expr* e) override;
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
        void mk_model(model& mdl) override {}
        void set_value(expr* e, expr* v) override;
    };

}
