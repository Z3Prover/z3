/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_arith_plugin.h

Abstract:

    Theory plugin for arithmetic local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-05

--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/sls/sls_arith_base.h"

namespace sls {

    class arith_plugin : public plugin {
        scoped_ptr<arith_base<checked_int64<true>>> m_arith64;
        scoped_ptr<arith_base<rational>> m_arith;
        expr_ref_vector m_shared;

        void init_backup();
    public:
        arith_plugin(context& ctx);
        ~arith_plugin() override {}
        void register_term(expr* e) override;
        expr_ref get_value(expr* e) override;
        void start_propagation() override;
        bool is_fixed(expr* e, expr_ref& value) override;
        void initialize() override;
        void propagate_literal(sat::literal lit) override;
        bool propagate() override;
        bool repair_down(app* e) override;
        void repair_up(app* e) override;
        void repair_literal(sat::literal lit) override;
        bool is_sat() override;

        void on_rescale() override;
        void on_restart() override;
        std::ostream& display(std::ostream& out) const override;
        bool set_value(expr* e, expr* v) override;

        void collect_statistics(statistics& st) const override;
        void reset_statistics() override;
    };

}
