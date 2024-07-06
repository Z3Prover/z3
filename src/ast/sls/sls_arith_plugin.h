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

#include "ast/sls/sls_smt.h"
#include "ast/sls/sls_arith_base.h"

namespace sls {

    class arith_plugin : public plugin {
        scoped_ptr<arith_base<checked_int64<true>>> m_arith64;
        scoped_ptr<arith_base<rational>> m_arith;
    public:
        arith_plugin(context& ctx) : plugin(ctx) { m_arith64 = alloc(arith_base<checked_int64<true>>,ctx); }
        ~arith_plugin() override {}
        void init_bool_var(sat::bool_var v) override;
        void register_term(expr* e) override;
        expr_ref get_value(expr* e) override;
        lbool check() override;
        bool is_sat() override;
        void reset() override;

        void on_rescale() override;
        void on_restart() override;
        std::ostream& display(std::ostream& out) const override;
        void mk_model(model& mdl) override;
    };

}
