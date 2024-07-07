/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_bv.h

Abstract:

    Theory plugin for bit-vector local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/
#pragma once

#include "ast/sls/sls_smt.h"
#include "ast/bv_decl_plugin.h"
#include "ast/sls/bv_sls_terms.h"
#include "ast/sls/bv_sls_eval.h"

namespace sls {

    class bv_plugin : public plugin {
        bv_util             bv;
        bv::sls_terms       m_terms;
        bv::sls_eval        m_eval;
        bv::sls_stats       m_stats;

        indexed_uint_set    m_repair_up, m_repair_roots;
        unsigned            m_repair_down = UINT_MAX;

        std::pair<bool, app*> next_to_repair();
        void init_repair_goal(app* e);
    public:
        bv_plugin(context& ctx);
        ~bv_plugin() override {}
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
        void set_shared(expr* e) override;
        void set_value(expr* e, expr* v) override;
    };

}
