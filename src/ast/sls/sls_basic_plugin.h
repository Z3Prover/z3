/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_basic_plugin.h

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-05

--*/
#pragma once

#include "ast/sls/sls_context.h"

namespace sls {

    class basic_plugin : public plugin {
        bool_vector        m_values;
        bool               m_initialized = false;

        bool bval1(app* e) const;
        bool bval0(expr* e) const;
        bool try_repair(app* e, unsigned i);
        bool try_repair_and_or(app* e, unsigned i);
        bool try_repair_not(app* e);
        bool try_repair_eq(app* e, unsigned i);
        bool try_repair_xor(app* e, unsigned i);
        bool try_repair_ite(app* e, unsigned i);
        bool try_repair_implies(app* e, unsigned i);
        bool try_repair_distinct(app* e, unsigned i);
        bool set_value(expr* e, bool b);

    public:
        basic_plugin(context& ctx) : 
            plugin(ctx) { 
            m_fid = basic_family_id;
        }
        ~basic_plugin() override {}
        void register_term(expr* e) override;
        expr_ref get_value(expr* e) override;
        void initialize() override;
        void propagate_literal(sat::literal lit) override;
        bool propagate() override { return false; }
        void repair_down(app* e) override;
        void repair_up(app* e) override;
        bool is_sat() override;

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override;
        void mk_model(model& mdl) override {}
        void set_value(expr* e, expr* v) override;
    };

}
