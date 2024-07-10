/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_basic_plugin.h

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-05

--*/
#pragma once

#include "ast/sls/sls_smt.h"

namespace sls {

    class basic_plugin : public plugin {
        bool_vector        m_values;
        indexed_uint_set   m_repair_up, m_repair_roots;
        unsigned           m_repair_down = UINT_MAX;
        bool               m_initialized = false;

        void init();
        bool bval1(app* e) const;
        bool bval0(expr* e) const;
        bool repair_up(expr* e);
        bool try_repair(app* e, unsigned i);
        bool try_repair_and_or(app* e, unsigned i);
        bool try_repair_not(app* e);
        bool try_repair_eq(app* e, unsigned i);
        bool try_repair_xor(app* e, unsigned i);
        bool try_repair_ite(app* e, unsigned i);
        bool try_repair_implies(app* e, unsigned i);
        void set_value(expr* e, bool b);

        void repair_down(app* e);
        void repair_defs_and_updates();
        void repair_literal(sat::literal lit);

    public:
        basic_plugin(context& ctx) : 
            plugin(ctx) { 
        }
        ~basic_plugin() override {}
        void init_bool_var(sat::bool_var v) override {}
        void register_term(expr* e) override {}
        expr_ref get_value(expr* e) override;
        lbool check() override;
        bool is_sat() override;

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override;
        void mk_model(model& mdl) override {}
        void set_shared(expr* e) override {}
        void set_value(expr* e, expr* v) override;
    };

}
