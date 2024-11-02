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
        expr_mark          m_axiomatized;
        
        bool is_basic(expr* e) const;
        bool bval0(expr* e) const;
        bool try_repair(app* e, unsigned i);
        bool try_repair_xor(app* e, unsigned i);
        bool try_repair_ite(app* e, unsigned i);
        bool try_repair_distinct(app* e, unsigned i);
        bool set_value(expr* e, bool b);

        expr_ref eval_ite(app* e);
        expr_ref eval_distinct(app* e);
        expr_ref eval_xor(app* e);

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
        bool propagate() override;
        bool repair_down(app* e) override;
        void repair_up(app* e) override;
        void repair_literal(sat::literal lit) override;
        bool is_sat() override;

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override;
        bool set_value(expr* e, expr* v) override;
        void collect_statistics(statistics& st) const override {}
        void reset_statistics() override {}
    };

}
