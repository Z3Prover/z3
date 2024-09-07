/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_model_value_plugin.h

Abstract:

    Theory plugin for model values
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/
#pragma once

#include "ast/sls/sls_context.h"

namespace sls {

    class model_value_plugin : public plugin {
        
    public:
        model_value_plugin(context& ctx) : plugin(ctx) { m_fid = m.get_family_id("model-value"); }
        ~model_value_plugin() override {}
        void register_term(expr* e) override { }
        expr_ref get_value(expr* e) override { return expr_ref(e, m); }
        void initialize() override { }
        void propagate_literal(sat::literal lit) override {  }
        bool propagate() override { return false; }
        bool repair_down(app* e) override { return true; }
        void repair_up(app* e) override {}
        void repair_literal(sat::literal lit) override {  }
        bool is_sat() override { return true; }

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override { return out;}
        void mk_model(model& mdl) override {}
        bool set_value(expr* e, expr* v) override { return false; }
        void collect_statistics(statistics& st) const override {}
        void reset_statistics() override {}
    };

}
