/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_array_plugin.h

Abstract:

    Theory plugin for arrays local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/array_decl_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace sls {


    class array_plugin : public plugin {
        array_util     a;

        typedef obj_map<euf::enode, obj_map<euf::enode, euf::enode*>> kv;
        void init_egraph(euf::egraph& g);
        void init_kv(euf::egraph& g, kv& kv);
        void saturate_store(euf::egraph& g, kv& kv);
        
    public:
        array_plugin(context& ctx);
        ~array_plugin() override {}
        void register_term(expr* e) override { }
        expr_ref get_value(expr* e) override { return expr_ref(m); }
        void initialize() override {}
        void propagate_literal(sat::literal lit) override {}
        bool propagate() override { return false; }
        bool repair_down(app* e) override { return false; }
        void repair_up(app* e) override {}
        void repair_literal(sat::literal lit) override {}
        bool is_sat() override;

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override { return out; }
        void mk_model(model& mdl) override {}
        bool set_value(expr* e, expr* v) override { return false; }
        void collect_statistics(statistics& st) const override {}
        void reset_statistics() override {}
    };

}
