/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_user_sort_plugin.h

Abstract:

    Theory plugin for arrays local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/euf/euf_egraph.h"

namespace sls {

    class user_sort_plugin : public plugin {
        scoped_ptr<euf::egraph> m_g;
        scoped_ptr<obj_map<sort, unsigned>> m_num_elems;
        scoped_ptr<obj_map<euf::enode, expr*>> m_root2value;
        scoped_ptr<expr_ref_vector> m_pinned;

        void init_egraph(euf::egraph& g);
        bool is_user_sort(sort* s) { return s->get_family_id() == user_sort_family_id; }
        
    public:
        user_sort_plugin(context& ctx);
        ~user_sort_plugin() override {}
        void register_term(expr* e) override { }
        expr_ref get_value(expr* e) override;
        void initialize() override { m_g = nullptr; }
        void propagate_literal(sat::literal lit) override { m_g = nullptr; }
        bool propagate() override { return false; }
        bool repair_down(app* e) override { return true; }
        void repair_up(app* e) override {}
        void repair_literal(sat::literal lit) override { m_g = nullptr; }
        bool is_sat() override { return true; }

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override;
        void mk_model(model& mdl) override {}
        bool set_value(expr* e, expr* v) override { return false; }
        void collect_statistics(statistics& st) const override {}
        void reset_statistics() override {}
    };

}
