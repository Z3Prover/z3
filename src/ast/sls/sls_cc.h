/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    cc_sls.h

Abstract:

    Congruence Closure for SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-06-24
    
--*/
#pragma once

#include "util/hashtable.h"
#include "ast/sls/sls_context.h"

namespace sls {
    
    class cc_plugin : public plugin {
        obj_map<func_decl, ptr_vector<app>> m_app;
        struct value_hash {
            cc_plugin& cc;
            value_hash(cc_plugin& cc) : cc(cc) {}
            unsigned operator()(app* t) const;
        };
        struct value_eq {
            cc_plugin& cc;
            value_eq(cc_plugin& cc) : cc(cc) {}
            bool operator()(app* a, app* b) const;
        };
        hashtable<app*, value_hash, value_eq> m_values;
    public:
        cc_plugin(context& c);
        ~cc_plugin() override;
        family_id fid() { return m_fid; }
        expr_ref get_value(expr* e) override;
        void initialize() override {}
        void propagate_literal(sat::literal lit) override {}       
        bool propagate() override;
        bool is_sat() override;
        void register_term(expr* e) override;
        std::ostream& display(std::ostream& out) const override;
        void mk_model(model& mdl) override;
        void set_value(expr* e, expr* v) override {}
        void repair_up(app* e) override {}
        void repair_down(app* e) override {}
    };
    
}