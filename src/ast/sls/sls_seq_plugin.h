/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_seq_plugin.h

Abstract:

    Sequence/String SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-11-22
    
--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/seq_decl_plugin.h"


namespace sls {
    
    class seq_plugin : public plugin {
        struct value {
            value(ast_manager& m): evalue(m) {}
            zstring  svalue;
            expr_ref evalue;
        };

        struct eval {
            eval(ast_manager& m):
                val0(m), val1(m) {}
            value val0;
            value val1;
        };

        seq_util seq;
        scoped_ptr_vector<eval> m_values;

        struct str_update {
            expr* e;
            zstring value;
            unsigned m_score;
        };
        vector<str_update> m_str_updates;
        bool apply_str_update();
        bool update(expr* e, zstring const& value);
        
        bool bval1(expr* e);
        bool bval1_seq(app* e);
        zstring& strval0(expr* e);
        zstring const& strval1(expr* e);
        
        bool repair_contains(expr* e);
    
    public:
        seq_plugin(context& c);
        ~seq_plugin() override {}
        expr_ref get_value(expr* e) override;
        void initialize() override {}
        void start_propagation() override {}
        void propagate_literal(sat::literal lit) override;
        bool propagate() override;
        bool is_sat() override;
        void register_term(expr* e) override;
        std::ostream& display(std::ostream& out) const override;
        bool set_value(expr* e, expr* v) override;
        bool include_func_interp(func_decl* f) const override { return true; }

        void repair_up(app* e) override;
        bool repair_down(app* e) override;
        void repair_literal(sat::literal lit) override;

        void collect_statistics(statistics& st) const override {}
        void reset_statistics() override {}

    };
    
}
