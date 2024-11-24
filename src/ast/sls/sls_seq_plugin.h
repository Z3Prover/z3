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
#include "ast/arith_decl_plugin.h"


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
            bool is_value = false;
            unsigned min_length = 0;
            unsigned max_length = UINT_MAX;
        };

        seq_util seq;
        arith_util a;
        scoped_ptr_vector<eval> m_values;
        indexed_uint_set m_chars;
        bool m_initialized = false;

        struct str_update {
            expr* e;
            zstring value;
            unsigned m_score;
        };
        struct int_update {
            expr* e;
            rational value;
            unsigned m_score;
        };
        vector<str_update> m_str_updates;
        vector<int_update> m_int_updates;
        bool apply_update();
        bool update(expr* e, zstring const& value);
        bool update(expr* e, rational const& value);
        
        bool bval1(expr* e);
        bool bval1_seq(app* e);
        zstring& strval0(expr* e);
        zstring const& strval1(expr* e);
        
        bool repair_down_seq(app* e);
        bool repair_down_eq(app* e);
        bool repair_down_str_eq(app* e);
        bool repair_down_str_extract(app* e);
        bool repair_down_str_contains(expr* e);
        bool repair_down_str_concat(app* e);
        bool repair_down_str_length(app* e);
        bool repair_down_str_at(app* e);
        bool repair_down_str_indexof(app* e);
        bool repair_down_str_replace(app* e);
        bool repair_down_str_prefixof(app* e);
        bool repair_down_str_suffixof(app* e);

        void repair_up_str_length(app* e);
        void repair_up_str_indexof(app* e);


        bool is_seq_predicate(expr* e);

        eval& get_eval(expr* e);
        eval* get_eval(expr* e) const;

        bool is_value(expr* e);
    public:
        seq_plugin(context& c);
        ~seq_plugin() override {}
        expr_ref get_value(expr* e) override;
        void initialize() override;
        void start_propagation() override {}
        void propagate_literal(sat::literal lit) override;
        bool propagate() override;
        bool is_sat() override;
        void register_term(expr* e) override;
        std::ostream& display(std::ostream& out) const override;
        bool set_value(expr* e, expr* v) override;
        bool include_func_interp(func_decl* f) const override { return false; }

        void repair_up(app* e) override;
        bool repair_down(app* e) override;
        void repair_literal(sat::literal lit) override;

        void collect_statistics(statistics& st) const override {}
        void reset_statistics() override {}

    };
    
}
