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
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

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
            ptr_vector<expr> lhs, rhs;
        };

        enum edit_distance_strategy {
            EDIT_CHAR = 0,
            EDIT_SUBSTR = 1,
            EDIT_COMBINED = 2,
        };

        seq_util seq;
        arith_util a;
        seq_rewriter rw;
        th_rewriter thrw;
        scoped_ptr_vector<eval> m_values;
        indexed_uint_set m_chars; // set of characters in the problem
        bool m_initialized = false;
        edit_distance_strategy m_str_update_strategy;

        struct str_update {
            expr* e;
            zstring value;
            double m_score;
        };
        struct int_update {
            expr* e;
            rational value;
            double m_score;
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
        bool repair_down_str_eq_unify(app* e);
        bool repair_down_str_eq_edit_distance(app* e);
        bool repair_down_str_eq_edit_distance_incremental(app* e);
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
        bool repair_down_str_itos(app* e);
        bool repair_down_str_stoi(app* e);
        bool repair_down_in_re(app* e);

        void repair_up_str_length(app* e);
        void repair_up_str_indexof(app* e);
        void repair_up_str_itos(app* e);
        void repair_up_str_stoi(app* e);

        enum op_t {
            add, del, copy
        };
        enum side_t {
            left, right
        };
        struct string_update {
            side_t side;
            op_t op;
            unsigned i, j;
        };
        struct string_instance {
            zstring s;
            bool_vector is_value;
            bool_vector prev_is_var;
            bool_vector next_is_var;

            bool can_add(unsigned i) const {
                return !is_value[i] || prev_is_var[i];
            }
        };
        svector<string_update> m_string_updates;
        void add_string_update(side_t side, op_t op, unsigned i, unsigned j) { m_string_updates.push_back({ side, op, i, j }); }
        void init_string_instance(ptr_vector<expr> const& es, string_instance& a);
        unsigned edit_distance_with_updates(string_instance const& a, string_instance const& b);
        unsigned edit_distance(zstring const& a, zstring const& b);
        void add_edit_updates(ptr_vector<expr> const& w, zstring const& val, zstring const& val_other, uint_set const& chars, unsigned diff);
        void add_char_edit_updates(ptr_vector<expr> const& w, zstring const& val, zstring const& val_other, uint_set const& chars);
        void add_substr_edit_updates(ptr_vector<expr> const& w, zstring const& val, zstring const& val_other, uint_set const& chars);

        int add_str_update(expr* e, zstring const& currVal, zstring const& val, double score);
        zstring trunc_pad_to_fit(unsigned min_length, unsigned max_length, zstring const& s) const;
        zstring trunc_pad_to_fit(unsigned length, zstring const& s) const {
            return trunc_pad_to_fit(length, length, s);
        }

        // regex functionality
        
        // enumerate set of strings that can match a prefix of regex r.
        struct lookahead {
            zstring s;
            unsigned min_depth;
        };
        void choose(expr* r, unsigned k, zstring& prefix, vector<lookahead>& result);

        // enumerate set of possible next chars, including possibly sampling from m_chars for whild-cards.
        void next_char(expr* r, unsigned_vector& chars);

        bool is_in_re(zstring const& s, expr* r);

        bool is_num_string(zstring const& s); // Checks if s \in [0-9]+ (i.e., str.to_int is not -1)

        unsigned random_char() const;

        // access evaluation
        bool is_seq_predicate(expr* e);

        eval& get_eval(expr* e);
        eval* get_eval(expr* e) const;
        ptr_vector<expr> const& lhs(expr* eq);
        ptr_vector<expr> const& rhs(expr* eq);
        ptr_vector<expr> const& concats(expr* eq);

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
