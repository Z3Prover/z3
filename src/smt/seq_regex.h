/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_regex.h

Abstract:

    Solver for regexes 

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-22

--*/
#pragma once

#include "util/scoped_vector.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "smt/smt_context.h"
#include "smt/seq_skolem.h"

namespace smt {

    class theory_seq;

    class seq_regex {
        struct s_in_re {
            literal m_lit;
            expr*   m_s;
            expr*   m_re;
            bool    m_active;
        s_in_re(literal l, expr* s, expr* r):
            m_lit(l), m_s(s), m_re(r), m_active(true) {}
        };

        struct propagation_lit {
            literal m_lit;
            literal m_trigger;
            propagation_lit(literal lit, literal t): m_lit(lit), m_trigger(t) {}
            propagation_lit(literal lit): m_lit(lit), m_trigger(null_literal) {}
            propagation_lit(): m_lit(null_literal), m_trigger(null_literal) {}
        };

        theory_seq&      th;
        context&         ctx;
        ast_manager&     m;
        vector<s_in_re> m_s_in_re;
        scoped_vector<propagation_lit> m_to_propagate;

        seq_util& u();
        class seq_util::re& re();
        class seq_util::str& str();
        seq_rewriter& seq_rw();
        seq_skolem& sk();
        arith_util& a();

        bool is_string_equality(literal lit);

        void rewrite(expr_ref& e);

        bool coallesce_in_re(literal lit);

        bool propagate(literal lit, literal& trigger);

        bool block_unfolding(literal lit, unsigned i);

        void propagate_nullable(literal lit, expr* s, unsigned idx, expr* r);

        bool propagate_derivative(literal lit, expr* e, expr* s, expr* i, unsigned idx, expr* r, literal& trigger);

        expr_ref mk_first(expr* r, expr* n);

        expr_ref unroll_non_empty(expr* r, expr_mark& seen, unsigned depth);

        bool is_member(expr* r, expr* u);

        expr_ref symmetric_diff(expr* r1, expr* r2);

        expr_ref derivative_wrapper(expr* hd, expr* r);

        void get_cofactors(expr* r, expr_ref_vector& conds, expr_ref_pair_vector& result);

        void get_cofactors(expr* r, expr_ref_pair_vector& result) {
            expr_ref_vector conds(m);
            get_cofactors(r, conds, result);
        }

    public:

        seq_regex(theory_seq& th);

        void push_scope() { m_to_propagate.push_scope(); }

        void pop_scope(unsigned num_scopes) { m_to_propagate.pop_scope(num_scopes); }

        bool can_propagate() const;

        bool propagate();

        void propagate_in_re(literal lit);

        // (accept s i r) means 
        // the suffix of s after the first i characters is a member of r
        void propagate_accept(literal lit);

        void propagate_eq(expr* r1, expr* r2);

        void propagate_ne(expr* r1, expr* r2);
        
        void propagate_is_non_empty(literal lit);

        void propagate_is_empty(literal lit);
        
    };

};

