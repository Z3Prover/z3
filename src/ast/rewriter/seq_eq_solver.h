/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_eq_solver

Abstract:

    Solver-agnostic equality solving routines for sequences
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-03-01

--*/
#pragma once

#include "ast/rewriter/seq_axioms.h"

namespace seq {

    struct eq {
        expr_ref_vector ls;
        expr_ref_vector rs;
        eq(expr_ref_vector& l, expr_ref_vector& r):
            ls(l), rs(r) {}
    };

    typedef scoped_ptr<eq> eq_ptr;
        
    class eq_solver {
        ast_manager& m;
        axioms&      m_ax;
        seq_util     seq;
        expr_ref_vector                        m_clause;
        std::function<expr*(expr*)>            m_value;
        std::function<bool(expr*, rational&)>  m_int_value;
        std::function<void(bool, expr_ref_vector const&)>  m_add_consequence;

        bool match_itos1(eq const& e, expr*& s, expr*& t);
        bool solve_itos1(eq const& e, eq_ptr& r);

        bool match_itos2(eq const& e, expr*& s);
        bool solve_itos2(eq const& e, eq_ptr& r);

        void add_consequence(expr_ref const& a);
        void add_consequence(expr_ref const& a, expr_ref const& b);

        expr_ref mk_eq(expr* a, expr* b) { return expr_ref(m.mk_eq(a, b), m); }
        expr_ref mk_ge(expr* x, int n) { return m_ax.mk_ge(x, n); }
        expr_ref mk_le(expr* x, int n) { return m_ax.mk_le(x, n); }
        expr_ref mk_ge(expr* x, rational const& n) { return m_ax.mk_ge(x, n); }
        expr_ref mk_le(expr* x, rational const& n) { return m_ax.mk_le(x, n); }

    public:
        
        eq_solver(ast_manager& m, axioms& ax):
            m(m),
            m_ax(ax),
            seq(m),
            m_clause(m)
        {}

        void set_value(std::function<expr*(expr*)>& v) { m_value = v; }
        void set_int_value(std::function<bool(expr*,rational&)>& iv) { m_int_value = iv; }
        void set_add_consequence(std::function<void(bool, expr_ref_vector const&)>& ac) { m_add_consequence = ac; }

        bool solve(eq const& e, eq_ptr& r);

        
    };

};

