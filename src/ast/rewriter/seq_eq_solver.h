/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_eq_solver

Abstract:

    Solver core-agnostic equality inference routines for sequences
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-03-01

--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_axioms.h"

namespace seq {

    struct eq {
        expr_ref_vector ls;
        expr_ref_vector rs;
        eq(expr_ref_vector& l, expr_ref_vector& r):
            ls(l), rs(r) {}
    };

    struct eqr {
        expr_ref_vector const& ls;
        expr_ref_vector const& rs;
        eqr(expr_ref_vector const& l, expr_ref_vector const& r):
            ls(l), rs(r) {}
    };

    typedef scoped_ptr<eq> eq_ptr;

    class eq_solver_context {
    public:
        virtual void  add_consequence(bool uses_dep, expr_ref_vector const& clause) = 0;
        virtual void  add_solution(expr* var, expr* term) = 0;
        virtual expr* expr2rep(expr* e) = 0;
        virtual bool  get_length(expr* e, rational& r) = 0;
    };
        
    class eq_solver {
        ast_manager&       m;
        eq_solver_context& ctx;
        axioms&            m_ax;
        arith_util         a;
        seq_util           seq;
        expr_ref_vector    m_clause;

        bool reduce_unit(eqr const& e, eq_ptr& r);

        bool match_itos1(eqr const& e, expr*& s, expr*& t);
        bool reduce_itos1(eqr const& e, eq_ptr& r);

        bool match_itos2(eqr const& e, expr*& s);
        bool reduce_itos2(eqr const& e, eq_ptr& r);

        bool reduce_itos3(eqr const& e, eq_ptr& r);
        bool match_itos3(eqr const& e, expr*& n, expr_ref_vector const* & es);

        bool match_ubv2s1(eqr const& e, expr*& s, expr*& t);
        bool reduce_ubv2s1(eqr const& e, eq_ptr& r);

        bool match_ubv2s2(eqr const& e, expr*& n, expr_ref_vector const*& es);
        bool reduce_ubv2s2(eqr const& e, eq_ptr& r);

        bool match_binary_eq(eqr const& e, expr_ref& x, ptr_vector<expr>& xs, ptr_vector<expr>& ys, expr_ref& y);
        bool reduce_binary_eq(eqr const& e, eq_ptr& r);

        bool reduce_nth_solved(eqr const& e, eq_ptr& r);
        bool match_nth_solved(eqr const& e, expr_ref& x, expr_ref& y);
        bool match_nth_solved_aux(expr_ref_vector const& ls, expr_ref_vector const& rs, expr_ref& x, expr_ref& y);

        bool match_ternary_eq_r(expr_ref_vector const& ls, expr_ref_vector const& rs,
                                expr_ref& x, expr_ref_vector& xs, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2);

        bool match_ternary_eq_l(expr_ref_vector const& ls, expr_ref_vector const& rs,
                                expr_ref_vector& xs, expr_ref& x, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2);


        bool branch_unit_variable(eqr const& e);


        /**
         * count unit or non-unit entries left-to-right or right-to-left starting at, and including offset.
         */
        unsigned count_units_l2r(expr_ref_vector const& es, unsigned offset) const;
        unsigned count_units_r2l(expr_ref_vector const& es, unsigned offset) const;
        unsigned count_non_units_l2r(expr_ref_vector const& es, unsigned offset) const;
        unsigned count_non_units_r2l(expr_ref_vector const& es, unsigned offset) const;

        void set_prefix(expr_ref& x, expr_ref_vector const& xs, unsigned sz) const;
        void set_suffix(expr_ref& x, expr_ref_vector const& xs, unsigned sz) const;

        template<typename V>
        void set_prefix(V& dst, expr_ref_vector const& xs, unsigned sz) const { set_extract(dst, xs, 0, sz); }

        template<typename V>
        void set_suffix(V& dst, expr_ref_vector const& xs, unsigned sz) const { set_extract(dst, xs, xs.size() - sz, sz); }

        template<typename V> 
        void set_extract(V& dst, expr_ref_vector const& xs, unsigned offset, unsigned sz) const {
            SASSERT(offset + sz <= xs.size());
            dst.reset();
            dst.append(sz, xs.data() + offset);
        }

        void set_conflict();
        void add_consequence(expr_ref const& a);
        void add_consequence(expr_ref const& a, expr_ref const& b);

        expr_ref mk_eq(expr* a, expr* b) { return expr_ref(m.mk_eq(a, b), m); }
        expr_ref mk_ge(expr* x, int n) { return m_ax.mk_ge(x, n); }
        expr_ref mk_le(expr* x, int n) { return m_ax.mk_le(x, n); }
        expr_ref mk_ge(expr* x, rational const& n) { return m_ax.mk_ge(x, n); }
        expr_ref mk_le(expr* x, rational const& n) { return m_ax.mk_le(x, n); }

        ptr_vector<expr> m_todo;
        bool occurs(expr* a, expr_ref_vector const& b);
        bool occurs(expr* a, expr* b);

        bool all_units(expr_ref_vector const& es, unsigned start, unsigned end) const;

    public:
        
        eq_solver(ast_manager& m, eq_solver_context& ctx, axioms& ax):
            m(m),
            ctx(ctx),
            m_ax(ax),
            a(m),
            seq(m),
            m_clause(m)
        {}

        bool reduce(eqr const& e, eq_ptr& r);

        bool reduce(expr* s, expr* t, eq_ptr& r);

        bool branch(unsigned priority, eqr const& e);

        bool is_var(expr* a) const;

        bool match_binary_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, 
                             expr_ref& x, ptr_vector<expr>& xs, ptr_vector<expr>& ys, expr_ref& y);

        bool match_ternary_eq_rhs(expr_ref_vector const& ls, expr_ref_vector const& rs,
                                  expr_ref& x, expr_ref_vector& xs, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2);

        bool match_ternary_eq_lhs(expr_ref_vector const& ls, expr_ref_vector const& rs,
                                  expr_ref_vector& xs, expr_ref& x, expr_ref& y1, expr_ref_vector& ys, expr_ref& y2);

        bool match_quat_eq(expr_ref_vector const& ls, expr_ref_vector const& rs,
                           expr_ref& x1, expr_ref_vector& xs, expr_ref& x2,
                           expr_ref& y1, expr_ref_vector& ys, expr_ref& y2);

        bool can_align_from_lhs_aux(expr_ref_vector const& ls, expr_ref_vector const& rs);
        bool can_align_from_rhs_aux(expr_ref_vector const& ls, expr_ref_vector const& rs);

        bool branch_unit_variable(expr* X, expr_ref_vector const& units);
        
    };

};

