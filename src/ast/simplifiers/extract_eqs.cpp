/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    extract_eqs.cpp

Abstract:

    simplifier for solving equations

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/


#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/simplifiers/extract_eqs.h"
#include "params/tactic_params.hpp"


namespace euf {

    class basic_extract_eq : public extract_eq {
        ast_manager& m;
        bool m_ite_solver = true;
        bool m_allow_bool = true;

    public:
        basic_extract_eq(ast_manager& m) : m(m) {}

        virtual void set_allow_booleans(bool f) {
            m_allow_bool = f;
        }

        void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) override {
            auto [f, d] = e();
            expr* x, * y;
            if (m.is_eq(f, x, y)) {
                if (x == y)
                    return;
                if (!m_allow_bool && m.is_bool(x))
                    return;
                if (is_uninterp_const(x))
                    eqs.push_back(dependent_eq(e.fml(), to_app(x), expr_ref(y, m), d));
                if (is_uninterp_const(y))
                    eqs.push_back(dependent_eq(e.fml(), to_app(y), expr_ref(x, m), d));
            }
            expr* c, * th, * el, * x1, * y1, * x2, * y2;
            if (m_ite_solver && m.is_ite(f, c, th, el)) {
                if (m.is_eq(th, x1, y1) && m.is_eq(el, x2, y2)) {
                    if (!m_allow_bool && m.is_bool(x1))
                        return;
                    if (x1 == y2 && is_uninterp_const(x1))
                        std::swap(x2, y2);
                    if (x2 == y2 && is_uninterp_const(x2))
                        std::swap(x2, y2), std::swap(x1, y1);
                    if (x2 == y1 && is_uninterp_const(x2))
                        std::swap(x1, y1);
                    if (x1 == x2 && is_uninterp_const(x1)) 
                        eqs.push_back(dependent_eq(e.fml(), to_app(x1), expr_ref(m.mk_ite(c, y1, y2), m), d));
                }
            }
            if (!m_allow_bool)
                return;
            if (is_uninterp_const(f))
                eqs.push_back(dependent_eq(e.fml(), to_app(f), expr_ref(m.mk_true(), m), d));
            if (m.is_not(f, x) && is_uninterp_const(x))
                eqs.push_back(dependent_eq(e.fml(), to_app(x), expr_ref(m.mk_false(), m), d));
        }

        void updt_params(params_ref const& p) {
            tactic_params tp(p);
            m_ite_solver = p.get_bool("ite_solver", tp.solve_eqs_ite_solver());
        }
    };

    class arith_extract_eq : public extract_eq {
        ast_manager&       m;
        arith_util         a;
        expr_ref_vector    m_args;
        expr_sparse_mark   m_nonzero;
        bool               m_enabled = true;


        // solve u mod r1 = y -> u = r1*mod!1 + y
        void solve_mod(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            expr* u, * z;
            rational r1, r2;
            if (!a.is_mod(x, u, z))
                return;
            if (!a.is_numeral(z, r1))
                return;
            if (r1 <= 0)
                return;
            expr_ref term(m);
            term = a.mk_add(a.mk_mul(z, m.mk_fresh_const("mod", a.mk_int())), y);

            if (is_uninterp_const(u))
                eqs.push_back(dependent_eq(orig, to_app(u), term, d));
            else
                solve_eq(orig, u, term, d, eqs);
        }

        /***
        * Solve
        *    x + Y = Z    -> x = Z - Y
        *    -1*x + Y = Z -> x = Y - Z
        *    a*x + Y = Z  -> x = (Z - Y)/a for is-real(x)        
        */
        void solve_add(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            if (!a.is_add(x))
                return;
            expr* u, * z;
            rational r;
            expr_ref term(m);
            unsigned i = 0;
            auto mk_term = [&](unsigned i) {
                term = y;
                unsigned j = 0;
                for (expr* arg2 : *to_app(x)) {
                    if (i != j)
                        term = a.mk_sub(term, arg2);
                    ++j;
                }
            };
            for (expr* arg : *to_app(x)) {
                if (is_uninterp_const(arg)) {
                    mk_term(i);
                    eqs.push_back(dependent_eq(orig, to_app(arg), term, d));
                }
                else if (a.is_mul(arg, u, z) && a.is_numeral(u, r) && is_uninterp_const(z)) {
                    if (r == -1) {
                        mk_term(i);
                        term = a.mk_uminus(term);
                        eqs.push_back(dependent_eq(orig, to_app(z), term, d));
                    }
                    else if (a.is_real(arg) && r != 0) {
                        mk_term(i);
                        term = a.mk_div(term, u);
                        eqs.push_back(dependent_eq(orig, to_app(z), term, d));
                    }
                }
                else if (a.is_real(arg) && a.is_mul(arg)) {
                    unsigned j = 0;
                    for (expr* xarg : *to_app(arg)) {
                        ++j;
                        if (!is_uninterp_const(xarg))
                            continue;
                        unsigned k = 0;
                        bool nonzero = true;
                        for (expr* yarg : *to_app(arg)) {
                            ++k;
                            nonzero = k == j || m_nonzero.is_marked(yarg) || (a.is_numeral(yarg, r) && r != 0);                           
                            if (!nonzero)
                                break;
                        }
                        if (!nonzero)
                            continue;

                        k = 0;
                        ptr_buffer<expr> args;
                        for (expr* yarg : *to_app(arg)) {
                            ++k;
                            if (k != j)
                                args.push_back(yarg);
                        }
                        mk_term(i);
                        term = a.mk_div(term, a.mk_mul(args.size(), args.data()));
                        eqs.push_back(dependent_eq(orig, to_app(xarg), term, d));
                    }
                }
                ++i;
            }
        }

        /***
        * Solve for x * Y = Z, where Y != 0 -> x = Z / Y
        */
        void solve_mul(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            if (!a.is_mul(x))
                return;
            rational r;
            expr_ref term(m);
            unsigned i = 0;
            for (expr* arg : *to_app(x)) {
                ++i;
                if (!is_uninterp_const(arg))
                    continue;
                if (!a.is_real(arg))
                    continue;
                unsigned j = 0;
                bool nonzero = true;
                for (expr* arg2 : *to_app(x)) {
                    ++j;
                    nonzero = j == i || m_nonzero.is_marked(arg2) || (a.is_numeral(arg2, r) && r != 0);
                    if (!nonzero)
                        break;
                }
                if (!nonzero)
                    continue;
                ptr_buffer<expr> args;
                j = 0;
                for (expr* arg2 : *to_app(x)) {
                    ++j;
                    if (j != i)
                        args.push_back(arg2);
                }
                term = a.mk_div(y, a.mk_mul(args));
                eqs.push_back(dependent_eq(orig, to_app(arg), term, d));
            }
        }

        void add_pos(expr* f) {
            expr* lhs = nullptr, * rhs = nullptr;
            rational val;
            if (a.is_le(f, lhs, rhs) && a.is_numeral(rhs, val) && val.is_neg()) 
                m_nonzero.mark(lhs);            
            else if (a.is_ge(f, lhs, rhs) && a.is_numeral(rhs, val) && val.is_pos())
                m_nonzero.mark(lhs);            
            else if (m.is_not(f, f)) {
                if (a.is_le(f, lhs, rhs) && a.is_numeral(rhs, val) && !val.is_neg())
                    m_nonzero.mark(lhs);
                else if (a.is_ge(f, lhs, rhs) && a.is_numeral(rhs, val) && !val.is_pos())
                    m_nonzero.mark(lhs);
                else if (m.is_eq(f, lhs, rhs) && a.is_numeral(rhs, val) && val.is_zero())
                    m_nonzero.mark(lhs);
            }
        }

        void solve_eq(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            solve_add(orig, x, y, d, eqs);
            solve_mod(orig, x, y, d, eqs);
            solve_mul(orig, x, y, d, eqs);
        }

    public:

        arith_extract_eq(ast_manager& m) : m(m), a(m), m_args(m) {}

        void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) override {
            if (!m_enabled)
                return;
            auto [f, d] = e();
            expr* x, * y;
            if (m.is_eq(f, x, y) && a.is_int_real(x)) {
                solve_eq(f, x, y, d, eqs);
                solve_eq(f, y, x, d, eqs);
            }
        }

        void pre_process(dependent_expr_state& fmls) override {
            if (!m_enabled)
                return;
            m_nonzero.reset();
            for (unsigned i = 0; i < fmls.size(); ++i) 
                add_pos(fmls[i].fml());            
        }


        void updt_params(params_ref const& p) {
            tactic_params tp(p);
            m_enabled = p.get_bool("theory_solver", tp.solve_eqs_ite_solver());
        }
    };

    void register_extract_eqs(ast_manager& m, scoped_ptr_vector<extract_eq>& ex) {
        ex.push_back(alloc(arith_extract_eq, m));
        ex.push_back(alloc(basic_extract_eq, m));
    }
}
