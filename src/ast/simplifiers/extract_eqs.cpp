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
#include "ast/bv_decl_plugin.h"
#include "ast/simplifiers/extract_eqs.h"
#include "ast/simplifiers/bound_manager.h"
#include "params/tactic_params.hpp"


namespace euf {

    class basic_extract_eq : public extract_eq {
        ast_manager& m;
        bool m_ite_solver = true;
        bool m_allow_bool = true;

    public:
        basic_extract_eq(ast_manager& m) : m(m) {}

        void set_allow_booleans(bool f) override {
            m_allow_bool = f;
        }

        void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) override {
            auto [f, p, d] = e();
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

        void updt_params(params_ref const& p) override {
            tactic_params tp(p);
            m_ite_solver = p.get_bool("ite_solver", tp.solve_eqs_ite_solver());
        }
    };

    class bv_extract_eq : public extract_eq {
        ast_manager&       m;
        bv_util            bv;
        bool               m_enabled = true;

        
        void solve_add(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            if (!bv.is_bv_add(x))
                return;
            expr_ref term(m);
            auto mk_term = [&](unsigned i) {
                term = y;
                unsigned j = 0;
                for (expr* arg2 : *to_app(x)) {
                    if (i != j)
                        term = bv.mk_bv_sub(term, arg2);
                    ++j;
                }
            };
            expr* u = nullptr, *z = nullptr;
            rational r;
            unsigned i = 0;
            for (expr* arg : *to_app(x)) {
                if (is_uninterp_const(arg)) {
                    mk_term(i);
                    eqs.push_back(dependent_eq(orig, to_app(arg), term, d));
                }
                else if (bv.is_bv_mul(arg, u, z) && bv.is_numeral(u, r) && is_uninterp_const(z) && r.is_odd()) {
                    mk_term(i);
                    unsigned sz = bv.get_bv_size(z);
                    rational inv_r;
                    VERIFY(r.mult_inverse(sz, inv_r));
                    term = bv.mk_bv_mul(bv.mk_numeral(inv_r, sz), term);
                    eqs.push_back(dependent_eq(orig, to_app(z), term, d));
                }
                ++i;
            }
        }

        void solve_mul(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            expr* u = nullptr, *z = nullptr;
            rational r, inv_r;
            if (bv.is_bv_mul(x, u, z) && bv.is_numeral(u, r) && is_uninterp_const(z) && r.is_odd()) {
                unsigned sz = bv.get_bv_size(z);
                VERIFY(r.mult_inverse(sz, inv_r));
                auto term = expr_ref(bv.mk_bv_mul(bv.mk_numeral(inv_r, sz), y), m);
                eqs.push_back(dependent_eq(orig, to_app(z), term, d));                
            }
        }

        void solve_eq(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            solve_add(orig, x, y, d, eqs);
            solve_mul(orig, x, y, d, eqs);
        }

        
    public:
        bv_extract_eq(ast_manager& m) : m(m), bv(m) {}

        void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) override {
            if (!m_enabled)
                return;
            auto [f, p, d] = e();
            expr* x, * y;
            if (m.is_eq(f, x, y) && bv.is_bv(x)) {
                solve_eq(f, x, y, d, eqs);
                solve_eq(f, y, x, d, eqs);
            }

        }

        void pre_process(dependent_expr_state& fmls) override {
        }

        void updt_params(params_ref const& p) override {
        }
        
    };

    class arith_extract_eq : public extract_eq {
        ast_manager&       m;
        arith_util         a;
        bound_manager      m_bm;
        expr_ref_vector    m_args, m_trail;
        expr_sparse_mark   m_nonzero;
        bool               m_enabled = true;
        bool               m_eliminate_mod = true;


        // solve u mod r1 = y -> u = r1*mod!1 + y
        void solve_mod(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            if (!m_eliminate_mod)
                return;
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

        void solve_to_real(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            expr* z, *u;
            rational r;            
            if (!a.is_to_real(x, z) || !is_uninterp_const(z))
                return;
            if (a.is_to_real(y, u)) 
                eqs.push_back(dependent_eq(orig, to_app(z), expr_ref(u, m), d));
            else if (a.is_numeral(y, r) && r.is_int())
                eqs.push_back(dependent_eq(orig, to_app(z), expr_ref(a.mk_int(r), m), d));
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

        void mark_nonzero(expr* e) {
            m_trail.push_back(e);
            m_nonzero.mark(e);
        }

        void add_pos(expr* f) {
            expr* lhs = nullptr, * rhs = nullptr;
            rational val;
            if (a.is_le(f, lhs, rhs) && a.is_numeral(rhs, val) && val.is_neg())
                mark_nonzero(lhs);
            else if (a.is_ge(f, lhs, rhs) && a.is_numeral(rhs, val) && val.is_pos())
                mark_nonzero(lhs);
            else if (m.is_not(f, f)) {
                if (a.is_le(f, lhs, rhs) && a.is_numeral(rhs, val) && !val.is_neg())
                    mark_nonzero(lhs);
                else if (a.is_ge(f, lhs, rhs) && a.is_numeral(rhs, val) && !val.is_pos())
                    mark_nonzero(lhs);
                else if (m.is_eq(f, lhs, rhs) && a.is_numeral(rhs, val) && val.is_zero())
                    mark_nonzero(lhs);
            }
        }

        void solve_eq(expr* orig, expr* x, expr* y, expr_dependency* d, dep_eq_vector& eqs) {
            solve_add(orig, x, y, d, eqs);
            solve_mod(orig, x, y, d, eqs);
            solve_mul(orig, x, y, d, eqs);
            solve_to_real(orig, x, y, d, eqs);
        }

    public:

        arith_extract_eq(ast_manager& m) : m(m), a(m), m_bm(m), m_args(m), m_trail(m) {}

        void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) override {
            if (!m_enabled)
                return;
            auto [f, p, d] = e();
            expr* x, * y;
            if (m.is_eq(f, x, y) && a.is_int_real(x)) {
                solve_eq(f, x, y, d, eqs);
                solve_eq(f, y, x, d, eqs);
            }
            bool str;
            rational lo, hi;
            if (a.is_le(f, x, y) && a.is_numeral(y, hi) && m_bm.has_lower(x, lo, str) && !str && lo == hi) {
                expr_dependency_ref d2(m);
                d2 = m.mk_join(d, m_bm.lower_dep(x));
                if (is_uninterp_const(x)) 
                    eqs.push_back(dependent_eq(f, to_app(x), expr_ref(y, m), d2));
                else {
                    solve_eq(f, x, y, d2, eqs);                
                    solve_eq(f, y, x, d2, eqs);                
                }
            }
        }

        void pre_process(dependent_expr_state& fmls) override {
            if (!m_enabled)
                return;
            m_nonzero.reset();
            m_trail.reset();
            m_bm.reset();
            for (unsigned i = 0; i < fmls.qtail(); ++i) {
                auto [f, p, d] = fmls[i]();
                add_pos(f);
                m_bm(f, d, p);
            }
        }

        void updt_params(params_ref const& p) override {
            tactic_params tp(p);
            m_enabled = p.get_bool("theory_solver", tp.solve_eqs_ite_solver());
            m_eliminate_mod = p.get_bool("eliminate_mod", true);
        }
    };

    void register_extract_eqs(ast_manager& m, scoped_ptr_vector<extract_eq>& ex) {
        ex.push_back(alloc(arith_extract_eq, m));
        ex.push_back(alloc(basic_extract_eq, m));
        ex.push_back(alloc(bv_extract_eq, m));
    }
}
