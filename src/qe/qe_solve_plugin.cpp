/**
Copyright (c) 2018 Microsoft Corporation

Module Name:

    qe_solve.cpp

Abstract:

    Light-weight variable solving plugin model for qe-lite and term_graph.

Author:

    Nikolaj Bjorner (nbjorner), Arie Gurfinkel 2018-6-8

Revision History:


--*/

#include "ast/arith_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "qe/qe_solve_plugin.h"

namespace qe {

    expr_ref solve_plugin::operator()(expr* lit) {
        if (m.is_not(lit, lit))
            return solve(lit, false);
        else
            return solve(lit, true);
    }

    class arith_solve_plugin : public solve_plugin {
        arith_util a;
    public:
        arith_solve_plugin(ast_manager& m, is_variable_proc& is_var): solve_plugin(m, m.get_family_id("arith"), is_var), a(m) {}

        typedef std::pair<bool,expr*> signed_expr;

        /**
         *\brief
         *   return r * (sum_{(sign,e) \in exprs} sign * e)
         */
        expr_ref mk_term(bool is_int, rational const& r, bool sign, svector<signed_expr> const& exprs) {
            expr_ref_vector result(m);
            for (auto const& kv : exprs) {
                bool sign2 = kv.first;
                expr* e    = kv.second;
                rational r2(r);
                if (sign == sign2) {
                    r2.neg();
                }
                if (!r2.is_one()) {
                    result.push_back(a.mk_mul(a.mk_numeral(r2, is_int), e));
                }
                else {
                    result.push_back(e);
                }
            }
            return a.mk_add_simplify(result);
        }

        /**
         * \brief return true if lhs = rhs can be solved as v = t, where v is a variable.
         */
        bool solve(expr* lhs, expr* rhs, expr_ref& v, expr_ref& t) {
            if (!a.is_int(lhs) && !a.is_real(rhs)) {
                return false;
            }
            rational a_val;
            bool is_int = a.is_int(lhs);
            svector<signed_expr> todo, done;
            todo.push_back(std::make_pair(true,  lhs));
            todo.push_back(std::make_pair(false, rhs));
            while (!todo.empty()) {
                expr* e = todo.back().second;
                bool sign = todo.back().first;
                todo.pop_back();
                if (a.is_add(e)) {
                    for (expr* arg : *to_app(e)) {
                        todo.push_back(std::make_pair(sign, arg));
                    }
                }
                else if (a.is_sub(e)) {
                    app* sub = to_app(e);
                    todo.push_back(std::make_pair(sign, sub->get_arg(0)));
                    for (unsigned i = 1; i < sub->get_num_args(); ++i) {
                        todo.push_back(std::make_pair(!sign, sub->get_arg(i)));
                    }
                }
                else if (a.is_uminus(e)) {
                    todo.push_back(std::make_pair(!sign, to_app(e)->get_arg(0)));
                }
                else if (is_invertible_mul(is_int, e, a_val)) {
                    done.append(todo);
                    v = e;
                    a_val = rational(1)/a_val;
                    t = mk_term(is_int, a_val, sign, done);
                    TRACE("qe", tout << mk_pp(lhs, m) << " " << mk_pp(rhs, m) << " " << mk_pp(e, m) << " := " << t << "\n";);
                    return true;
                }
                else {
                    done.push_back(std::make_pair(sign, e));
                }
            }
            return false;
        }

        // is x a constant and can we safely divide by x to solve for a variable?
        bool is_invertible_const(bool is_int, expr* x, rational& a_val) {
            expr* y;
            if (a.is_uminus(x, y) && is_invertible_const(is_int, y, a_val)) {
                a_val.neg();
                return true;
            }
            else if (a.is_numeral(x, a_val) && !a_val.is_zero()) {
                if (!is_int || a_val.is_one() || a_val.is_minus_one()) {
                    return true;
                }
            }
            return false;
        }

        // is arg of the form a_val * v, where a_val
        // is a constant that we can safely divide by.
        bool is_invertible_mul(bool is_int, expr*& arg, rational& a_val) {
            if (is_variable(arg)) {
                a_val = rational(1);
                return true;
            }
            expr* x, *y;
            if (a.is_mul(arg, x, y)) {
                if (is_variable(x) && is_invertible_const(is_int, y, a_val)) {
                    arg = x;
                    return true;
                }
                if (is_variable(y) && is_invertible_const(is_int, x, a_val)) {
                    arg = y;
                    return true;
                }
            }
            return false;
        }


        expr_ref mk_eq_core (expr *e1, expr *e2) {
            expr_ref v(m), t(m);
            if (solve(e1, e2, v, t)) {
                return expr_ref(m.mk_eq(v, t), m);
            }

            if (a.is_zero(e1)) {
                std::swap(e1, e2);
            }
            // y + -1*x == 0  --> y = x
            expr *a0 = nullptr, *a1 = nullptr, *x = nullptr;
            if (a.is_zero(e2) && a.is_add(e1, a0, a1)) {
                if (a.is_times_minus_one(a1, x)) {
                    e1 = a0;
                    e2 = x;
                }
                else if (a.is_times_minus_one(a0, x)) {
                    e1 = a1;
                    e2 = x;
                }
            }
            return expr_ref(m.mk_eq(e1, e2), m);
        }

        app* mk_le_zero(expr *arg) {
            expr *e1, *e2, *e3;
            if (a.is_add(arg, e1, e2)) {
                // e1-e2<=0 --> e1<=e2
                if (a.is_times_minus_one(e2, e3)) {
                    return a.mk_le(e1, e3);
                }
                // -e1+e2<=0 --> e2<=e1
                else if (a.is_times_minus_one(e1, e3)) {
                    return a.mk_le(e2, e3);
                }
            }
            return a.mk_le(arg, mk_zero());
        }

        app* mk_ge_zero(expr *arg) {
            expr *e1, *e2, *e3;
            if (a.is_add(arg, e1, e2)) {
                // e1-e2>=0 --> e1>=e2
                if (a.is_times_minus_one(e2, e3)) {
                    return a.mk_ge(e1, e3);
                }
                // -e1+e2>=0 --> e2>=e1
                else if (a.is_times_minus_one(e1, e3)) {
                    return a.mk_ge(e2, e3);
                }
            }
            return a.mk_ge(arg, mk_zero());
        }

        bool mk_le_core (expr *arg1, expr * arg2, expr_ref &result) {
            // t <= -1  ==> t < 0 ==> ! (t >= 0)
            rational n;
            if (a.is_int (arg1) && a.is_minus_one (arg2)) {
                result = m.mk_not (mk_ge_zero (arg1));
                return true;
            }
            else if (a.is_zero(arg2)) {
                result = mk_le_zero(arg1);
                return true;
            }
            else if (a.is_int(arg1) && a.is_numeral(arg2, n) && n < 0) {
                // t <= n ==> t < n + 1 ==> ! (t >= n + 1)
                result = m.mk_not(a.mk_ge(arg1, a.mk_numeral(n+1, true)));
                return true;
            }
            return false;
        }

        expr * mk_zero () {
            return a.mk_numeral (rational (0), true);
        }

        bool is_one (expr const * n) const {
            rational val;
            return a.is_numeral (n, val) && val.is_one ();
        }

        bool mk_ge_core (expr * arg1, expr * arg2, expr_ref &result) {
            // t >= 1 ==> t > 0 ==> ! (t <= 0)
            rational n;
            if (a.is_int (arg1) && is_one (arg2)) {
                result = m.mk_not (mk_le_zero (arg1));
                return true;
            }
            else if (a.is_zero(arg2)) {
                result = mk_ge_zero(arg1);
                return true;
            }
            else if (a.is_int(arg1) && a.is_numeral(arg2, n) && n > 0) {
                // t >= n ==> t > n - 1 ==> ! (t <= n - 1)
                result = m.mk_not(a.mk_le(arg1, a.mk_numeral(n-1, true)));
                return true;
            }
            return false;
        }

        expr_ref solve(expr* atom, bool is_pos) override {
            expr *e1, *e2;

            expr_ref res(atom, m);
            if (m.is_eq (atom, e1, e2)) {
                expr_ref v(m), t(m);
                v = e1; t = e2;
                // -- attempt to solve using arithmetic
                solve(e1, e2, v, t);
                // -- normalize equality
                res = mk_eq_core(v, t);
            }
            else if (a.is_le(atom, e1, e2)) {
                mk_le_core(e1, e2, res);
            }
            else if (a.is_ge(atom, e1, e2)) {
                mk_ge_core(e1, e2, res);
            }

            // restore negation
            if (!is_pos) {
                res = mk_not(m, res);
            }
            return res;
        }
    };

    class basic_solve_plugin : public solve_plugin {
    public:
        basic_solve_plugin(ast_manager& m, is_variable_proc& is_var):
            solve_plugin(m, m.get_basic_family_id(), is_var) {}

        expr_ref solve(expr *atom, bool is_pos) override {
            expr_ref res(atom, m);
            expr* lhs = nullptr, *rhs = nullptr, *n = nullptr;
            if (m.is_eq(atom, lhs, rhs)) {
                if (m.is_not(lhs, n) && is_variable(n)) {
                    res = m.mk_eq(n, mk_not(m, rhs));
                }
                else if (m.is_not(rhs, n) && is_variable(n)) {
                    res = m.mk_eq(n, mk_not(m, lhs));
                }
                else if (is_variable(rhs) && !is_variable(lhs)) {
                    res = m.mk_eq(rhs, lhs);
                }
            }
            // (ite cond (= VAR t) (= VAR t2)) case
            expr* cond = nullptr, *th = nullptr, *el = nullptr;
            if (m.is_ite(atom, cond, th, el)) {
                expr_ref r1 = solve(th, true);
                expr_ref r2 = solve(el, true);
                expr* v1 = nullptr, *t1 = nullptr, *v2 = nullptr, *t2 = nullptr;
                if (m.is_eq(r1, v1, t1) && m.is_eq(r2, v2, t2) && v1 == v2) {
                    res = m.mk_eq(v1, m.mk_ite(cond, t1, t2));
                }
            }

            if (is_variable(atom) && m.is_bool(atom)) {
                res = m.mk_eq(atom, m.mk_bool_val(is_pos));
                return res;
            }

            return is_pos ? res : mk_not(res);
        }
    };

    class dt_solve_plugin : public solve_plugin {
        datatype_util dt;
    public:
        dt_solve_plugin(ast_manager& m, is_variable_proc& is_var):
            solve_plugin(m, m.get_family_id("datatype"), is_var),
            dt(m) {}

        expr_ref solve(expr *atom, bool is_pos) override {
            expr_ref res(atom, m);
            expr* lhs = nullptr, *rhs = nullptr;
            if (m.is_eq(atom, lhs, rhs)) {
                if (dt.is_constructor(rhs)) {
                    std::swap(lhs, rhs);
                }
                if (dt.is_constructor(lhs) && dt.is_constructor(rhs)) {
                    app* l = to_app(lhs), *r = to_app(rhs);
                    if (l->get_decl() == r->get_decl()) {
                        expr_ref_vector eqs(m);
                        for (unsigned i = 0, sz = l->get_num_args(); i < sz; ++i) {
                            eqs.push_back(m.mk_eq(l->get_arg(i), r->get_arg(i)));
                        }
                        res = mk_and(eqs);
                    }
                    else {
                        res = m.mk_false();
                    }
                }
                else if (dt.is_constructor(lhs)) {
                    app* l = to_app(lhs);
                    func_decl* d = l->get_decl();
                    expr_ref_vector conjs(m);
                    conjs.push_back(dt.mk_is(d, rhs));
                    ptr_vector<func_decl> const& acc = *dt.get_constructor_accessors(d);
                    for (unsigned i = 0; i < acc.size(); ++i) {
                        conjs.push_back(m.mk_eq(l->get_arg(i), m.mk_app(acc[i], rhs)));
                    }
                    res = mk_and(conjs);
                }
            }
            // TBD: can also solve for is_nil(x) by x = nil
            //
            return is_pos ? res : mk_not(res);
        }
    };

    class bv_solve_plugin : public solve_plugin {
    public:
        bv_solve_plugin(ast_manager& m, is_variable_proc& is_var): solve_plugin(m, m.get_family_id("bv"), is_var) {}
        expr_ref solve(expr *atom, bool is_pos) override {
            expr_ref res(atom, m);
            return is_pos ? res : mk_not(res);
        }
    };

    class array_solve_plugin : public solve_plugin {
    public:
        array_solve_plugin(ast_manager& m, is_variable_proc& is_var): solve_plugin(m, m.get_family_id("array"), is_var) {}
        expr_ref solve(expr *atom, bool is_pos) override {
            expr_ref res(atom, m);
            return is_pos ? res : mk_not(res);
        }
    };

    solve_plugin* mk_basic_solve_plugin(ast_manager& m, is_variable_proc& is_var) {
        return alloc(basic_solve_plugin, m, is_var);
    }

    solve_plugin* mk_arith_solve_plugin(ast_manager& m, is_variable_proc& is_var) {
        return alloc(arith_solve_plugin, m, is_var);
    }

    solve_plugin* mk_dt_solve_plugin(ast_manager& m, is_variable_proc& is_var) {
        return alloc(dt_solve_plugin, m, is_var);
    }

#if 0
    solve_plugin* mk_bv_solve_plugin(ast_manager& m, is_variable_proc& is_var) {
        return alloc(bv_solve_plugin, m, is_var);
    }

    solve_plugin* mk_array_solve_plugin(ast_manager& m, is_variable_proc& is_var) {
        return alloc(array_solve_plugin, m, is_var);
    }
#endif

}
