/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_curve_certificate.cpp

Abstract:

    Unboundedness certificates along polynomial curves through recent models.

Author:

    Lev Nachmanson (levnach) 2026-10-29

--*/
#include "opt/opt_curve_certificate.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "model/model_evaluator.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"

namespace opt {

    curve_certificate::curve_certificate(ast_manager& m, params_ref const& p):
        m(m), a(m), m_params(p) {}

    char const* curve_certificate::kind_name() const {
        if (m_unit)
            return "unit direction";
        switch (m_degree) {
        case 1: return "ray";
        case 2: return "quadratic";
        default: return "cubic";
        }
    }

    namespace {
        struct constant_collector {
            arith_util&      a;
            ptr_vector<app>& arith_consts;
            ptr_vector<app>& other_consts;
            constant_collector(arith_util& a, ptr_vector<app>& arith_consts, ptr_vector<app>& other_consts):
                a(a), arith_consts(arith_consts), other_consts(other_consts) {}
            void operator()(var*) {}
            void operator()(quantifier*) {}
            void operator()(app* n) {
                if (!is_uninterp_const(n))
                    return;
                if (a.is_int_real(n))
                    arith_consts.push_back(n);
                else
                    other_consts.push_back(n);
            }
        };
    }

    void curve_certificate::collect_constants(expr_ref_vector const& hard, expr* obj,
                                              ptr_vector<app>& arith_consts, ptr_vector<app>& other_consts) {
        constant_collector proc(a, arith_consts, other_consts);
        expr_mark visited;
        for (expr* f : hard)
            for_each_expr(proc, visited, f);
        for_each_expr(proc, visited, obj);
    }

    // sums, products, negations, numerals, arithmetic constants, to_real,
    // and powers with a natural exponent
    bool curve_certificate::is_polynomial(expr* e) {
        ptr_vector<expr> todo;
        todo.push_back(e);
        rational r;
        while (!todo.empty()) {
            expr* t = todo.back();
            todo.pop_back();
            if (a.is_numeral(t))
                continue;
            if (is_uninterp_const(t)) {
                if (!a.is_int_real(t))
                    return false;
                continue;
            }
            if (a.is_add(t) || a.is_sub(t) || a.is_mul(t) || a.is_uminus(t) || a.is_to_real(t)) {
                for (expr* arg : *to_app(t))
                    todo.push_back(arg);
                continue;
            }
            expr* base = nullptr;
            expr* exponent = nullptr;
            if (a.is_power(t, base, exponent) && a.is_numeral(exponent, r) && r.is_unsigned()) {
                todo.push_back(base);
                continue;
            }
            return false;
        }
        return true;
    }

    bool curve_certificate::evaluate(model& mdl, ptr_vector<app> const& consts, vector<rational>& values) {
        model_evaluator ev(mdl);
        ev.set_model_completion(true);
        values.reset();
        rational r;
        for (app* c : consts) {
            expr_ref v = ev(c);
            if (!a.is_numeral(v, r))
                return false;
            values.push_back(r);
        }
        return true;
    }

    lbool curve_certificate::prove_unbounded(expr_ref_vector const& hard, expr* obj, sref_vector<model> const& models) {
        if (models.empty() || !is_polynomial(obj))
            return l_undef;
        ptr_vector<app> arith_consts, other_consts;
        collect_constants(hard, obj, arith_consts, other_consts);
        if (arith_consts.empty())
            return l_undef;
        unsigned k = arith_consts.size();
        unsigned n = models.size();
        model& latest = *models[n - 1];

        // values[i] holds the i-th most recent model
        vector<vector<rational>> values;
        for (unsigned i = 0; i < n && i <= max_degree; ++i) {
            vector<rational> row;
            if (!evaluate(*models[n - 1 - i], arith_consts, row))
                break;
            values.push_back(row);
        }
        if (values.empty())
            return l_undef;

        // differences[j] is the j-th backward difference at the latest model:
        // sum over i <= j of (-1)^i binomial(j, i) values[i]
        vector<vector<rational>> differences;
        for (unsigned j = 0; j < values.size(); ++j) {
            vector<rational> row(k, rational::zero());
            rational binomial(1);
            for (unsigned i = 0; i <= j; ++i) {
                rational sign = (i % 2 == 0) ? rational::one() : rational::minus_one();
                for (unsigned c = 0; c < k; ++c)
                    row[c] += sign * binomial * values[i][c];
                binomial = binomial * rational(j - i) / rational(i + 1);
            }
            differences.push_back(row);
        }

        // the polynomial of lowest degree through the recent models
        vector<coefficients> curve(k);
        for (unsigned degree = 1; degree < differences.size(); ++degree) {
            bool bends = false;
            for (unsigned c = 0; c < k; ++c)
                bends |= !differences[degree][c].is_zero();
            if (!bends)
                continue;
            for (unsigned c = 0; c < k; ++c) {
                curve[c].reset();
                for (unsigned j = 0; j <= degree; ++j)
                    curve[c].push_back(differences[j][c]);
            }
            if (certify(hard, obj, latest, arith_consts, other_consts, curve, degree, false))
                return l_true;
        }

        // unit directions along the objective's own variables
        ptr_vector<app> obj_consts, obj_other_consts;
        expr_ref_vector no_hard(m);
        collect_constants(no_hard, obj, obj_consts, obj_other_consts);
        if (obj_consts.size() > 8)
            return l_undef;
        for (app* v : obj_consts) {
            for (int sign : {1, -1}) {
                for (unsigned c = 0; c < k; ++c) {
                    curve[c].reset();
                    curve[c].push_back(values[0][c]);
                    curve[c].push_back(arith_consts[c] == v ? rational(sign) : rational::zero());
                }
                if (certify(hard, obj, latest, arith_consts, other_consts, curve, 1, true))
                    return l_true;
            }
        }
        return l_undef;
    }

    bool curve_certificate::certify(expr_ref_vector const& hard, expr* obj, model& latest,
                                    ptr_vector<app> const& arith_consts, ptr_vector<app> const& other_consts,
                                    vector<coefficients> const& curve, unsigned degree, bool unit) {
        unsigned k = arith_consts.size();
        for (unsigned c = 0; c < k; ++c)
            if (a.is_int(arith_consts[c]))
                for (rational const& coefficient : curve[c])
                    if (!coefficient.is_int())
                        return false;

        // t is the integer parameter; basis[j] = t (t + 1) ... (t + j - 1) / j!
        // is an integer for every integer t, defined through j * basis[j] =
        // basis[j - 1] * (t + j - 1).
        app_ref t(m.mk_fresh_const("t", a.mk_int()), m);
        expr_ref_vector basis(m), along(m);
        basis.push_back(a.mk_int(1));
        basis.push_back(t);
        along.push_back(a.mk_ge(t, a.mk_int(0)));
        for (unsigned j = 2; j <= degree; ++j) {
            app_ref b(m.mk_fresh_const("h", a.mk_int()), m);
            along.push_back(m.mk_eq(a.mk_mul(a.mk_int(j), b), a.mk_mul(basis.get(j - 1), a.mk_add(t, a.mk_int(j - 1)))));
            basis.push_back(b);
        }

        expr_ref_vector trail(m);
        expr_safe_replace subst(m);
        for (unsigned c = 0; c < k; ++c) {
            bool is_int = a.is_int(arith_consts[c]);
            expr_ref_vector sum(m);
            sum.push_back(a.mk_numeral(curve[c][0], is_int));
            for (unsigned j = 1; j < curve[c].size(); ++j) {
                if (curve[c][j].is_zero())
                    continue;
                expr* b = is_int ? basis.get(j) : a.mk_to_real(basis.get(j));
                sum.push_back(a.mk_mul(a.mk_numeral(curve[c][j], is_int), b));
            }
            expr_ref term(sum.size() == 1 ? sum.get(0) : a.mk_add(sum.size(), sum.data()), m);
            trail.push_back(term);
            subst.insert(arith_consts[c], term);
        }
        model_evaluator ev(latest);
        ev.set_model_completion(true);
        for (app* c : other_consts) {
            expr_ref v = ev(c);
            if (m.is_value(v)) {
                trail.push_back(v);
                subst.insert(c, v);
            }
        }

        auto check = [&](expr* query) {
            solver_ref s = mk_smt_solver(m, m_params, symbol::null);
            for (expr* f : along)
                s->assert_expr(f);
            s->assert_expr(query);
            return s->check_sat(0, nullptr);
        };

        // every hard constraint holds at every point of the curve
        expr_ref_vector violations(m);
        for (expr* f : hard) {
            expr_ref g(m);
            subst(f, g);
            violations.push_back(mk_not(m, g));
        }
        if (!violations.empty() && check(mk_or(violations)) != l_false)
            return false;

        // the objective never drops below its value at the latest model
        expr_ref p(m);
        subst(obj, p);
        expr_ref p0 = ev(obj);
        rational r;
        if (!a.is_numeral(p0, r))
            return false;
        if (check(a.mk_lt(p, p0)) != l_false)
            return false;

        // and is not constant along the curve
        expr_ref_vector grows(m);
        grows.push_back(a.mk_ge(t, a.mk_int(1)));
        grows.push_back(m.mk_not(m.mk_eq(p, p0)));
        if (check(mk_and(grows)) != l_true)
            return false;

        m_degree = degree;
        m_unit = unit;
        return true;
    }
}
