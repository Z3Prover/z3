#include "model/model.h"
#include "model/model_evaluator.h"
#include "model/func_interp.h"
#include "model/model_pp.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/expr_safe_replace.h"
#include <iostream>

static void tst_partial_arithmetic() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    params_ref p;
    p.set_uint("max_steps", 10000);

    for (auto k : { OP_IDIV, OP_MOD, OP_REM, OP_DIV }) {
        bool is_int = k != OP_DIV;
        sort* s = is_int ? a.mk_int() : a.mk_real();
        expr_ref zero(a.mk_numeral(rational(0), is_int), m);
        expr_ref one(a.mk_numeral(rational(1), is_int), m);
        expr_ref four(a.mk_numeral(rational(4), is_int), m);
        expr_ref z(m.mk_const("z", s), m);
        expr_ref divisor(a.mk_add(one, z), m);
        expr_ref division(m.mk_app(a.get_family_id(), k, four, divisor), m);
        func_decl_ref f0(m);
        ENSURE(a.is_considered_partially_interpreted(to_app(division)->get_decl(), 2,
                                                    to_app(division)->get_args(), f0));
        for (int value : { 0, 5, 7 }) {
            model mdl(m);
            expr_ref v0(a.mk_numeral(rational(value), is_int), m);
            auto* fi = alloc(func_interp, m, 2);
            fi->set_else(v0);
            mdl.register_decl(f0, fi);
            model_evaluator eval(mdl, p);
            expr_ref condition(a.mk_gt(z, zero), m);
            expr_ref is_zero(m.mk_eq(divisor, zero), m);
            expr_ref nonzero(m.mk_not(is_zero), m);
            expr_ref_vector terms(m);
            terms.push_back(m.mk_ite(condition, division, v0));
            terms.push_back(m.mk_ite(condition, v0, division));
            terms.push_back(m.mk_ite(condition, division, zero));
            terms.push_back(m.mk_ite(nonzero, division, v0));
            terms.push_back(a.mk_add(one, division));
            for (expr* term : terms) {
                expr_ref result(m);
                ENSURE(eval.eval(term, result, false));
                for (int sample : { -2, -1, 0, 1, 3 }) {
                    expr_ref numeral(a.mk_numeral(rational(sample), is_int), m);
                    expr_safe_replace subst(m);
                    subst.insert(z, numeral);
                    expr_ref original(term, m), reduced(result, m), expected(m), actual(m);
                    subst(original);
                    subst(reduced);
                    ENSURE(eval.eval(original, expected, false));
                    ENSURE(eval.eval(reduced, actual, false));
                    ENSURE(a.is_numeral(actual));
                    ENSURE(actual == expected);
                }

                expr_ref body(a.mk_gt(term, zero), m);
                expr_safe_replace subst(m);
                expr_ref x(m.mk_var(0, s), m);
                subst.insert(z, x);
                subst(body);
                symbol name("x");
                expr_ref quantified(m.mk_exists(1, &s, &name, body), m);
                for (bool completion : { false, true })
                    ENSURE(eval.eval(quantified, result, completion));
            }
        }
    }
}

void tst_model_evaluator() {
    tst_partial_arithmetic();
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);

    model mdl(m);

    sort* sI = a.mk_int();

    sort* dom[2] = { sI, m.mk_bool_sort() };
    func_decl_ref f(m.mk_func_decl(symbol("f"), 2, dom, sI), m);
    func_decl_ref g(m.mk_func_decl(symbol("g"), 2, dom, sI), m);
    func_decl_ref h(m.mk_func_decl(symbol("h"), 2, dom, sI), m);
    func_decl_ref F(m.mk_func_decl(symbol("F"), 2, dom, sI), m);
    func_decl_ref G(m.mk_func_decl(symbol("G"), 2, dom, sI), m);
    expr_ref vI0(m.mk_var(0, sI), m);
    expr_ref vI1(m.mk_var(1, sI), m);
    expr_ref vB0(m.mk_var(0, m.mk_bool_sort()), m);
    expr_ref vB1(m.mk_var(1, m.mk_bool_sort()), m);
    expr_ref vB2(m.mk_var(2, m.mk_bool_sort()), m);
    expr* vI0p = vI0.get();
    expr* vI1p = vI1.get();
    expr* vB1p = vB1.get();
    expr* vB2p = vB2.get();

    expr_ref f01(m.mk_app(f, vI0p, vB1p), m);
    expr_ref g01(m.mk_app(g, vI0p, vB1p), m);
    expr_ref h01(m.mk_app(h, vI0p, vB1p), m);
    func_interp* fi = alloc(func_interp, m, 2);
    func_interp* gi = alloc(func_interp, m, 2);
    func_interp* hi = alloc(func_interp, m, 2);
    {
        expr_ref then_value(m.mk_app(f, vI0p, vB1p), m);
        expr_ref else_value(m.mk_app(g, vI0p, vB1p), m);
        hi->set_else(m.mk_ite(vB1p, then_value, else_value));
    }
    mdl.register_decl(h, hi);
    

    model_evaluator eval(mdl);

    expr_ref e(m), v(m);

    for (bool is_int : {true, false}) {
        expr_ref x(m.mk_const("x", is_int ? a.mk_int() : a.mk_real()), m);
        expr_ref_vector bounds(m);
        for (unsigned i = 1; i <= 3; ++i) {
            expr_ref numeral(a.mk_numeral(rational(i), is_int), m);
            bounds.push_back(a.mk_le(numeral, x));
        }
        unsigned orders[][3] = {
            {0, 2, 1}, {0, 1, 2}, {1, 0, 2},
            {1, 2, 0}, {2, 0, 1}, {2, 1, 0}
        };
        for (auto const& order : orders) {
            e = m.mk_and(bounds.get(order[0]), bounds.get(order[1]), bounds.get(order[2]));
            ENSURE(eval.eval(e, v, false));
            ENSURE(v == bounds[2]);
        }
        e = m.mk_and(bounds.get(2), bounds.get(0));
        ENSURE(eval.eval(e, v, false));
        ENSURE(v == bounds[2]);
    }

    {
        symbol nI("N");
        {
            expr_ref condition(m.mk_exists(1, &sI, &nI, a.mk_le(vI0p, m.mk_app(F, vI1p, vB2p))), m);
            expr_ref else_value(a.mk_int(1), m);
            fi->set_else(m.mk_ite(condition, vI0p, else_value));
        }
        {
            expr_ref condition(m.mk_exists(1, &sI, &nI, a.mk_le(vI0p, m.mk_app(G, vI1p, vB2p))), m);
            expr_ref then_value(a.mk_int(2), m);
            gi->set_else(m.mk_ite(condition, then_value, vI0p));
        }
        mdl.register_decl(g, gi);
        mdl.register_decl(f, fi);
        model_pp(std::cout, mdl);
        e = m.mk_app(h, vI0p, vB1p);
        eval(e, v);
        std::cout << e << " " << v << "\n";
    }

    {
        fi->set_else(m.mk_app(F, vI0p, vB1p));
        gi->set_else(m.mk_app(G, vI0p, vB1p));
        model_pp(std::cout, mdl);
        e = m.mk_app(h, vI0p, vB1p);
        eval(e, v);
        std::cout << e << " " << v << "\n";
    }

    {
        func_interp fi2(m, 1);
        expr_ref zero(a.mk_int(0), m);
        expr_ref one(a.mk_int(1), m);
        fi2.set_else(zero);
        for (unsigned i = 0; i < 600; ++i) {
            expr_ref arg(a.mk_int(rational(i)), m);
            expr* args[1] = { arg.get() };
            fi2.insert_entry(args, i == 599 ? one.get() : zero.get());
        }
        fi2.compress();
        ENSURE(fi2.num_entries() == 1);

        expr_ref removed_arg(a.mk_int(0), m);
        [[maybe_unused]] expr* removed_args[1] = { removed_arg.get() };
        ENSURE(fi2.get_entry(removed_args) == nullptr);

        expr_ref kept_arg(a.mk_int(599), m);
        expr* kept_args[1] = { kept_arg.get() };
        [[maybe_unused]] func_entry* kept = fi2.get_entry(kept_args);
        ENSURE(kept != nullptr);
        ENSURE(kept->get_result() == one.get());
    }

    {
        array_util au(m);
        sort* dom[1] = { sI };
        func_decl_ref fn(m.mk_func_decl(symbol("fn"), 1, dom, sI), m);
        expr_ref as_array(au.mk_as_array(fn), m);
        ENSURE(eval.eval(as_array, v, true));
        ENSURE(!au.is_as_array(v));
        ENSURE(au.is_const(v));
        func_interp* fni = mdl.get_func_interp(fn);
        ENSURE(fni != nullptr);
        ENSURE(fni->get_else() != nullptr);
    }
    
}
