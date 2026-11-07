#include "model/model.h"
#include "model/model_evaluator.h"
#include "model/func_interp.h"
#include "model/model_pp.h"
#include "model/model_instance_generator.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/has_free_vars.h"
#include "ast/well_sorted.h"
#include <iostream>

namespace {
    struct instance_context : model_instance_generator::context {
        ast_manager& m;
        model mdl;
        expr_ref_vector terms;
        vector<expr_ref_vector> instances;
        obj_hashtable<func_decl> auxiliary;

        instance_context(ast_manager& m): m(m), mdl(m), terms(m) {}
        model_core& get_model() override { return mdl; }
        bool is_auxiliary(func_decl* f) const override {
            return f->is_skolem() || auxiliary.contains(f);
        }
        void get_terms(expr_ref_vector& result) override { result.append(terms); }
        expr_ref rewrite_value(expr* e) override { return expr_ref(e, m); }
        void add_instance(quantifier* q, expr_ref_vector const& bindings) override {
            ENSURE(q->get_num_decls() == bindings.size());
            for (unsigned i = 0; i < bindings.size(); ++i) {
                ENSURE(bindings.get(i)->get_sort() == q->get_decl_sort(i));
                ENSURE(!has_free_vars(bindings.get(i)));
                ENSURE(is_well_sorted(m, bindings.get(i)));
            }
            instances.push_back(bindings);
        }
    };
}

static void check_instance_provenance(bool skolem) {
    for (char const* name : {"elem!user", "k!user", "sk!user", "ordinary"}) {
        ast_manager m;
        reg_decl_plugins(m);
        array_util array(m);
        sort_ref u(m.mk_uninterpreted_sort(symbol("U")), m);
        sort_ref v(m.mk_uninterpreted_sort(symbol("V")), m);
        sort_ref as(array.mk_array_sort(u, v), m);
        expr_ref user_u(m.mk_const(name, u), m);
        expr_ref user_v(m.mk_const(name, v), m);
        expr_ref fresh_u(m.mk_fresh_const("unrelated", u, skolem), m);
        expr_ref fresh_v(m.mk_fresh_const("unrelated", v, skolem), m);
        func_decl_ref wrap_u(m.mk_func_decl(symbol("wrap-u"), u, u), m);
        func_decl_ref wrap_v(m.mk_func_decl(symbol("wrap-v"), v, v), m);
        expr_ref nested_u(m.mk_app(wrap_u.get(), fresh_u.get()), m);
        expr_ref nested_v(m.mk_app(wrap_v.get(), fresh_v.get()), m);
        expr_ref d(m.mk_const("default", v), m);
        expr_ref auxiliary_array(m.mk_fresh_const("array", as, skolem), m);
        sort* guard_domain[2] = { u, u };
        func_decl_ref guard(m.mk_func_decl(symbol("guard"), 2, guard_domain, m.mk_bool_sort()), m);
        expr_ref f(array.mk_const_array(as, d), m);
        expr_ref inner_f(m.mk_var(2, as), m);
        expr_ref inner_u(m.mk_var(1, u), m);
        expr_ref x(m.mk_var(0, u), m);
        expr_ref gx(m.mk_app(guard.get(), inner_u.get(), x.get()), m);
        expr_ref fx(array.mk_select(inner_f, x), m);
        expr_ref eq(m.mk_eq(fx, d), m);
        expr_ref inner_body(m.mk_ite(gx, m.mk_true(), eq), m);
        sort* dom = u;
        symbol x_name("x");
        expr_ref inner(m.mk_forall(1, &dom, &x_name, inner_body), m);
        expr_ref default_eq(m.mk_eq(d, d), m);
        expr_ref body(m.mk_and(inner, default_eq), m);
        sort* sorts[2] = { as, u };
        symbol names[2] = { symbol("f"), symbol("u") };
        expr_ref_vector bindings(m);
        bindings.push_back(f);
        bindings.push_back(fresh_u);
        ptr_vector<func_decl> bases;
        bases.resize(2, nullptr);
        for (unsigned shape = 0; shape < 3; ++shape) {
            expr_ref q_body(body);
            if (shape == 1) {
                expr_ref outer_f(m.mk_var(1, as), m);
                expr_ref outer_u(m.mk_var(0, u), m);
                func_decl_ref index(m.mk_fresh_func_decl("index", 2, sorts, u), m);
                expr_ref idx(m.mk_app(index.get(), outer_f.get(), outer_u.get()), m);
                expr_ref gidx(m.mk_app(guard.get(), outer_u.get(), idx.get()), m);
                expr_ref fidx(array.mk_select(outer_f, idx), m);
                expr_ref eqidx(m.mk_eq(fidx, d), m);
                expr_ref guard_body(m.mk_ite(gidx, m.mk_true(), eqidx), m);
                q_body = m.mk_and(guard_body, default_eq);
            }
            else if (shape == 2) {
                expr_ref bound_f(m.mk_var(3, as), m);
                expr_ref bound_g(m.mk_app(guard.get(), inner_u.get(), x.get()), m);
                expr_ref bound_fx(array.mk_select(bound_f, x), m);
                expr_ref bound_eq(m.mk_eq(bound_fx, d), m);
                expr_ref nested(m.mk_ite(bound_g, m.mk_true(), bound_eq), m);
                nested = m.mk_forall(1, &dom, &x_name, nested);
                nested = m.mk_forall(1, &dom, &x_name, nested);
                q_body = m.mk_and(nested, default_eq);
            }
            quantifier_ref q(m.mk_forall(2, sorts, names, q_body), m);
            for (bool has_replacement : {false, true}) {
                instance_context ctx(m);
                ctx.auxiliary.insert(to_app(fresh_u)->get_decl());
                ctx.auxiliary.insert(to_app(fresh_v)->get_decl());
                ctx.auxiliary.insert(to_app(auxiliary_array)->get_decl());
                ctx.mdl.register_decl(to_app(auxiliary_array)->get_decl(), f);
                ctx.terms.push_back(fresh_u);
                ctx.terms.push_back(nested_u);
                ctx.terms.push_back(fresh_v);
                ctx.terms.push_back(nested_v);
                if (has_replacement)
                    ctx.terms.push_back(user_u);
                ctx.terms.push_back(user_v);
                model_instance_generator generator(ctx);
                generator(q, bindings, bases);
                bool expect_instance = has_replacement && shape != 2;
                ENSURE(ctx.instances.size() == (expect_instance ? 1u : 0u));
                if (!expect_instance)
                    continue;
                expr_ref expected_guard(m.mk_app(guard.get(), user_u.get(), x.get()), m);
                expr_ref expected_body(m.mk_ite(expected_guard, user_v, d), m);
                expr_ref expected(m.mk_lambda(1, &dom, &x_name, expected_body), m);
                ENSURE(ctx.instances[0].get(0) == expected);
                ENSURE(ctx.instances[0].get(1) == user_u);
            }
        }
    }
}

static void check_store_instance_base() {
    ast_manager m;
    reg_decl_plugins(m);
    array_util array(m);
    arith_util arith(m);
    sort_ref as(array.mk_array_sort(arith.mk_int(), arith.mk_int()), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref one(arith.mk_int(1), m);
    expr_ref f(array.mk_const_array(as, one), m);
    expr_ref base(m.mk_const("base", as), m);
    expr_ref auxiliary(m.mk_fresh_const("array", as, false), m);
    expr_ref bound_f(m.mk_var(1, as), m);
    expr_ref index(m.mk_var(0, arith.mk_int()), m);
    expr_ref selected(array.mk_select(bound_f, index), m);
    expr_ref body(m.mk_eq(selected, zero), m);
    sort* sorts[2] = { as, arith.mk_int() };
    symbol names[2] = { symbol("f"), symbol("i") };
    quantifier_ref q(m.mk_forall(2, sorts, names, body), m);
    expr_ref_vector bindings(m);
    bindings.push_back(f);
    bindings.push_back(one);
    ptr_vector<func_decl> bases;
    bases.resize(2, nullptr);
    for (bool has_base : {false, true}) {
        instance_context ctx(m);
        ctx.auxiliary.insert(to_app(auxiliary)->get_decl());
        ctx.mdl.register_decl(to_app(auxiliary)->get_decl(), f);
        if (has_base)
            ctx.mdl.register_decl(to_app(base)->get_decl(), f);
        model_instance_generator generator(ctx);
        generator(q, bindings, bases);
        ENSURE(ctx.instances.size() == (has_base ? 1u : 0u));
        if (has_base) {
            expr* args[3] = { base, one, zero };
            expr_ref expected(array.mk_store(3, args), m);
            ENSURE(ctx.instances[0].get(0) == expected);
            ENSURE(ctx.instances[0].get(1) == one);
        }
    }
}

static void check_boxed_array_instance() {
    ast_manager m;
    reg_decl_plugins(m);
    array_util array(m);
    arith_util arith(m);
    datatype::util dt(m);
    sort_ref as(array.mk_array_sort(m.mk_bool_sort(), arith.mk_int()), m);
    func_decl_ref fst(m), snd(m), pair(m);
    sort_ref box = dt.mk_pair_datatype(as, m.mk_bool_sort(), fst, snd, pair);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref one(arith.mk_int(1), m);
    expr_ref true_expr(m.mk_true(), m);
    expr_ref false_expr(m.mk_false(), m);
    expr_ref f(array.mk_const_array(as, one), m);
    expr_ref binding(m.mk_app(pair.get(), f.get(), true_expr.get()), m);
    expr_ref b(m.mk_var(0, box), m);
    expr_ref unboxed(m.mk_app(fst.get(), b.get()), m);
    expr_ref selected(array.mk_select(unboxed, false_expr), m);
    expr_ref body(m.mk_eq(selected, zero), m);
    sort* dom = box;
    symbol name("b");
    quantifier_ref q(m.mk_forall(1, &dom, &name, body), m);
    expr_ref_vector bindings(m);
    bindings.push_back(binding);
    ptr_vector<func_decl> bases;
    bases.push_back(nullptr);
    instance_context ctx(m);
    model_instance_generator generator(ctx);
    generator(q, bindings, bases);
    ENSURE(ctx.instances.size() == 1);
    expr_ref constant(array.mk_const_array(as, zero), m);
    expr_ref expected(m.mk_app(pair.get(), constant.get(), true_expr.get()), m);
    ENSURE(ctx.instances[0].get(0) == expected);
}

static void check_array_instance_conversion() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);
    array_util array(m);
    instance_context ctx(m);
    model cex(m);
    sort* domains[2] = { m.mk_bool_sort(), arith.mk_int() };
    sort_ref as(array.mk_array_sort(2, domains, arith.mk_int()), m);
    func_decl_ref f(m.mk_func_decl(symbol("f"), 2, domains, arith.mk_int()), m);
    expr_ref zero(arith.mk_int(0), m);
    expr_ref one(arith.mk_int(1), m);
    expr_ref two(arith.mk_int(2), m);
    expr_ref b(m.mk_true(), m);
    expr* entry[2] = { b, one };
    func_interp* fi = alloc(func_interp, m, 2);
    fi->set_else(zero);
    fi->insert_entry(entry, two);
    cex.register_decl(f, fi);
    expr_ref base(m.mk_const("base", as), m);
    expr_ref constant(array.mk_const_array(as, zero), m);
    expr_ref auxiliary(m.mk_fresh_const("array", as, false), m);
    ctx.auxiliary.insert(to_app(auxiliary)->get_decl());
    ctx.mdl.register_decl(to_app(auxiliary)->get_decl(), constant);
    ctx.mdl.register_decl(to_app(base)->get_decl(), constant);
    model_instance_generator generator(ctx);
    func_decl* chosen = nullptr;
    expr_ref store = generator.mk_store_instance(f, cex, chosen);
    expr* args[4] = { base, b, one, two };
    expr_ref expected(array.mk_store(4, args), m);
    ENSURE(chosen == to_app(base)->get_decl());
    ENSURE(store == expected);
    expr_ref as_array(array.mk_as_array(f), m);
    expr_ref converted = generator.as_array_to_stores(as_array, cex);
    args[0] = constant;
    expected = array.mk_store(4, args);
    ENSURE(converted == expected);
    ENSURE(!has_free_vars(converted));
    ENSURE(is_well_sorted(m, converted));
    func_decl_ref wrap(m.mk_func_decl(symbol("wrap"), as, as), m);
    expr_ref nested(m.mk_app(wrap.get(), as_array.get()), m);
    converted = generator.as_array_to_stores(nested, cex);
    expected = m.mk_app(wrap.get(), expected.get());
    ENSURE(converted == expected);
    expr_ref variable(m.mk_var(1, arith.mk_int()), m);
    fi->set_else(variable);
    converted = generator.as_array_to_stores(as_array, cex);
    ENSURE(converted == as_array);
}

void tst_model_evaluator() {
    check_instance_provenance(true);
    check_instance_provenance(false);
    check_store_instance_base();
    check_boxed_array_instance();
    check_array_instance_conversion();
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
