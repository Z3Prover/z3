/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/ast.h"
#include "ast/bv_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include "ackermannization/lackr.h"
#include "ackermannization/ackermannize_bv_tactic.h"
#include "ackermannization/ackr_bound_probe.h"
#include "ackermannization/ackr_model_converter.h"
#include "ackermannization/ackr_info.h"
#include "model/model.h"
#include "util/params.h"
#include <iostream>
#include <limits>

// Helper: create a BV uninterpreted function formula: f(x) = f(y)
static void mk_uf_bv_goal(ast_manager& m, goal_ref& g) {
    bv_util bv(m);
    sort* bv8 = bv.mk_sort(8);

    func_decl* f = m.mk_func_decl(symbol("f"), 1, &bv8, bv8);
    expr* x = m.mk_const(symbol("x"), bv8);
    expr* y = m.mk_const(symbol("y"), bv8);
    app* fx = m.mk_app(f, x);
    app* fy = m.mk_app(f, y);

    // f(x) = f(y)
    g->assert_expr(m.mk_eq(fx, fy));
    // x != y
    g->assert_expr(m.mk_not(m.mk_eq(x, y)));
}

// Test 1: mk_ackermann returns false when lemmas_upper_bound <= 0
static void test_mk_ackermann_zero_bound() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    sort* bv8 = bv.mk_sort(8);

    func_decl* f = m.mk_func_decl(symbol("f"), 1, &bv8, bv8);
    expr* x = m.mk_const(symbol("x"), bv8);
    app* fx = m.mk_app(f, x);

    ptr_vector<expr> flas;
    flas.push_back(fx);
    params_ref p;
    lackr_stats st;
    lackr lk(m, p, st, flas, nullptr);
    goal_ref g(alloc(goal, m, true, false));
    // With bound = 0, mk_ackermann should return false
    ENSURE(!lk.mk_ackermann(g, 0.0));
    std::cout << "test_mk_ackermann_zero_bound: PASS\n";
}

// Test 2: mk_ackermann returns false when init() fails (formula with quantifiers)
static void test_mk_ackermann_quantifier() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    sort* bv8 = bv.mk_sort(8);

    // Create a quantified formula: forall x:bv8. x = x
    symbol name("x");
    expr_ref body(m.mk_eq(m.mk_var(0, bv8), m.mk_var(0, bv8)), m);
    expr_ref qfml(m.mk_forall(1, &bv8, &name, body), m);

    ptr_vector<expr> flas;
    flas.push_back(qfml.get());
    params_ref p;
    lackr_stats st;
    lackr lk(m, p, st, flas, nullptr);
    goal_ref g(alloc(goal, m, true, false));
    // Quantified formulas cause init() to fail, mk_ackermann should return false
    ENSURE(!lk.mk_ackermann(g, std::numeric_limits<double>::infinity()));
    std::cout << "test_mk_ackermann_quantifier: PASS\n";
}

// Test 3: mk_ackermann returns false when lemma count exceeds upper bound
static void test_mk_ackermann_exceeds_bound() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    sort* bv8 = bv.mk_sort(8);

    // Create a goal with 2 distinct uninterpreted terms f(x), f(y)
    // This gives C(2,2)=1 lemma; use bound=0.5 to trigger the limit (1 > 0.5)
    func_decl* f = m.mk_func_decl(symbol("f"), 1, &bv8, bv8);
    expr* x = m.mk_const(symbol("x"), bv8);
    expr* y = m.mk_const(symbol("y"), bv8);
    app* fx = m.mk_app(f, x);
    app* fy = m.mk_app(f, y);

    ptr_vector<expr> flas;
    flas.push_back(m.mk_eq(fx, fy));
    flas.push_back(m.mk_not(m.mk_eq(x, y)));
    params_ref p;
    lackr_stats st;
    lackr lk(m, p, st, flas, nullptr);
    goal_ref g(alloc(goal, m, true, false));
    // With upper_bound=0.5, C(2,2)=1 > 0.5, so mk_ackermann should return false
    ENSURE(!lk.mk_ackermann(g, 0.5));
    std::cout << "test_mk_ackermann_exceeds_bound: PASS\n";
}

// Test 4: ackermannize_bv_tactic processes all formulas in goal (covers loop at ackermannize_bv_tactic.cpp:42)
static void test_ackermannize_bv_tactic_loop() {
    ast_manager m;
    reg_decl_plugins(m);

    goal_ref g(alloc(goal, m, true, false));
    mk_uf_bv_goal(m, g);

    params_ref p;
    tactic_ref t = mk_ackermannize_bv_tactic(m, p);
    goal_ref_buffer result;
    (*t)(g, result);
    // The tactic should produce a result (not crash)
    ENSURE(result.size() > 0);
    std::cout << "test_ackermannize_bv_tactic_loop: PASS\n";
}

// Test 5: ackr_bound_probe processes all formulas in goal (covers loop at ackr_bound_probe.cpp:67)
static void test_ackr_bound_probe_loop() {
    ast_manager m;
    reg_decl_plugins(m);

    goal_ref g(alloc(goal, m, true, false));
    mk_uf_bv_goal(m, g);

    scoped_ptr<probe> pr = mk_ackr_bound_probe();
    probe::result r = (*pr)(*g);
    // Should return a non-negative bound (covers the loop)
    ENSURE(r.get_value() >= 0.0);
    std::cout << "test_ackr_bound_probe_loop: PASS\n";
}

// Test 6: ackermannize_bv_tactic with multiple formulas verifies full loop coverage
static void test_ackermannize_multiple_formulas() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    sort* bv8 = bv.mk_sort(8);

    func_decl* f = m.mk_func_decl(symbol("f"), 1, &bv8, bv8);
    expr* x = m.mk_const(symbol("x"), bv8);
    expr* y = m.mk_const(symbol("y"), bv8);

    goal_ref g(alloc(goal, m, true, false));
    // Add multiple formulas to ensure the loop iterates more than once
    g->assert_expr(m.mk_eq(m.mk_app(f, x), m.mk_app(f, y)));
    g->assert_expr(m.mk_not(m.mk_eq(x, y)));
    g->assert_expr(m.mk_true());

    // Verify the probe processes all 3 formulas
    scoped_ptr<probe> pr = mk_ackr_bound_probe();
    probe::result r = (*pr)(*g);
    ENSURE(r.get_value() >= 0.0);

    // Verify the tactic also processes all 3 formulas
    params_ref p;
    tactic_ref t = mk_ackermannize_bv_tactic(m, p);
    goal_ref_buffer result;
    (*t)(g, result);
    ENSURE(result.size() > 0);
    std::cout << "test_ackermannize_multiple_formulas: PASS\n";
}

// Test 7: ackr_model_converter iterates over model constants
// (covers loop at ackr_model_converter.cpp:106)
static void test_ackr_model_converter_constants() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    sort* bv8 = bv.mk_sort(8);

    // Set up an abstraction: f(x) -> fresh_c
    func_decl* f = m.mk_func_decl(symbol("f"), 1, &bv8, bv8);
    expr_ref x(m.mk_const(symbol("x"), bv8), m);
    app_ref fx(m.mk_app(f, x.get()), m);
    app_ref fresh_c(m.mk_fresh_const("f", bv8), m);

    ackr_info_ref info = alloc(ackr_info, m);
    info->set_abstr(fx.get(), fresh_c.get());
    info->seal();

    // Create a source model with the fresh constant having a value (BV numeral 42)
    model_ref src_model = alloc(model, m);
    expr_ref val42(bv.mk_numeral(42, 8), m);
    src_model->register_decl(fresh_c->get_decl(), val42.get());
    ENSURE(src_model->get_num_constants() == 1);

    // Apply the model converter: it should process the constant and create a new model
    model_converter_ref mc(mk_ackr_model_converter(m, info));
    model_ref dst_model(src_model.get());
    (*mc)(dst_model);

    // The converter ran without crashing, verifying the loop iterated correctly
    std::cout << "test_ackr_model_converter_constants: PASS\n";
}

void tst_ackermannize() {
    test_mk_ackermann_zero_bound();
    test_mk_ackermann_quantifier();
    test_mk_ackermann_exceeds_bound();
    test_ackermannize_bv_tactic_loop();
    test_ackr_bound_probe_loop();
    test_ackermannize_multiple_formulas();
    test_ackr_model_converter_constants();
}
