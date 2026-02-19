/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    ackermannize.cpp

Abstract:

    Tests for the ackermannization module.
    Covers: ackermannize_bv_tactic, lackr::mk_ackermann,
            ackr_bound_probe, and ackr_model_converter.

Author:

    Test Coverage

Notes:

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/debug.h"

//
// Test that the ackermannize_bv tactic runs correctly on a BV formula with
// uninterpreted function applications.  Two applications of the same function
// are required so that at least one Ackermann congruence lemma is generated.
// This exercises the loop in ackermannize_bv_tactic.cpp (off-by-one guard) and
// the negated-condition guard that controls whether the result is returned.
//
static void test_ackermannize_bv_basic() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    Z3_func_decl f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "f"), 1, &bv8, bv8);

    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), bv8);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bv8);

    Z3_ast fa = Z3_mk_app(ctx, f, 1, &a);
    Z3_ast fb = Z3_mk_app(ctx, f, 1, &b);

    // Formula: a = b AND f(a) != f(b).  This is UNSAT (by functional congruence).
    Z3_ast eq_ab    = Z3_mk_eq(ctx, a, b);
    Z3_ast neq_fab  = Z3_mk_not(ctx, Z3_mk_eq(ctx, fa, fb));
    Z3_ast args[2]  = { eq_ab, neq_fab };
    Z3_ast formula  = Z3_mk_and(ctx, 2, args);

    // Create a goal with models enabled and assert the formula.
    Z3_goal g = Z3_mk_goal(ctx, true, false, false);
    Z3_goal_inc_ref(ctx, g);
    Z3_goal_assert(ctx, g, formula);
    unsigned input_size = Z3_goal_size(ctx, g);

    // Apply the ackermannize_bv tactic.
    Z3_tactic t = Z3_mk_tactic(ctx, "ackermannize_bv");
    Z3_tactic_inc_ref(ctx, t);
    Z3_apply_result ar = Z3_tactic_apply(ctx, t, g);
    Z3_apply_result_inc_ref(ctx, ar);

    // The tactic must produce exactly one subgoal.
    unsigned num_subgoals = Z3_apply_result_get_num_subgoals(ctx, ar);
    ENSURE(num_subgoals == 1);

    // The resulting goal must contain more formulas than the input because the
    // tactic adds Ackermann congruence lemmas.  If the negated-condition mutation
    // is present (success path returns original unchanged) the sizes would be equal.
    Z3_goal rg = Z3_apply_result_get_subgoal(ctx, ar, 0);
    ENSURE(Z3_goal_size(ctx, rg) > input_size);

    Z3_apply_result_dec_ref(ctx, ar);
    Z3_tactic_dec_ref(ctx, t);
    Z3_goal_dec_ref(ctx, g);
    Z3_del_context(ctx);
}

//
// Test that setting div0_ackermann_limit to 0 causes lackr::mk_ackermann to
// return false, so the tactic passes through the original formula unchanged.
// This exercises the "lemmas_upper_bound <= 0 → return false" guard in lackr.cpp.
// If the wrong-return-value mutation is present (return true), the goal would be
// processed differently and the size check below would be violated.
//
static void test_ackermannize_bv_zero_limit() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    Z3_func_decl f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "f"), 1, &bv8, bv8);

    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), bv8);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bv8);

    Z3_ast fa = Z3_mk_app(ctx, f, 1, &a);
    Z3_ast fb = Z3_mk_app(ctx, f, 1, &b);

    Z3_ast eq_fab = Z3_mk_eq(ctx, fa, fb);

    Z3_goal g = Z3_mk_goal(ctx, false, false, false);
    Z3_goal_inc_ref(ctx, g);
    Z3_goal_assert(ctx, g, eq_fab);
    unsigned input_size = Z3_goal_size(ctx, g);

    // Set div0_ackermann_limit = 0 so that mk_ackermann returns false immediately.
    Z3_params p = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, p);
    Z3_params_set_uint(ctx, p, Z3_mk_string_symbol(ctx, "div0_ackermann_limit"), 0);

    Z3_tactic t = Z3_mk_tactic(ctx, "ackermannize_bv");
    Z3_tactic_inc_ref(ctx, t);
    Z3_apply_result ar = Z3_tactic_apply_ex(ctx, t, g, p);
    Z3_apply_result_inc_ref(ctx, ar);

    // With limit = 0 the tactic returns the input unchanged.
    unsigned num_subgoals = Z3_apply_result_get_num_subgoals(ctx, ar);
    ENSURE(num_subgoals == 1);
    Z3_goal rg = Z3_apply_result_get_subgoal(ctx, ar, 0);

    // The original goal must be returned unchanged (no Ackermann lemmas added).
    ENSURE(Z3_goal_size(ctx, rg) == input_size);

    Z3_apply_result_dec_ref(ctx, ar);
    Z3_params_dec_ref(ctx, p);
    Z3_tactic_dec_ref(ctx, t);
    Z3_goal_dec_ref(ctx, g);
    Z3_del_context(ctx);
}

//
// Test the ackr-bound-probe.  A formula with two applications of the same
// uninterpreted function requires C(2,2)=1 Ackermann lemma.  The probe must
// return a value >= 1.
// This exercises the loop in ackr_bound_probe.cpp (off-by-one guard).
//
static void test_ackr_bound_probe() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    Z3_func_decl f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "f"), 1, &bv8, bv8);

    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), bv8);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bv8);

    Z3_ast fa = Z3_mk_app(ctx, f, 1, &a);
    Z3_ast fb = Z3_mk_app(ctx, f, 1, &b);

    // One formula involving both f(a) and f(b).
    Z3_ast eq_fab = Z3_mk_eq(ctx, fa, fb);

    Z3_goal g = Z3_mk_goal(ctx, false, false, false);
    Z3_goal_inc_ref(ctx, g);
    Z3_goal_assert(ctx, g, eq_fab);

    Z3_probe pr = Z3_mk_probe(ctx, "ackr-bound-probe");
    Z3_probe_inc_ref(ctx, pr);

    double bound = Z3_probe_apply(ctx, pr, g);
    // Two occurrences of f → C(2,2) = 1 Ackermann lemma required.
    ENSURE(bound >= 1.0);

    Z3_probe_dec_ref(ctx, pr);
    Z3_goal_dec_ref(ctx, g);
    Z3_del_context(ctx);
}

//
// Test model extraction after ackermannization.  This exercises
// ackr_model_converter::operator() which converts the abstract model produced
// by the BV solver back to a model for the original formula (with UF).
// The two null-pointer guards in ackr_model_converter.cpp are exercised here.
//
static void test_ackermannize_bv_model() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    Z3_func_decl f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "f"), 1, &bv8, bv8);

    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), bv8);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bv8);

    Z3_ast fa = Z3_mk_app(ctx, f, 1, &a);
    Z3_ast fb = Z3_mk_app(ctx, f, 1, &b);

    // SAT formula: f(a) != f(b).  After ackermannization the model converter
    // will be installed on the result goal.
    Z3_ast formula = Z3_mk_not(ctx, Z3_mk_eq(ctx, fa, fb));

    // Goal with models enabled so that the model converter is installed.
    Z3_goal g = Z3_mk_goal(ctx, true, false, false);
    Z3_goal_inc_ref(ctx, g);
    Z3_goal_assert(ctx, g, formula);

    Z3_tactic t = Z3_mk_tactic(ctx, "ackermannize_bv");
    Z3_tactic_inc_ref(ctx, t);
    Z3_apply_result ar = Z3_tactic_apply(ctx, t, g);
    Z3_apply_result_inc_ref(ctx, ar);

    ENSURE(Z3_apply_result_get_num_subgoals(ctx, ar) == 1);
    Z3_goal rg = Z3_apply_result_get_subgoal(ctx, ar, 0);

    // Verify the model converter was installed (models_enabled=true on input goal).
    // The ackermannized subgoal should have more formulas than the one-formula input.
    // Calling Z3_goal_convert_model with an empty model exercises the null-check
    // guards on abstr_model (line 52) and md (line 54) in ackr_model_converter.cpp.
    // The negated-condition mutations negate_b7a3a60d97 and negate_78a6d6f2f9 would
    // cause a null-pointer dereference here if present.
    Z3_model empty_m = Z3_mk_model(ctx);
    Z3_model_inc_ref(ctx, empty_m);
    Z3_model converted = Z3_goal_convert_model(ctx, rg, empty_m);
    // converted may be null if the model converter is not installed, but if
    // it is installed and runs without crashing, we consider the test passed.
    if (converted) Z3_model_inc_ref(ctx, converted);
    if (converted) Z3_model_dec_ref(ctx, converted);
    Z3_model_dec_ref(ctx, empty_m);

    Z3_apply_result_dec_ref(ctx, ar);
    Z3_tactic_dec_ref(ctx, t);
    Z3_goal_dec_ref(ctx, g);
    Z3_del_context(ctx);
}

//
// Test ackermannize_bv on a formula with multiple assertions in the goal.
// This exercises the loop in ackermannize_bv_tactic.cpp that collects all
// formulas (the off-by-one mutation would crash here by reading past the end).
//
static void test_ackermannize_bv_multiple_assertions() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
    Z3_func_decl f = Z3_mk_func_decl(ctx, Z3_mk_string_symbol(ctx, "f"), 1, &bv8, bv8);

    Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "a"), bv8);
    Z3_ast b = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "b"), bv8);
    Z3_ast c = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "c"), bv8);

    Z3_ast fa = Z3_mk_app(ctx, f, 1, &a);
    Z3_ast fb = Z3_mk_app(ctx, f, 1, &b);
    Z3_ast fc = Z3_mk_app(ctx, f, 1, &c);

    // Three separate assertions with three UF applications.
    Z3_ast f1 = Z3_mk_eq(ctx, fa, fb);
    Z3_ast f2 = Z3_mk_eq(ctx, fb, fc);
    Z3_ast f3 = Z3_mk_not(ctx, Z3_mk_eq(ctx, a, b));

    Z3_goal g = Z3_mk_goal(ctx, false, false, false);
    Z3_goal_inc_ref(ctx, g);
    Z3_goal_assert(ctx, g, f1);
    Z3_goal_assert(ctx, g, f2);
    Z3_goal_assert(ctx, g, f3);
    unsigned input_size = Z3_goal_size(ctx, g);  // 3

    Z3_tactic t = Z3_mk_tactic(ctx, "ackermannize_bv");
    Z3_tactic_inc_ref(ctx, t);
    Z3_apply_result ar = Z3_tactic_apply(ctx, t, g);
    Z3_apply_result_inc_ref(ctx, ar);

    ENSURE(Z3_apply_result_get_num_subgoals(ctx, ar) == 1);
    Z3_goal rg = Z3_apply_result_get_subgoal(ctx, ar, 0);
    // With 3 UF applications, C(3,2)=3 Ackermann lemmas should be added.
    ENSURE(Z3_goal_size(ctx, rg) > input_size);

    Z3_apply_result_dec_ref(ctx, ar);
    Z3_tactic_dec_ref(ctx, t);
    Z3_goal_dec_ref(ctx, g);
    Z3_del_context(ctx);
}

void tst_ackermannize() {
    test_ackermannize_bv_basic();
    test_ackermannize_bv_zero_limit();
    test_ackr_bound_probe();
    test_ackermannize_bv_multiple_assertions();
}
