/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_bounds.cpp

Abstract:

    Tests for the optimization API's lower and upper bounds, including
    exact algebraic values, rational values, infinity, and epsilon.
    Check both expression results and the three-element coefficient vector
    [a, b, c], which represents a * infinity + b + c * epsilon.

--*/
#include "api/z3.h"
#include "ast/reg_decl_plugins.h"
#include "opt/opt_context.h"
#include "opt/opt_geometric.h"
#include "util/debug.h"
#include <climits>
#include <cstring>
#include <initializer_list>
#include <iostream>

namespace {

// Solve two independent maximization problems over real x and y, both under
// the constraints x <= 3 and y <= 7: first maximize x, then maximize y.
// The maxima are attained at x = 3 and y = 7; neither variable constrains
// the other, so both expected answers follow directly from the upper bounds.
//
// For each call, check that the returned maximize_result accepts the bound
// (bound_valid), reports an accepted hint (hint_status == l_true), and holds
// the exact expected value. Also check that the solver's saved objective
// value agrees and that a blocker was produced.
//
// Keep the first result while making the second call, then check its value
// and status again. This checks the new per-call ownership: maximizing y
// must not replace the retained result for x with the latest hint, 7.
static void tst_maximize_result() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    params_ref p;
    p.set_uint("arith.solver", 6);
    generic_model_converter fm(m, "maximize result");
    opt::opt_solver s(m, p, fm);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref y(m.mk_const(symbol("y"), a.mk_real()), m);
    s.assert_expr(a.mk_le(x, a.mk_numeral(rational(3), false)));
    s.assert_expr(a.mk_le(y, a.mk_numeral(rational(7), false)));
    ENSURE(s.check_sat(0, nullptr) == l_true);
    s.add_objective(to_app(x));
    s.add_objective(to_app(y));
    expr_ref blocker(m);
    auto first = s.maximize_objective(0, blocker);
    ENSURE(first.bound_valid && first.hint_status == l_true);
    ENSURE(first.hint == opt::inf_eps(rational(3)));
    ENSURE(blocker);
    ENSURE(s.saved_objective_value(0) == first.hint);
    ENSURE(s.check_sat(0, nullptr) == l_true);
    auto second = s.maximize_objective(1, blocker);
    ENSURE(second.bound_valid && second.hint_status == l_true);
    ENSURE(second.hint == opt::inf_eps(rational(7)));
    ENSURE(blocker);
    ENSURE(s.saved_objective_value(1) == second.hint);
    // A later objective must not overwrite the earlier call's result.
    ENSURE(first.bound_valid && first.hint_status == l_true);
    ENSURE(first.hint == opt::inf_eps(rational(3)));
}

static void tst_geometric_step() {
    opt::geometric_step step;
    ENSURE(step.value() == rational(1));

    // The first doubling takes two eligible rounds, the next takes three,
    // then four, then five. A full reset must restart that same sequence.
    for (unsigned repeat = 0; repeat < 2; ++repeat) {
        for (unsigned expected : {1u, 2u, 2u, 2u, 4u, 4u, 4u, 4u, 8u, 8u, 8u, 8u, 8u, 16u}) {
            step.update(true);
            ENSURE(step.value() == rational(expected));
        }
        step.reset();
        ENSURE(step.value() == rational(1));
    }

    // Turning growth off must not erase a round already counted toward doubling.
    step.update(true);
    step.update(false);
    ENSURE(step.value() == rational(1));
    step.update(true);
    ENSURE(step.value() == rational(2));

    // Keep the count of earlier doublings too. After growth is turned back on,
    // the next doubling still needs three rounds in total, then four.
    step.update(true);
    step.update(false);
    step.update(false);
    ENSURE(step.value() == rational(1));
    for (unsigned expected : {1u, 2u, 2u, 2u, 2u, 4u}) {
        step.update(true);
        ENSURE(step.value() == rational(expected));
    }

    // Unlike turning growth off, a failed larger trial clears both counters.
    step.update(true);
    step.reset();
    step.reset();
    step.update(true);
    ENSURE(step.value() == rational(1));
    step.update(true);
    ENSURE(step.value() == rational(2));

    // The step remains an exact rational even after it outgrows a machine word.
    step.reset();
    rational expected(1);
    for (unsigned doubles = 0; doubles < 70; ++doubles) {
        for (unsigned round = 0; round < doubles + 1; ++round) {
            step.update(true);
            ENSURE(step.value() == expected);
        }
        step.update(true);
        expected *= rational(2);
        ENSURE(step.value() == expected);
    }
    step.update(false);
    ENSURE(step.value() == rational(1));
    step.reset();
    step.update(true);
    ENSURE(step.value() == rational(1));
    step.update(true);
    ENSURE(step.value() == rational(2));
}

// Own a separate C API context for each test and pin the optimizer settings.
struct opt_fixture {
    Z3_context ctx;
    Z3_optimize opt;

    opt_fixture(char const* priority = "lex", unsigned rounds = 64, bool nlsat = true,
                unsigned supremum_rlimit = 100000, char const* engine = "basic") {
        Z3_config cfg = Z3_mk_config();
        ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        Z3_set_error_handler(ctx, [](Z3_context, Z3_error_code) {});
        opt = Z3_mk_optimize(ctx);
        // Keep the optimizer alive for this fixture; the destructor releases it.
        Z3_optimize_inc_ref(ctx, opt);
        Z3_params p = Z3_mk_params(ctx);
        // Parameter sets need reference counting even with Z3_mk_context.
        // Hold p while filling it and applying its settings to the optimizer.
        Z3_params_inc_ref(ctx, p);
        Z3_params_set_symbol(ctx, p, symbol("priority"), symbol(priority));
        Z3_params_set_symbol(ctx, p, symbol("optsmt_engine"), symbol(engine));
        Z3_params_set_bool(ctx, p, symbol("optsmt_nlsat"), nlsat);
        Z3_params_set_uint(ctx, p, symbol("optsmt_bisect_rounds"), rounds);
        // Bound the extra finite-limit proof independently of the overall work limit.
        Z3_params_set_uint(ctx, p, symbol("optsmt_nlsat_supremum_rlimit"), supremum_rlimit);
        Z3_params_set_uint(ctx, p, symbol("smt.arith.solver"), std::strcmp(engine, "symba") == 0 ? 5 : 6);
        // Limit solver work without counting time spent paused in the debugger.
        Z3_params_set_uint(ctx, p, symbol("timeout"), 0);
        Z3_params_set_uint(ctx, p, symbol("rlimit"), 1000000);
        // The optimizer copies the settings; it does not take ownership of p.
        Z3_optimize_set_params(ctx, opt, p);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
        // Release our reference to the temporary set; opt keeps the copied settings.
        Z3_params_dec_ref(ctx, p);
    }

    ~opt_fixture() {
        // Balance the constructor's reference before deleting the context.
        Z3_optimize_dec_ref(ctx, opt);
        Z3_del_context(ctx);
    }

    opt_fixture(opt_fixture const&) = delete;
    opt_fixture& operator=(opt_fixture const&) = delete;

    Z3_symbol symbol(char const* name) { return Z3_mk_string_symbol(ctx, name); }
    Z3_ast real(char const* name) { return Z3_mk_const(ctx, symbol(name), Z3_mk_real_sort(ctx)); }
    Z3_ast num(int n, int d = 1) { return Z3_mk_real(ctx, n, d); }
    Z3_ast sum(Z3_ast a, Z3_ast b) {
        Z3_ast args[] = {a, b};
        return Z3_mk_add(ctx, 2, args);
    }
    Z3_ast sub(Z3_ast a, Z3_ast b) {
        Z3_ast args[] = {a, b};
        return Z3_mk_sub(ctx, 2, args);
    }
    Z3_ast square(Z3_ast a) {
        Z3_ast args[] = {a, a};
        return Z3_mk_mul(ctx, 2, args);
    }
    void add(Z3_ast a) {
        Z3_optimize_assert(ctx, opt, a);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
    }
    unsigned objective(Z3_ast a, bool maximize = true) {
        // Register an objective; this does not run the optimizer.
        unsigned h = maximize ? Z3_optimize_maximize(ctx, opt, a) : Z3_optimize_minimize(ctx, opt, a);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
        return h;
    }
    Z3_lbool check() {
        // This is the solving call; objective registration and bound getters do not solve.
        // In box mode, subsequent calls enumerate the already optimized models.
        Z3_lbool r = Z3_optimize_check(ctx, opt, 0, nullptr);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
        return r;
    }
};

// Construct sqrt(2), or another positive root of 2, independently of Optimize.
static Z3_ast root(opt_fixture& f, unsigned degree = 2) {
    Z3_ast r = Z3_algebraic_root(f.ctx, f.num(2), degree);
    ENSURE(r && Z3_is_algebraic_number(f.ctx, r));
    ENSURE(Z3_algebraic_is_pos(f.ctx, r));
    ENSURE(Z3_algebraic_eq(f.ctx, Z3_algebraic_power(f.ctx, r, degree), f.num(2)));
    return r;
}

// Build offset +/- sqrt(2) without introducing a rational approximation.
static Z3_ast shifted_root(opt_fixture& f, Z3_ast offset, bool positive) {
    return positive ? Z3_algebraic_add(f.ctx, offset, root(f)) :
                      Z3_algebraic_sub(f.ctx, offset, root(f));
}

// Check exact equality and whether each value is rational or irrational algebraic.
static void ensure_value(opt_fixture& f, Z3_ast actual, Z3_ast expected) {
    ENSURE(actual && Z3_algebraic_is_value(f.ctx, actual));
    ENSURE(Z3_is_algebraic_number(f.ctx, actual) == Z3_is_algebraic_number(f.ctx, expected));
    ENSURE(Z3_algebraic_eq(f.ctx, actual, expected));
}

// Check the numeral's sort independently of its value.
static void ensure_sort(opt_fixture& f, Z3_ast a, Z3_sort_kind kind) {
    ENSURE(Z3_get_sort_kind(f.ctx, Z3_get_sort(f.ctx, a)) == kind);
}

// Read a bound from the latest optimization result; this call does not solve.
static Z3_ast scalar_bound(opt_fixture& f, unsigned h, bool lower) {
    Z3_ast r = lower ? Z3_optimize_get_lower(f.ctx, f.opt, h) :
                       Z3_optimize_get_upper(f.ctx, f.opt, h);
    ENSURE(r && Z3_get_error_code(f.ctx) == Z3_OK);
    return r;
}

// Check the [infinity, finite value, epsilon] coefficients and their numeral sorts.
static void ensure_vector(opt_fixture& f, unsigned h, bool lower, int infinity,
                          Z3_ast finite, int epsilon, Z3_sort_kind finite_sort) {
    Z3_ast_vector v = lower ? Z3_optimize_get_lower_as_vector(f.ctx, f.opt, h) :
                              Z3_optimize_get_upper_as_vector(f.ctx, f.opt, h);
    ENSURE(v && Z3_get_error_code(f.ctx) == Z3_OK);
    Z3_ast_vector_inc_ref(f.ctx, v);
    ENSURE(Z3_ast_vector_size(f.ctx, v) == 3);
    ensure_value(f, Z3_ast_vector_get(f.ctx, v, 0), f.num(infinity));
    ensure_value(f, Z3_ast_vector_get(f.ctx, v, 1), finite);
    ensure_value(f, Z3_ast_vector_get(f.ctx, v, 2), f.num(epsilon));
    ensure_sort(f, Z3_ast_vector_get(f.ctx, v, 0), Z3_INT_SORT);
    ensure_sort(f, Z3_ast_vector_get(f.ctx, v, 1), finite_sort);
    ensure_sort(f, Z3_ast_vector_get(f.ctx, v, 2), Z3_INT_SORT);
    Z3_ast_vector_dec_ref(f.ctx, v);
}

// All four getters must agree on an attained finite optimum.
static void ensure_finite_bounds(opt_fixture& f, unsigned h, Z3_ast expected,
                                 Z3_sort_kind kind = Z3_REAL_SORT) {
    for (bool lower : {true, false}) {
        Z3_ast b = scalar_bound(f, h, lower);
        ensure_value(f, b, expected);
        ensure_sort(f, b, kind);
        ensure_vector(f, h, lower, 0, expected, 0, kind);
    }
}

// An open scalar bound is finite +/- epsilon, not an algebraic numeral.
// Check its exact finite part and epsilon sign in all four getters.
static void ensure_open_bounds(opt_fixture& f, unsigned h, Z3_ast finite, int epsilon,
                               Z3_sort_kind finite_sort = Z3_REAL_SORT) {
    ENSURE(epsilon == -1 || epsilon == 1);
    Z3_ast ep = f.real("epsilon");
    Z3_ast expected = epsilon < 0 ? f.sub(finite, ep) : f.sum(finite, ep);
    for (bool lower : {true, false}) {
        Z3_ast b = scalar_bound(f, h, lower);
        ENSURE(!Z3_algebraic_is_value(f.ctx, b));
        ensure_sort(f, b, Z3_REAL_SORT);
        Z3_ast same = Z3_simplify(f.ctx, Z3_mk_eq(f.ctx, b, expected));
        ENSURE(Z3_get_bool_value(f.ctx, same) == Z3_L_TRUE);
        ensure_vector(f, h, lower, 0, finite, epsilon, finite_sort);
    }
}

// Check that the witness actually attains the independently computed optimum.
static void ensure_model_value(opt_fixture& f, Z3_ast objective, Z3_ast expected) {
    Z3_model m = Z3_optimize_get_model(f.ctx, f.opt);
    ENSURE(m);
    Z3_model_inc_ref(f.ctx, m);
    Z3_ast value = nullptr;
    ENSURE(Z3_model_eval(f.ctx, m, objective, true, &value));
    ensure_value(f, value, expected);
    Z3_model_dec_ref(f.ctx, m);
}

// A model for an open optimum must satisfy every hard assertion and remain
// strictly on the feasible side of the limit, rather than attain that limit.
static void ensure_open_model(opt_fixture& f, Z3_ast objective, Z3_ast limit, bool maximize) {
    Z3_model m = Z3_optimize_get_model(f.ctx, f.opt);
    ENSURE(m);
    Z3_model_inc_ref(f.ctx, m);
    Z3_ast_vector hard = Z3_optimize_get_assertions(f.ctx, f.opt);
    ENSURE(hard);
    Z3_ast_vector_inc_ref(f.ctx, hard);
    Z3_ast value = nullptr;
    for (unsigned i = 0; i < Z3_ast_vector_size(f.ctx, hard); ++i) {
        ENSURE(Z3_model_eval(f.ctx, m, Z3_ast_vector_get(f.ctx, hard, i), true, &value));
        ENSURE(Z3_get_bool_value(f.ctx, value) == Z3_L_TRUE);
    }
    ENSURE(Z3_model_eval(f.ctx, m, objective, true, &value));
    ENSURE(Z3_algebraic_is_value(f.ctx, value));
    ENSURE(maximize ? Z3_algebraic_lt(f.ctx, value, limit) : Z3_algebraic_gt(f.ctx, value, limit));
    Z3_ast_vector_dec_ref(f.ctx, hard);
    Z3_model_dec_ref(f.ctx, m);
}

// Maximize and minimize offset +/- x over x^2 <= 2. All four bound getters
// and the witness must give the corresponding exact shifted root.
static void tst_signed_offsets() {
    struct objective_case { int numerator, denominator; bool negate; };
    // x - 3/2 has a negative maximum as well as a negative minimum.
    objective_case const cases[] = {{0, 1, false}, {3, 1, false}, {3, 1, true}, {-3, 2, false}};
    for (auto const& t : cases) {
        for (bool maximize : {true, false}) {
            opt_fixture f;
            Z3_ast x = f.real("x");
            f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
            Z3_ast offset = f.num(t.numerator, t.denominator);
            Z3_ast objective = t.negate ? f.sub(offset, x) : f.sum(x, offset);
            unsigned h = f.objective(objective, maximize);
            // Run optimization for this objective, sign, and offset.
            ENSURE(f.check() == Z3_L_TRUE);
            // The shifted root is checked algebraically, not through a rounded display.
            Z3_ast expected = shifted_root(f, offset, maximize);
            ensure_finite_bounds(f, h, expected);
            ensure_model_value(f, objective, expected);
        }
    }
}

// Exercise both signs of sqrt(2) from inside and outside the parabola,
// followed by integral finite limits 2, -2, and 0 with Int vector entries.
static void tst_open_bounds() {
    for (bool outside : {false, true}) {
        for (bool maximize : {true, false}) {
            opt_fixture f("lex", 8);
            Z3_ast x = f.real("x");
            f.add(outside ? Z3_mk_gt(f.ctx, f.square(x), f.num(2)) :
                            Z3_mk_lt(f.ctx, f.square(x), f.num(2)));
            if (outside)
                f.add(maximize ? Z3_mk_lt(f.ctx, x, f.num(0)) : Z3_mk_gt(f.ctx, x, f.num(0)));
            unsigned h = f.objective(x, maximize);
            // Optimize a single open objective; its internal commitment must be skipped.
            ENSURE(f.check() == Z3_L_TRUE);
            Z3_ast limit = shifted_root(f, f.num(0), maximize != outside);
            ensure_open_bounds(f, h, limit, maximize ? -1 : 1);
            ensure_open_model(f, x, limit, maximize);
        }
    }
    for (int limit : {2, -2, 0}) {
        opt_fixture f("lex", 8);
        Z3_ast x = f.real("x");
        if (limit > 0) {
            // A disconnected feasible set still approaches 2 from below.
            f.add(Z3_mk_lt(f.ctx, f.square(x), f.num(4)));
            f.add(Z3_mk_ge(f.ctx, f.square(f.sub(x, f.num(1))), f.num(1, 4)));
        }
        else {
            f.add(Z3_mk_gt(f.ctx, f.square(x), f.num(limit * limit)));
            f.add(Z3_mk_lt(f.ctx, x, f.num(0)));
        }
        unsigned h = f.objective(x);
        // Optimize the nonlinear problem with a rational, unattained finite limit.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_open_bounds(f, h, f.num(limit), -1, Z3_INT_SORT);
        ensure_open_model(f, x, f.num(limit), true);
    }
}

// Cover shifted/scaled limits, a cubic root, a coupled disk objective, and
// a quadratic infimum whose quantified certificate needs a larger budget.
static void tst_open_polynomial_objectives() {
    struct objective_case { int scale, numerator, denominator; };
    objective_case const cases[] = {{1, 3, 1}, {2, 3, 1}, {-1, 3, 1}, {1, -3, 2}};
    for (auto const& t : cases) {
        for (bool maximize : {true, false}) {
            opt_fixture f("lex", 8);
            Z3_ast x = f.real("x");
            f.add(Z3_mk_lt(f.ctx, f.square(x), f.num(2)));
            Z3_ast offset = f.num(t.numerator, t.denominator);
            Z3_ast factors[] = {f.num(t.scale), x};
            Z3_ast objective = f.sum(Z3_mk_mul(f.ctx, 2, factors), offset);
            unsigned h = f.objective(objective, maximize);
            // Optimize each sign, scale, and offset without rounding the finite part.
            ENSURE(f.check() == Z3_L_TRUE);
            Z3_ast radius = Z3_algebraic_mul(f.ctx, f.num(t.scale < 0 ? -t.scale : t.scale), root(f));
            Z3_ast limit = maximize ? Z3_algebraic_add(f.ctx, offset, radius) :
                                      Z3_algebraic_sub(f.ctx, offset, radius);
            ensure_open_bounds(f, h, limit, maximize ? -1 : 1);
            ensure_open_model(f, objective, limit, maximize);
        }
    }
    {
        opt_fixture f("lex", 8);
        Z3_ast x = f.real("x");
        Z3_ast factors[] = {x, x, x};
        f.add(Z3_mk_lt(f.ctx, Z3_mk_mul(f.ctx, 3, factors), f.num(2)));
        unsigned h = f.objective(x);
        // Optimize x^3 < 2 to obtain cubert(2) - epsilon.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_open_bounds(f, h, root(f, 3), -1);
        ensure_open_model(f, x, root(f, 3), true);
    }
    {
        opt_fixture f("lex", 8);
        Z3_ast x = f.real("x"), y = f.real("y");
        f.add(Z3_mk_lt(f.ctx, f.sum(f.square(x), f.square(y)), f.num(1)));
        Z3_ast objective = f.sum(x, y);
        unsigned h = f.objective(objective);
        // Optimize over the open unit disk; the limit of x+y is sqrt(2).
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_open_bounds(f, h, root(f), -1);
        ensure_open_model(f, objective, root(f), true);
    }
    {
        opt_fixture f("lex", 8, true, 1000000);
        Z3_ast x = f.real("x"), y = f.real("y");
        f.add(Z3_mk_gt(f.ctx, f.sum(x, y), f.num(1)));
        Z3_ast objective = f.sum(f.square(x), f.square(y));
        unsigned h = f.objective(objective, false);
        // Minimize x^2+y^2 with the larger private proof budget to certify 1/2+epsilon.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_open_bounds(f, h, f.num(1, 2), 1);
        ensure_open_model(f, objective, f.num(1, 2), false);
    }
}

// A fixed soft cost precedes max(x), min(x+3), testing handle remapping.
// Lex fixes x at sqrt(2); box minimizes x+3 independently to 3-sqrt(2).
static void tst_multiobjective(bool box) {
    opt_fixture f(box ? "box" : "lex");
    Z3_ast x = f.real("x");
    f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
    Z3_ast p = Z3_mk_const(f.ctx, f.symbol("p"), Z3_mk_bool_sort(f.ctx));
    f.add(Z3_mk_not(f.ctx, p));
    // A soft objective makes public handles differ from the optsmt indices.
    unsigned soft = Z3_optimize_assert_soft(f.ctx, f.opt, p, "5/2", f.symbol("cost"));
    unsigned hi = f.objective(x);
    Z3_ast shifted = f.sum(x, f.num(3));
    unsigned lo = f.objective(shifted, false);
    ENSURE(soft == 0 && hi == 1 && lo == 2);
    // Optimize the full objective list under the selected priority.
    ENSURE(f.check() == Z3_L_TRUE);
    Z3_ast high_value = root(f);
    Z3_ast low_value = shifted_root(f, f.num(3), !box);
    auto ensure_bounds = [&]() {
        ensure_finite_bounds(f, soft, f.num(5, 2));
        ensure_finite_bounds(f, hi, high_value);
        ensure_finite_bounds(f, lo, low_value);
    };
    ensure_bounds();
    if (box) {
        // These checks select cached box models rather than optimizing again.
        // Selecting a model must not overwrite another objective's value.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_model_value(f, x, high_value);
        ensure_bounds();
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_model_value(f, shifted, low_value);
        ensure_bounds();
        ENSURE(f.check() == Z3_L_FALSE);
    }
    else {
        ensure_model_value(f, x, high_value);
        ensure_model_value(f, shifted, low_value);
    }
}

// For x >= 0, y >= 0, x + y <= 5, lexicographic maximization gives (5, 0).
// Box optimization instead gives max(x) = max(y) = 5 in different models.
// Call optsmt directly: the public context also fixes earlier objectives,
// which could hide a missing constraint in optsmt::lex itself.
static void tst_lex_box_search() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    params_ref p;
    p.set_uint("arith.solver", 6);
    generic_model_converter fm(m, "lex and box");
    struct solver_with_unknown : opt::opt_solver {
        using opt_solver::opt_solver;
        bool unknown_on_next_check = false;

        lbool check_sat_core2(unsigned n, expr* const* assumptions) override {
            if (unknown_on_next_check) {
                unknown_on_next_check = false;
                return l_undef;
            }
            return opt_solver::check_sat_core2(n, assumptions);
        }
    } s(m, p, fm);
    opt::optsmt optimizer(m, ctx);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref y(m.mk_const(symbol("y"), a.mk_real()), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    s.assert_expr(a.mk_ge(x, zero));
    s.assert_expr(a.mk_ge(y, zero));
    solver::scoped_push problem_scope(s);
    s.assert_expr(a.mk_le(a.mk_add(x, y), a.mk_numeral(rational(5), false)));
    ENSURE(s.check_sat(0, nullptr) == l_true);
    model_ref mdl;
    s.get_model(mdl);
    ctx.set_model(mdl);
    unsigned first = optimizer.add(to_app(x));
    unsigned second = optimizer.add(to_app(y));
    optimizer.setup(s);
    optimizer.updt_params(p);
    rational initial_x, initial_y;
    ENSURE(a.is_numeral((*mdl)(x), initial_x));
    ENSURE(a.is_numeral((*mdl)(y), initial_y));
    optimizer.update_lower(first, opt::inf_eps(initial_x));
    optimizer.update_lower(second, opt::inf_eps(initial_y));
    unsigned assertions = s.get_num_assertions();
    auto ensure_problem_unchanged = [&]() {
        ENSURE(s.get_scope_level() == 1);
        ENSURE(s.get_num_assertions() == assertions);
    };
    auto ensure_bounds = [&](unsigned h, int expected) {
        ENSURE(optimizer.get_lower(h).rational_bound() == opt::inf_eps(rational(expected)));
        ENSURE(optimizer.get_upper(h).rational_bound() == opt::inf_eps(rational(expected)));
    };
    auto ensure_model = [&](model* witness, int expected_x, int expected_y) {
        ENSURE(witness);
        rational q;
        ENSURE(a.is_numeral((*witness)(x), q) && q == rational(expected_x));
        ENSURE(a.is_numeral((*witness)(y), q) && q == rational(expected_y));
    };

    // An unfinished first objective must not erase the later model-derived bound.
    s.unknown_on_next_check = true;
    ENSURE(optimizer.lex(first, true) == l_undef);
    ENSURE(!s.unknown_on_next_check);
    ENSURE(optimizer.get_lower(second).rational_bound() == opt::inf_eps(initial_y));
    ensure_problem_unchanged();

    // Success clears the later lower bound. The next call must fix x = 5
    // while optimizing y, even though the first call's solver scope is gone.
    ENSURE(optimizer.lex(first, true) == l_true);
    ensure_bounds(first, 5);
    ENSURE(!optimizer.get_lower(second).is_finite());
    ENSURE(optimizer.get_lower(second).rational_bound().is_neg());
    ensure_problem_unchanged();
    ENSURE(optimizer.lex(second, true) == l_true);
    ensure_bounds(first, 5);
    ensure_bounds(second, 0);
    svector<symbol> labels;
    optimizer.get_model(mdl, labels);
    ensure_model(mdl.get(), 5, 0);
    ensure_problem_unchanged();

    // Reuse the same solver in box mode. Neither objective may be constrained
    // by the other's optimum, and each cached model must attain its own bound.
    ENSURE(optimizer.box() == l_true);
    ensure_bounds(first, 5);
    ensure_bounds(second, 5);
    ensure_model(optimizer.get_model(first), 5, 0);
    ensure_model(optimizer.get_model(second), 0, 5);
    ensure_problem_unchanged();
}

// Earlier open lex objectives conservatively stop before later objectives.
// Last-lex and independent box objectives succeed, also with a preceding soft handle.
static void tst_open_multiobjective(bool box, bool open_first, bool with_soft) {
    opt_fixture f(box ? "box" : "lex", 8);
    Z3_ast x = f.real("x"), y = f.real("y");
    f.add(Z3_mk_lt(f.ctx, f.square(x), f.num(2)));
    f.add(Z3_mk_le(f.ctx, y, f.num(3)));
    unsigned soft = UINT_MAX;
    if (with_soft) {
        Z3_ast p = Z3_mk_const(f.ctx, f.symbol("p"), Z3_mk_bool_sort(f.ctx));
        f.add(Z3_mk_not(f.ctx, p));
        soft = Z3_optimize_assert_soft(f.ctx, f.opt, p, "5/2", f.symbol("cost"));
        ENSURE(soft == 0);
    }
    unsigned first = f.objective(open_first ? x : y);
    unsigned second = f.objective(open_first ? y : x);
    ENSURE(first == (with_soft ? 1u : 0u) && second == first + 1);
    unsigned open = open_first ? first : second;
    unsigned closed = open_first ? second : first;
    bool incomplete = !box && open_first;
    // Optimize the full list; only an earlier open lex objective must return unknown.
    ENSURE(f.check() == (incomplete ? Z3_L_UNDEF : Z3_L_TRUE));
    Z3_ast limit = root(f);
    // Bound caches must remain attached to their public handles while models change.
    auto ensure_bounds = [&]() {
        ensure_open_bounds(f, open, limit, -1);
        if (with_soft)
            ensure_finite_bounds(f, soft, f.num(5, 2));
        if (!incomplete)
            ensure_finite_bounds(f, closed, f.num(3), Z3_INT_SORT);
    };
    ensure_bounds();
    ensure_open_model(f, x, limit, true);
    if (incomplete) {
        char const* reason = Z3_optimize_get_reason_unknown(f.ctx, f.opt);
        ENSURE(reason && std::strstr(reason,
            "later lexicographic objectives after an unattained nonlinear optimum are not supported"));
        // The later objective retains an unproved interval, not the first handle's limit.
        ENSURE(!Z3_is_eq_ast(f.ctx, scalar_bound(f, closed, true), scalar_bound(f, closed, false)));
        for (bool lower : {true, false}) {
            Z3_ast_vector v = lower ? Z3_optimize_get_lower_as_vector(f.ctx, f.opt, closed) :
                                      Z3_optimize_get_upper_as_vector(f.ctx, f.opt, closed);
            ENSURE(v && Z3_get_error_code(f.ctx) == Z3_OK);
            Z3_ast_vector_inc_ref(f.ctx, v);
            ENSURE(Z3_ast_vector_size(f.ctx, v) == 3);
            Z3_ast finite = Z3_ast_vector_get(f.ctx, v, 1);
            ENSURE(Z3_is_numeral_ast(f.ctx, finite) && !Z3_is_algebraic_number(f.ctx, finite));
            ensure_value(f, Z3_ast_vector_get(f.ctx, v, 2), f.num(0));
            Z3_ast_vector_dec_ref(f.ctx, v);
        }
    }
    else if (box) {
        for (unsigned index = 1; index < (with_soft ? 3u : 2u); ++index) {
            // Select each remaining cached box model without optimizing again.
            ENSURE(f.check() == Z3_L_TRUE);
            ensure_bounds();
            ensure_open_model(f, x, limit, true);
            if (index == closed)
                ensure_model_value(f, y, f.num(3));
        }
        // No cached box model remains after one has been returned for each objective.
        ENSURE(f.check() == Z3_L_FALSE);
    }
    else {
        ensure_model_value(f, y, f.num(3));
    }
}

// Unknown results must retain a strict rational bracket around sqrt(2),
// with the vector getters reporting the same endpoints as the scalar getters.
static void ensure_rational_interval(opt_fixture& f, unsigned h) {
    Z3_ast lo = scalar_bound(f, h, true);
    Z3_ast hi = scalar_bound(f, h, false);
    ENSURE(Z3_is_numeral_ast(f.ctx, lo) && !Z3_is_algebraic_number(f.ctx, lo));
    ENSURE(Z3_is_numeral_ast(f.ctx, hi) && !Z3_is_algebraic_number(f.ctx, hi));
    Z3_ast optimum = root(f);
    ENSURE(Z3_algebraic_ge(f.ctx, lo, f.num(0)));
    ENSURE(Z3_algebraic_lt(f.ctx, lo, optimum));
    ENSURE(Z3_algebraic_lt(f.ctx, optimum, hi));
    ENSURE(Z3_algebraic_le(f.ctx, hi, f.num(2)));
    ensure_vector(f, h, true, 0, lo, 0, Z3_get_sort_kind(f.ctx, Z3_get_sort(f.ctx, lo)));
    ensure_vector(f, h, false, 0, hi, 0, Z3_get_sort_kind(f.ctx, Z3_get_sort(f.ctx, hi)));
}

// Budgets zero and one disable or exhaust only the extra certificate.
// Closed optima still work, while an open problem keeps a rational gap and witness.
static void tst_open_proof_budget() {
    for (unsigned proof_budget : {0u, 1u}) {
        opt_fixture f("lex", 8, true, proof_budget);
        Z3_ast x = f.real("x");
        f.add(Z3_mk_ge(f.ctx, x, f.num(0)));
        f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
        unsigned h = f.objective(x);
        // Optimize the closed problem even though the extra proof cannot run to completion.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_finite_bounds(f, h, root(f));
        Z3_optimize_push(f.ctx, f.opt);
        f.add(Z3_mk_lt(f.ctx, f.square(x), f.num(2)));
        // Re-optimize the open problem with disabled or exhausted certification.
        ENSURE(f.check() == Z3_L_UNDEF);
        ensure_rational_interval(f, h);
        ensure_open_model(f, x, root(f), true);
        Z3_optimize_pop(f.ctx, f.opt);
        // Re-optimize after popping the failed proof; its private limit must not leak.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_finite_bounds(f, h, root(f));
    }
}

// Check bounds across repeated solves, additional constraints, and pop.
// The rational cap gives 1; the strict square bound gives an open limit;
// popping either condition restores the attained sqrt(2).
static void tst_recheck_and_scopes() {
    opt_fixture f("lex", 8);
    Z3_ast x = f.real("x");
    f.add(Z3_mk_ge(f.ctx, x, f.num(0)));
    f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
    unsigned h = f.objective(x);
    // Optimize the closed problem, then repeat without changing its inputs.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));

    Z3_optimize_push(f.ctx, f.opt);
    f.add(Z3_mk_le(f.ctx, x, f.num(1)));
    // Re-optimize with a rational cap; the cached sqrt(2) must be replaced.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, f.num(1), Z3_INT_SORT);
    Z3_optimize_pop(f.ctx, f.opt);
    // Re-optimize after removing the cap to recover the algebraic optimum.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));

    Z3_optimize_push(f.ctx, f.opt);
    f.add(Z3_mk_lt(f.ctx, f.square(x), f.num(2)));
    // Re-optimize the open problem; the cached attained optimum is no longer valid.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_open_bounds(f, h, root(f), -1);
    ensure_open_model(f, x, root(f), true);
    // Solve the same open problem again and check its bound and feasible witness.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_open_bounds(f, h, root(f), -1);
    ensure_open_model(f, x, root(f), true);
    Z3_optimize_pop(f.ctx, f.opt);
    // After pop, the closed optimum must have a zero epsilon coefficient.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));
}

static void tst_incremental_callback_bounds() {
    for (bool maximize : {false, true}) {
        opt_fixture f;
        Z3_params p = Z3_mk_params(f.ctx);
        Z3_params_inc_ref(f.ctx, p);
        Z3_params_set_bool(f.ctx, p, f.symbol("incremental"), true);
        Z3_optimize_set_params(f.ctx, f.opt, p);
        ENSURE(Z3_get_error_code(f.ctx) == Z3_OK);
        Z3_params_dec_ref(f.ctx, p);

        Z3_ast x = f.real("x");
        f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
        unsigned first = f.objective(x, maximize);
        unsigned second = f.objective(f.sum(x, f.num(3)), !maximize);
        struct callback_state {
            opt_fixture& f;
            unsigned first;
            bool maximize;
            bool added = false;
        } state{f, first, maximize};
        Z3_model model = Z3_mk_model(f.ctx);
        Z3_model_inc_ref(f.ctx, model);
        Z3_optimize_register_model_eh(f.ctx, f.opt, model, &state, [](void* data) {
            auto& s = *static_cast<callback_state*>(data);
            auto& f = s.f;
            bool lower = !s.maximize;
            if (s.added || !Z3_is_algebraic_number(f.ctx, scalar_bound(f, s.first, lower)))
                return;
            s.added = true;
            // Wait for the first exact optimum, then invalidate bounds without
            // changing feasibility. Infinity must not retain its algebraic part.
            f.add(Z3_mk_true(f.ctx));
            ensure_vector(f, s.first, lower, s.maximize ? 1 : -1, f.num(0), 0, Z3_INT_SORT);
            Z3_ast oo = Z3_mk_const(f.ctx, f.symbol("oo"), Z3_mk_int_sort(f.ctx));
            Z3_ast expected = s.maximize ? oo : Z3_mk_unary_minus(f.ctx, oo);
            Z3_ast same = Z3_simplify(f.ctx, Z3_mk_eq(f.ctx, scalar_bound(f, s.first, lower), expected));
            ENSURE(Z3_get_bool_value(f.ctx, same) == Z3_L_TRUE);
        });
        ENSURE(f.check() == Z3_L_TRUE);
        ENSURE(state.added);
        Z3_ast value = shifted_root(f, f.num(0), maximize);
        ensure_value(f, scalar_bound(f, first, maximize), value);
        ensure_finite_bounds(f, second, shifted_root(f, f.num(3), maximize));
        ensure_model_value(f, x, value);

        // A later solve must recover tight bounds after the one-off invalidation.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_finite_bounds(f, first, value);
        ensure_finite_bounds(f, second, shifted_root(f, f.num(3), maximize));
        Z3_model_dec_ref(f.ctx, model);
    }
}

// Disabling nlsat cells or adding a UF prevents the exact-cell proof.
// Both cases must expose the remaining rational gap, not an algebraic optimum.
static void tst_fallback_intervals() {
    for (bool uf : {false, true}) {
        opt_fixture f("lex", 8, uf);
        Z3_ast x = f.real("x");
        f.add(Z3_mk_ge(f.ctx, x, f.num(0)));
        f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
        if (uf) {
            // This does not restrict x, but keeps the formula outside pure NRA.
            Z3_sort real = Z3_mk_real_sort(f.ctx);
            Z3_func_decl g = Z3_mk_func_decl(f.ctx, f.symbol("g"), 1, &real, real);
            Z3_ast gx = Z3_mk_app(f.ctx, g, 1, &x);
            f.add(Z3_mk_ge(f.ctx, gx, f.num(0)));
        }
        unsigned h = f.objective(x);
        // Run fallback optimization with a small round budget; expect unknown.
        ENSURE(f.check() == Z3_L_UNDEF);
        ensure_rational_interval(f, h);
    }
}

enum class search_exit { unknown, cancel, exception };

class search_exit_solver : public opt::opt_solver {
public:
    search_exit kind;
    unsigned probe = 0;
    unsigned stop_at;
    bool stopped = false;

    search_exit_solver(ast_manager& m, params_ref const& p, generic_model_converter& fm,
                       search_exit kind, unsigned stop_at):
        opt_solver(m, p, fm), kind(kind), stop_at(stop_at) {}

    void assert_expr_core(expr* e) override {
        opt_solver::assert_expr_core(e);
        // Cancel between iterations, while the newly pushed probe is still live.
        if (kind == search_exit::cancel && stop_here())
            get_manager().limit().cancel();
    }

    lbool check_sat_core2(unsigned n, expr* const* assumptions) override {
        if (kind != search_exit::cancel && stop_here()) {
            if (kind == search_exit::exception)
                throw default_exception("search scope test");
            return l_undef;
        }
        return opt_solver::check_sat_core2(n, assumptions);
    }

private:
    bool stop_here() {
        // The test opens level one and optsmt::lex opens level two.
        // Wait for a deeper push, where a trial bound is active, and stop once.
        if (stopped || get_scope_level() <= 2 || ++probe != stop_at)
            return false;
        stopped = true;
        return true;
    }
};

// Maximize the real variable x subject to x >= 0 and x*x <= 2.
// The feasible interval is [0, sqrt(2)], so the true maximum is sqrt(2).
// With exact nlsat optimization disabled, this search keeps rational lower
// and upper bounds. A short bisection run leaves a gap, so we expect UNKNOWN,
// not a claim that one of those rational bounds is the exact maximum.
//
// The search first tries a temporary bound x >= best + step. When that bound
// is infeasible, it removes it and switches to bisection. Bisection alternates
// between asking for any improvement (x > lo) and trying the midpoint
// (x >= (lo + hi)/2). Each question gets its own temporary solver scope.
//
// Force an early exit while a trial bound is active, then check that all
// search scopes were removed, the original constraints still allow x = 0,
// and the same optimizer and solver can be used again.
static void tst_search_scope_exits() {
    // Run all three exit types at both locations, with a fresh solver each time:
    // stop_at = 1 stops the geometric trial; stop_at = 2 lets it fail normally
    // and stops the first bisection trial. Counting trials avoids timing limits
    // or resource counts that could stop at different places on other machines.
    for (search_exit exit : {search_exit::unknown, search_exit::cancel, search_exit::exception})
        for (unsigned stop_at : {1u, 2u}) {
            ast_manager m;
            reg_decl_plugins(m);
            arith_util a(m);
            opt::context ctx(m);
            params_ref p;
            // Keep the exact-cell shortcut out of the test so the failed
            // geometric step leads to the bisection code we want to exercise.
            p.set_bool("optsmt_nlsat", false);
            p.set_uint("optsmt_bisect_rounds", 8);
            p.set_uint("arith.solver", 6);
            generic_model_converter fm(m, "search scopes");
            search_exit_solver s(m, p, fm, exit, stop_at);
            opt::optsmt optimizer(m, ctx);
            expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
            expr_ref zero(a.mk_numeral(rational(0), false), m);
            s.assert_expr(a.mk_le(a.mk_mul(x, x), a.mk_numeral(rational(2), false)));
            // Put x >= 0 in a scope that must survive the optimization call.
            // After the search, this must still be the only open scope.
            solver::scoped_push caller_scope(s);
            s.assert_expr(a.mk_ge(x, zero));
            ENSURE(s.check_sat(0, nullptr) == l_true);
            model_ref mdl;
            s.get_model(mdl);
            ctx.set_model(mdl);
            unsigned h = optimizer.add(to_app(x));
            optimizer.setup(s);
            optimizer.updt_params(p);
            rational initial;
            // Start the search with a valid lower bound from a feasible model,
            // just as the normal optimization entry point does.
            ENSURE(opt::model_value_bound(a, (*mdl)(x), true, initial));
            optimizer.update_lower(h, opt::inf_eps(initial));
            unsigned assertions = s.get_num_assertions();
            bool threw = false;
            // UNKNOWN and cancellation should return l_undef. The test exception
            // should escape unchanged, but still trigger scope cleanup.
            try {
                ENSURE(optimizer.lex(h, true) == l_undef);
            }
            catch (default_exception const& ex) {
                ENSURE(std::strcmp(ex.what(), "search scope test") == 0);
                threw = true;
            }
            // Ensure the intended stop was reached, then check that neither
            // extra pushes nor temporary assertions remain.
            ENSURE(s.stopped);
            ENSURE(threw == (exit == search_exit::exception));
            ENSURE(s.get_scope_level() == 1);
            ENSURE(s.get_num_assertions() == assertions);
            if (exit == search_exit::cancel) {
                // Cleanup must not swallow the cancellation request. Clear it
                // here only so the remaining checks can use the solver again.
                ENSURE(m.limit().is_canceled());
                m.limit().reset_cancel();
            }
            // x = 0 satisfies both original constraints, but violates the trial
            // improvement bounds. A leaked bound would make this check UNSAT.
            {
                solver::scoped_push check_scope(s);
                s.assert_expr(m.mk_eq(x, zero));
                ENSURE(s.check_sat(0, nullptr) == l_true);
            }
            // The forced stop happens only once. Retry without it on the same
            // objects: eight bisection rounds still leave a rational gap around
            // sqrt(2), so UNKNOWN is expected, with no extra scopes or assertions.
            ENSURE(optimizer.lex(h, true) == l_undef);
            ENSURE(s.get_scope_level() == 1);
            ENSURE(s.get_num_assertions() == assertions);
        }
}

// A real relaxation would approach 2, but integer n < 2 forces x < 1.
// Keep this mixed-arithmetic problem incomplete rather than certify the wrong limit.
static void tst_open_integer_fallback() {
    opt_fixture f("lex", 8);
    Z3_ast x = f.real("x");
    Z3_sort integer = Z3_mk_int_sort(f.ctx);
    Z3_ast n = Z3_mk_const(f.ctx, f.symbol("n"), integer);
    f.add(Z3_mk_lt(f.ctx, x, Z3_mk_int2real(f.ctx, n)));
    f.add(Z3_mk_lt(f.ctx, n, Z3_mk_int(f.ctx, 2, integer)));
    f.add(Z3_mk_lt(f.ctx, f.square(x), f.num(4)));
    unsigned h = f.objective(x);
    // Optimization must not use the real-only quantified certificate for integer n.
    ENSURE(f.check() == Z3_L_UNDEF);
    ensure_open_model(f, x, f.num(1), true);
    // Do not prescribe fallback endpoints, but a finite lower bound cannot exceed 1.
    for (bool lower : {true, false}) {
        scalar_bound(f, h, lower);
        Z3_ast_vector v = lower ? Z3_optimize_get_lower_as_vector(f.ctx, f.opt, h) :
                                  Z3_optimize_get_upper_as_vector(f.ctx, f.opt, h);
        ENSURE(v && Z3_get_error_code(f.ctx) == Z3_OK);
        Z3_ast_vector_inc_ref(f.ctx, v);
        ENSURE(Z3_ast_vector_size(f.ctx, v) == 3);
        Z3_ast infinity = Z3_ast_vector_get(f.ctx, v, 0);
        Z3_ast finite = Z3_ast_vector_get(f.ctx, v, 1);
        ENSURE(Z3_algebraic_is_value(f.ctx, finite));
        ensure_sort(f, infinity, Z3_INT_SORT);
        ensure_sort(f, Z3_ast_vector_get(f.ctx, v, 2), Z3_INT_SORT);
        ENSURE(lower ? Z3_algebraic_le(f.ctx, infinity, f.num(0)) :
                       Z3_algebraic_ge(f.ctx, infinity, f.num(0)));
        if (Z3_algebraic_eq(f.ctx, infinity, f.num(0)))
            ENSURE(lower ? Z3_algebraic_le(f.ctx, finite, f.num(1)) :
                           Z3_algebraic_ge(f.ctx, finite, f.num(1)));
        Z3_ast_vector_dec_ref(f.ctx, v);
    }
}

// Invalid objective handles report Z3_EXCEPTION and "index out of bounds".
static void ensure_index_error(opt_fixture& f) {
    ENSURE(Z3_get_error_code(f.ctx) == Z3_EXCEPTION);
    ENSURE(std::strcmp(Z3_get_error_msg(f.ctx, Z3_EXCEPTION), "index out of bounds") == 0);
}

// All four getters must reject an invalid handle without accessing objective storage.
static void ensure_invalid_index(opt_fixture& f, unsigned h) {
    ENSURE(!Z3_optimize_get_lower(f.ctx, f.opt, h));
    ensure_index_error(f);
    ENSURE(!Z3_optimize_get_upper(f.ctx, f.opt, h));
    ensure_index_error(f);
    ENSURE(!Z3_optimize_get_lower_as_vector(f.ctx, f.opt, h));
    ensure_index_error(f);
    ENSURE(!Z3_optimize_get_upper_as_vector(f.ctx, f.opt, h));
    ensure_index_error(f);
}

// Check invalid handles before and after solving and after removing all objectives.
// A reused index must report the bounds of its replacement objective.
static void tst_reset_and_invalid_indices(bool open) {
    opt_fixture f("lex", 8);
    ensure_invalid_index(f, 0);
    ensure_invalid_index(f, UINT_MAX);
    Z3_ast x = f.real("x");
    Z3_optimize_push(f.ctx, f.opt);
    f.add(open ? Z3_mk_lt(f.ctx, f.square(x), f.num(2)) : Z3_mk_le(f.ctx, f.square(x), f.num(2)));
    unsigned h = f.objective(x);
    ENSURE(h == 0);
    // Optimize once to populate the exact-value cache before testing its lifetime.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_invalid_index(f, h + 1);
    ensure_invalid_index(f, UINT_MAX);
    if (open) {
        ensure_open_bounds(f, h, root(f), -1);
        ensure_open_model(f, x, root(f), true);
    }
    else {
        ensure_finite_bounds(f, h, root(f));
    }

    // There is no Optimize reset API: pop all objectives, then reuse handle zero.
    Z3_optimize_pop(f.ctx, f.opt);
    // With no objectives, this only checks feasibility and refreshes internal state.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_invalid_index(f, h);
    ensure_invalid_index(f, UINT_MAX);
    f.add(Z3_mk_le(f.ctx, x, f.num(-1)));
    unsigned replacement = f.objective(x);
    ENSURE(replacement == h);
    // Optimize the replacement objective; its rational result must replace the root.
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, replacement, f.num(-1), Z3_INT_SORT);
}

// Check max 7/3, min -5/2, and max 2 under x^2 <= 4.
// Fractional bounds use Real numerals; the integral bound 2 uses Int numerals.
static void tst_rational_bounds() {
    for (bool maximize : {true, false}) {
        opt_fixture f;
        Z3_ast x = f.real("x");
        f.add(Z3_mk_ge(f.ctx, x, f.num(-5, 2)));
        f.add(Z3_mk_le(f.ctx, x, f.num(7, 3)));
        unsigned h = f.objective(x, maximize);
        // Optimize the rational interval in each direction.
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_finite_bounds(f, h, maximize ? f.num(7, 3) : f.num(-5, 2));
    }
    opt_fixture f;
    Z3_ast x = f.real("x");
    f.add(Z3_mk_le(f.ctx, f.square(x), f.num(4)));
    unsigned h = f.objective(x);
    // Optimize a nonlinear problem whose attained optimum is nevertheless rational.
    ENSURE(f.check() == Z3_L_TRUE);
    // Require Int numerals for the integral bounds of this Real objective.
    ensure_finite_bounds(f, h, f.num(2), Z3_INT_SORT);
}

// Infinity and epsilon are symbolic bounds, not algebraic values. Check the
// scalar expression and its corresponding coefficient-vector representation.
static void ensure_symbolic_bounds(opt_fixture& f, unsigned h, int infinity, int finite, int epsilon) {
    Z3_sort sort = epsilon ? Z3_mk_real_sort(f.ctx) : Z3_mk_int_sort(f.ctx);
    Z3_ast terms[3];
    unsigned size = 0;
    if (infinity) {
        Z3_ast oo = Z3_mk_const(f.ctx, f.symbol("oo"), sort);
        terms[size++] = infinity > 0 ? oo : Z3_mk_unary_minus(f.ctx, oo);
    }
    if (finite)
        terms[size++] = Z3_mk_int(f.ctx, finite, sort);
    if (epsilon) {
        Z3_ast ep = Z3_mk_const(f.ctx, f.symbol("epsilon"), Z3_mk_real_sort(f.ctx));
        terms[size++] = epsilon > 0 ? ep : Z3_mk_unary_minus(f.ctx, ep);
    }
    ENSURE(size > 0);
    Z3_ast expected = size == 1 ? terms[0] : Z3_mk_add(f.ctx, size, terms);
    for (bool lower : {true, false}) {
        Z3_ast b = scalar_bound(f, h, lower);
        ENSURE(!Z3_algebraic_is_value(f.ctx, b));
        Z3_ast same = Z3_simplify(f.ctx, Z3_mk_eq(f.ctx, b, expected));
        ENSURE(Z3_get_bool_value(f.ctx, same) == Z3_L_TRUE);
        ensure_vector(f, h, lower, infinity, f.num(finite), epsilon, Z3_INT_SORT);
    }
}

// Unconstrained max/min must yield +/-oo. Strict bounds x<1 and x>1 must
// yield 1-epsilon and 1+epsilon, with matching scalar/vector encodings.
static void tst_infinity_and_epsilon() {
    for (bool maximize : {true, false}) {
        opt_fixture unbounded;
        unsigned h = unbounded.objective(unbounded.real("x"), maximize);
        // Optimize without constraints to obtain the signed infinite bound.
        ENSURE(unbounded.check() == Z3_L_TRUE);
        ensure_symbolic_bounds(unbounded, h, maximize ? 1 : -1, 0, 0);

        opt_fixture strict;
        Z3_ast x = strict.real("x");
        strict.add(maximize ? Z3_mk_lt(strict.ctx, x, strict.num(1)) :
                               Z3_mk_gt(strict.ctx, x, strict.num(1)));
        h = strict.objective(x, maximize);
        // Optimize the strict linear bound, whose finite limit is not attained.
        ENSURE(strict.check() == Z3_L_TRUE);
        ensure_symbolic_bounds(strict, h, 0, 1, maximize ? -1 : 1);
    }
}

static void tst_symba_bounds() {
    // An integer slack selects theory_inf_arith instead of the pure-LRA
    // shortcut, so these cases exercise SYMBA's vector-bound updates.
    for (bool strict : {false, true}) {
        opt_fixture f("lex", 64, true, 100000, "symba");
        Z3_ast x = f.real("x");
        Z3_ast n = Z3_mk_const(f.ctx, f.symbol("n"), Z3_mk_int_sort(f.ctx));
        Z3_ast slack = Z3_mk_int2real(f.ctx, n);
        f.add(Z3_mk_ge(f.ctx, slack, f.num(0)));
        Z3_ast total = f.sum(x, slack);
        f.add(strict ? Z3_mk_lt(f.ctx, total, f.num(2)) : Z3_mk_le(f.ctx, total, f.num(2)));
        unsigned h = f.objective(x);
        ENSURE(f.check() == Z3_L_TRUE);
        if (strict)
            ensure_symbolic_bounds(f, h, 0, 2, -1);
        else
            ensure_finite_bounds(f, h, f.num(2), Z3_INT_SORT);
    }

    opt_fixture f("lex", 64, true, 100000, "symba");
    Z3_ast x = f.real("x"), y = f.real("y");
    Z3_ast n = Z3_mk_const(f.ctx, f.symbol("n"), Z3_mk_int_sort(f.ctx));
    Z3_ast slack = Z3_mk_int2real(f.ctx, n);
    f.add(Z3_mk_ge(f.ctx, x, f.num(0)));
    f.add(Z3_mk_ge(f.ctx, y, f.num(0)));
    f.add(Z3_mk_ge(f.ctx, slack, f.num(0)));
    f.add(Z3_mk_le(f.ctx, f.sum(f.sum(x, y), slack), f.num(5)));
    unsigned first = f.objective(x), second = f.objective(y);
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, first, f.num(5), Z3_INT_SORT);
    ensure_finite_bounds(f, second, f.num(0), Z3_INT_SORT);
    // Legacy SYMBA may retain its initial feasible model even with tight
    // bounds. Witness selection is not changed by the value representation.
}

// Check unsigned BV maximum 9 and minimum 3 as Int scalar bounds,
// with coefficient vectors [0, 9, 0] and [0, 3, 0].
static void tst_bitvector_bounds() {
    for (bool maximize : {true, false}) {
        opt_fixture f;
        Z3_sort bv = Z3_mk_bv_sort(f.ctx, 8);
        Z3_ast x = Z3_mk_const(f.ctx, f.symbol("x"), bv);
        f.add(Z3_mk_bvuge(f.ctx, x, Z3_mk_int(f.ctx, 3, bv)));
        f.add(Z3_mk_bvule(f.ctx, x, Z3_mk_int(f.ctx, 9, bv)));
        unsigned h = f.objective(x, maximize);
        // Optimize the unsigned eight-bit range [3, 9] in each direction.
        ENSURE(f.check() == Z3_L_TRUE);
        // BV objectives lower to MaxSMT, not to the algebraic-value cache.
        ensure_finite_bounds(f, h, f.num(maximize ? 9 : 3), Z3_INT_SORT);
    }
}

}

// Run all the optimization tests defined above.
void tst_opt_bounds() {
    std::cout << "opt_bounds: per-call arithmetic results\n";
    tst_maximize_result();
    std::cout << "opt_bounds: geometric step schedule\n";
    tst_geometric_step();
    std::cout << "opt_bounds: signed algebraic optima and offsets\n";
    tst_signed_offsets();
    std::cout << "opt_bounds: lexicographic and box handles\n";
    tst_multiobjective(false);
    tst_multiobjective(true);
    tst_lex_box_search();
    std::cout << "opt_bounds: finite open bounds and polynomial objectives\n";
    tst_open_bounds();
    tst_open_polynomial_objectives();
    std::cout << "opt_bounds: open lexicographic and box handles\n";
    for (bool with_soft : {false, true}) {
        tst_open_multiobjective(false, true, with_soft);
        tst_open_multiobjective(true, true, with_soft);
        tst_open_multiobjective(false, false, with_soft);
    }
    std::cout << "opt_bounds: recheck, scopes, and unknown intervals\n";
    tst_recheck_and_scopes();
    tst_incremental_callback_bounds();
    tst_open_proof_budget();
    tst_fallback_intervals();
    tst_search_scope_exits();
    tst_open_integer_fallback();
    std::cout << "opt_bounds: reset and invalid indices\n";
    tst_reset_and_invalid_indices(false);
    tst_reset_and_invalid_indices(true);
    std::cout << "opt_bounds: rational, infinity, epsilon, and BV compatibility\n";
    tst_rational_bounds();
    tst_infinity_and_epsilon();
    tst_symba_bounds();
    tst_bitvector_bounds();
}
