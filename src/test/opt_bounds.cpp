/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_bounds.cpp

Abstract:

    Public API regressions for exact algebraic Optimize bounds and the
    rational, infinity, and infinitesimal coefficient-vector fallbacks.

--*/
#include "api/z3.h"
#include "util/debug.h"
#include <climits>
#include <cstring>
#include <initializer_list>
#include <iostream>

namespace {

struct opt_fixture {
    Z3_context ctx;
    Z3_optimize opt;

    opt_fixture(char const* priority = "lex", unsigned rounds = 64, bool nlsat = true) {
        Z3_config cfg = Z3_mk_config();
        ctx = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        Z3_set_error_handler(ctx, [](Z3_context, Z3_error_code) {});
        opt = Z3_mk_optimize(ctx);
        Z3_optimize_inc_ref(ctx, opt);
        Z3_params p = Z3_mk_params(ctx);
        Z3_params_inc_ref(ctx, p);
        Z3_params_set_symbol(ctx, p, symbol("priority"), symbol(priority));
        Z3_params_set_symbol(ctx, p, symbol("optsmt_engine"), symbol("basic"));
        Z3_params_set_bool(ctx, p, symbol("optsmt_nlsat"), nlsat);
        Z3_params_set_uint(ctx, p, symbol("optsmt_bisect_rounds"), rounds);
        Z3_params_set_uint(ctx, p, symbol("smt.arith.solver"), 6);
        Z3_params_set_uint(ctx, p, symbol("timeout"), 10000);
        Z3_optimize_set_params(ctx, opt, p);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
        Z3_params_dec_ref(ctx, p);
    }

    ~opt_fixture() {
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
        unsigned h = maximize ? Z3_optimize_maximize(ctx, opt, a) : Z3_optimize_minimize(ctx, opt, a);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
        return h;
    }
    Z3_lbool check() {
        Z3_lbool r = Z3_optimize_check(ctx, opt, 0, nullptr);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
        return r;
    }
};

static Z3_ast root(opt_fixture& f) {
    Z3_ast r = Z3_algebraic_root(f.ctx, f.num(2), 2);
    ENSURE(r && Z3_is_algebraic_number(f.ctx, r));
    ENSURE(Z3_algebraic_is_pos(f.ctx, r));
    ENSURE(Z3_algebraic_eq(f.ctx, Z3_algebraic_power(f.ctx, r, 2), f.num(2)));
    return r;
}

static Z3_ast shifted_root(opt_fixture& f, Z3_ast offset, bool positive) {
    return positive ? Z3_algebraic_add(f.ctx, offset, root(f)) :
                      Z3_algebraic_sub(f.ctx, offset, root(f));
}

static void ensure_value(opt_fixture& f, Z3_ast actual, Z3_ast expected) {
    ENSURE(actual && Z3_algebraic_is_value(f.ctx, actual));
    ENSURE(Z3_is_algebraic_number(f.ctx, actual) == Z3_is_algebraic_number(f.ctx, expected));
    ENSURE(Z3_algebraic_eq(f.ctx, actual, expected));
}

static void ensure_sort(opt_fixture& f, Z3_ast a, Z3_sort_kind kind) {
    ENSURE(Z3_get_sort_kind(f.ctx, Z3_get_sort(f.ctx, a)) == kind);
}

static Z3_ast scalar_bound(opt_fixture& f, unsigned h, bool lower) {
    Z3_ast r = lower ? Z3_optimize_get_lower(f.ctx, f.opt, h) :
                       Z3_optimize_get_upper(f.ctx, f.opt, h);
    ENSURE(r && Z3_get_error_code(f.ctx) == Z3_OK);
    return r;
}

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

static void ensure_finite_bounds(opt_fixture& f, unsigned h, Z3_ast expected,
                                 Z3_sort_kind kind = Z3_REAL_SORT) {
    for (bool lower : {true, false}) {
        Z3_ast b = scalar_bound(f, h, lower);
        ensure_value(f, b, expected);
        ensure_sort(f, b, kind);
        ensure_vector(f, h, lower, 0, expected, 0, kind);
    }
}

static void ensure_model_value(opt_fixture& f, Z3_ast objective, Z3_ast expected) {
    Z3_model m = Z3_optimize_get_model(f.ctx, f.opt);
    ENSURE(m);
    Z3_model_inc_ref(f.ctx, m);
    Z3_ast value = nullptr;
    ENSURE(Z3_model_eval(f.ctx, m, objective, true, &value));
    ensure_value(f, value, expected);
    Z3_model_dec_ref(f.ctx, m);
}

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
            ENSURE(f.check() == Z3_L_TRUE);
            // The shifted root is checked algebraically, not through a rounded display.
            Z3_ast expected = shifted_root(f, offset, maximize);
            ensure_finite_bounds(f, h, expected);
            ensure_model_value(f, objective, expected);
        }
    }
}

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
        // Selecting the next box model must not overwrite another objective's value.
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

static void tst_recheck_and_scopes() {
    opt_fixture f("lex", 8);
    Z3_ast x = f.real("x");
    f.add(Z3_mk_ge(f.ctx, x, f.num(0)));
    f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
    unsigned h = f.objective(x);
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));

    Z3_optimize_push(f.ctx, f.opt);
    f.add(Z3_mk_le(f.ctx, x, f.num(1)));
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, f.num(1), Z3_INT_SORT);
    Z3_optimize_pop(f.ctx, f.opt);
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));

    Z3_optimize_push(f.ctx, f.opt);
    f.add(Z3_mk_lt(f.ctx, f.square(x), f.num(2)));
    // A previously attained root is not an exact bound for the new open problem.
    ENSURE(f.check() == Z3_L_UNDEF);
    ensure_rational_interval(f, h);
    Z3_optimize_pop(f.ctx, f.opt);
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, h, root(f));
}

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
        // Either disabling cells or declining the UF fragment leaves a rational gap.
        ENSURE(f.check() == Z3_L_UNDEF);
        ensure_rational_interval(f, h);
    }
}

static void ensure_index_error(opt_fixture& f) {
    ENSURE(Z3_get_error_code(f.ctx) == Z3_EXCEPTION);
    ENSURE(std::strcmp(Z3_get_error_msg(f.ctx, Z3_EXCEPTION), "index out of bounds") == 0);
}

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

static void tst_reset_and_invalid_indices() {
    opt_fixture f;
    ensure_invalid_index(f, 0);
    ensure_invalid_index(f, UINT_MAX);
    Z3_ast x = f.real("x");
    Z3_optimize_push(f.ctx, f.opt);
    f.add(Z3_mk_le(f.ctx, f.square(x), f.num(2)));
    unsigned h = f.objective(x);
    ENSURE(h == 0);
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_invalid_index(f, h + 1);
    ensure_invalid_index(f, UINT_MAX);
    ensure_finite_bounds(f, h, root(f));

    // There is no Optimize reset API: pop all objectives, then reuse handle zero.
    Z3_optimize_pop(f.ctx, f.opt);
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_invalid_index(f, h);
    ensure_invalid_index(f, UINT_MAX);
    f.add(Z3_mk_le(f.ctx, x, f.num(-1)));
    unsigned replacement = f.objective(x);
    ENSURE(replacement == h);
    ENSURE(f.check() == Z3_L_TRUE);
    ensure_finite_bounds(f, replacement, f.num(-1), Z3_INT_SORT);
}

static void tst_rational_bounds() {
    for (bool maximize : {true, false}) {
        opt_fixture f;
        Z3_ast x = f.real("x");
        f.add(Z3_mk_ge(f.ctx, x, f.num(-5, 2)));
        f.add(Z3_mk_le(f.ctx, x, f.num(7, 3)));
        unsigned h = f.objective(x, maximize);
        ENSURE(f.check() == Z3_L_TRUE);
        ensure_finite_bounds(f, h, maximize ? f.num(7, 3) : f.num(-5, 2));
    }
    opt_fixture f;
    Z3_ast x = f.real("x");
    f.add(Z3_mk_le(f.ctx, f.square(x), f.num(4)));
    unsigned h = f.objective(x);
    ENSURE(f.check() == Z3_L_TRUE);
    // Integral rational optima retain Int numerals even for a Real objective.
    ensure_finite_bounds(f, h, f.num(2), Z3_INT_SORT);
}

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

static void tst_infinity_and_epsilon() {
    for (bool maximize : {true, false}) {
        opt_fixture unbounded;
        unsigned h = unbounded.objective(unbounded.real("x"), maximize);
        ENSURE(unbounded.check() == Z3_L_TRUE);
        ensure_symbolic_bounds(unbounded, h, maximize ? 1 : -1, 0, 0);

        opt_fixture strict;
        Z3_ast x = strict.real("x");
        strict.add(maximize ? Z3_mk_lt(strict.ctx, x, strict.num(1)) :
                               Z3_mk_gt(strict.ctx, x, strict.num(1)));
        h = strict.objective(x, maximize);
        ENSURE(strict.check() == Z3_L_TRUE);
        ensure_symbolic_bounds(strict, h, 0, 1, maximize ? -1 : 1);
    }
}

static void tst_bitvector_bounds() {
    for (bool maximize : {true, false}) {
        opt_fixture f;
        Z3_sort bv = Z3_mk_bv_sort(f.ctx, 8);
        Z3_ast x = Z3_mk_const(f.ctx, f.symbol("x"), bv);
        f.add(Z3_mk_bvuge(f.ctx, x, Z3_mk_int(f.ctx, 3, bv)));
        f.add(Z3_mk_bvule(f.ctx, x, Z3_mk_int(f.ctx, 9, bv)));
        unsigned h = f.objective(x, maximize);
        ENSURE(f.check() == Z3_L_TRUE);
        // BV objectives lower to MaxSMT, not to the algebraic-value cache.
        ensure_finite_bounds(f, h, f.num(maximize ? 9 : 3), Z3_INT_SORT);
    }
}

}

void tst_opt_bounds() {
    std::cout << "opt_bounds: signed algebraic optima and offsets\n";
    tst_signed_offsets();
    std::cout << "opt_bounds: lexicographic and box handles\n";
    tst_multiobjective(false);
    tst_multiobjective(true);
    std::cout << "opt_bounds: recheck, scopes, and unknown intervals\n";
    tst_recheck_and_scopes();
    tst_fallback_intervals();
    std::cout << "opt_bounds: reset and invalid indices\n";
    tst_reset_and_invalid_indices();
    std::cout << "opt_bounds: rational, infinity, epsilon, and BV compatibility\n";
    tst_rational_bounds();
    tst_infinity_and_epsilon();
    tst_bitvector_bounds();
}
