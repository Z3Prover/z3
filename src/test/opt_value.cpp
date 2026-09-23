/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_value.cpp

Abstract:

    Tests for exact optimization values and their legacy rational bounds.

--*/

#include "opt/opt_value.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "math/polynomial/algebraic_numbers.h"
#include <utility>

namespace {

expr_ref square_root(ast_manager& m, int n) {
    arith_util a(m);
    scoped_anum value(a.am());
    a.am().set(value, n);
    a.am().root(value, 2, value);
    return expr_ref(a.mk_numeral(a.am(), value, false), m);
}

void ensure_equal(ast_manager& m, expr* actual, expr* expected) {
    expr_ref equality(m.mk_eq(actual, expected), m);
    th_rewriter rw(m);
    rw(equality);
    ENSURE(m.is_true(equality));
}

void tst_rational(ast_manager& m) {
    arith_util a(m);
    opt::objective_value value(m);
    ENSURE(!value.exact_finite());
    ENSURE(value.is_finite() && !value.has_infinitesimal());
    ENSURE(a.is_int(value.to_expr()));
    ensure_equal(m, value.to_expr(), a.mk_int(0));

    value = opt::inf_eps(rational(7, 3));
    ensure_equal(m, value.to_expr(), a.mk_real(rational(7, 3)));
    expr_ref_vector coefficients(m);
    value.to_exprs(coefficients);
    ENSURE(coefficients.size() == 3);
    ENSURE(a.is_int(coefficients.get(0)) && a.is_real(coefficients.get(1)) && a.is_int(coefficients.get(2)));
    ensure_equal(m, coefficients.get(1), a.mk_real(rational(7, 3)));

    expr_ref two(a.mk_real(2), m);
    value.set_exact(opt::inf_eps(rational(2)), two);
    ENSURE(value == opt::objective_value(m, opt::inf_eps(rational(2))));
    ENSURE(a.is_real(value.exact_finite()));
    ENSURE(a.is_int(value.to_expr()));
    coefficients.reset();
    value.to_exprs(coefficients);
    ENSURE(a.is_int(coefficients.get(1)));
    ENSURE(value.adjusted(rational(3, 2), true) ==
           opt::objective_value(m, opt::inf_eps(rational(-1, 2))));

    value = opt::inf_eps::infinity();
    ENSURE(!value.exact_finite() && !value.is_finite());
    opt::objective_value adjusted = value.adjusted(rational(3), true);
    expr_ref oo(m.mk_const(symbol("oo"), a.mk_int()), m);
    ensure_equal(m, adjusted.to_expr(), a.mk_add(a.mk_uminus(oo), a.mk_int(3)));
    ENSURE(adjusted.rational_bound().get_infinity() == rational(-1));
    ENSURE(adjusted != value);
    value.reset();
    ENSURE(value == opt::objective_value(m));
}

void tst_algebraic(ast_manager& m) {
    arith_util a(m);
    expr_ref root = square_root(m, 2);
    opt::objective_value lower(m), upper(m), other(m);
    lower.set_exact(opt::inf_eps(rational(1)), root);
    upper.set_exact(opt::inf_eps(rational(2)), root);
    ENSURE(lower.rational_bound() != upper.rational_bound());
    ENSURE(lower == upper);
    ensure_equal(m, lower.to_expr(), root);
    ensure_equal(m, upper.to_expr(), root);

    // Identical rational approximations must not collapse distinct exact values.
    other.set_exact(opt::inf_eps(rational(1)), square_root(m, 3));
    ENSURE(lower.rational_bound() == other.rational_bound());
    ENSURE(lower != other);
    ENSURE(lower != opt::objective_value(m, opt::inf_eps(rational(1))));

    lower.update_rational_bound(opt::inf_eps(rational(7, 5)));
    ENSURE(lower == upper);
    ENSURE(lower.rational_bound() == opt::inf_eps(rational(7, 5)));
    opt::objective_value adjusted = lower.adjusted(rational(3), true);
    ensure_equal(m, adjusted.to_expr(), a.mk_sub(a.mk_real(3), root));
    ENSURE(adjusted.rational_bound() == opt::inf_eps(rational(8, 5)));
    ENSURE(adjusted != lower);

    expr_ref_vector coefficients(m);
    adjusted.to_exprs(coefficients);
    ENSURE(coefficients.size() == 3);
    ensure_equal(m, coefficients.get(0), a.mk_int(0));
    ensure_equal(m, coefficients.get(1), a.mk_sub(a.mk_real(3), root));
    ensure_equal(m, coefficients.get(2), a.mk_int(0));
    ENSURE(a.is_real(coefficients.get(1)));

    opt::objective_value copy(lower);
    lower.reset();
    ensure_equal(m, copy.to_expr(), root);
    lower = copy;
    copy = opt::inf_eps::infinity();
    ENSURE(lower == upper);
    ENSURE(!copy.exact_finite());
    opt::objective_value moved(std::move(lower));
    ensure_equal(m, moved.to_expr(), root);

    vector<opt::objective_value> values;
    for (unsigned i = 0; i < 20; ++i)
        values.push_back(moved);
    moved.reset_exact();
    ENSURE(!moved.exact_finite());
    ENSURE(moved.rational_bound() == opt::inf_eps(rational(7, 5)));
    for (auto const& value : values)
        ENSURE(value == upper);
    values.reset();
}

void tst_open(ast_manager& m) {
    arith_util a(m);
    expr_ref root = square_root(m, 2);
    expr_ref epsilon(m.mk_const(symbol("epsilon"), a.mk_real()), m);
    opt::objective_value value(m);
    value.set_exact(opt::inf_eps(rational(0), inf_rational(rational(1), rational(-1))), root);
    ENSURE(value.is_finite() && value.has_infinitesimal());
    ensure_equal(m, value.to_expr(), a.mk_sub(root, epsilon));
    opt::objective_value closed(m);
    closed.set_exact(opt::inf_eps(rational(1)), root);
    ENSURE(value != closed);

    opt::objective_value adjusted = value.adjusted(rational(3), true);
    ensure_equal(m, adjusted.to_expr(), a.mk_add(a.mk_sub(a.mk_real(3), root), epsilon));
    ENSURE(adjusted.rational_bound().get_infinitesimal() == rational(1));
    expr_ref_vector coefficients(m);
    adjusted.to_exprs(coefficients);
    ensure_equal(m, coefficients.get(1), a.mk_sub(a.mk_real(3), root));
    ensure_equal(m, coefficients.get(2), a.mk_int(1));

    // Replacing an open algebraic result must discard both its finite part
    // and its epsilon, while a copied result remains intact.
    value = opt::inf_eps(rational(-2));
    ENSURE(!value.exact_finite() && !value.has_infinitesimal());
    ENSURE(a.is_int(value.to_expr()));
    ENSURE(adjusted.exact_finite() && adjusted.has_infinitesimal());
    adjusted.reset();
    ENSURE(!adjusted.exact_finite() && !adjusted.has_infinitesimal());
}

}

void tst_opt_value() {
    ast_manager m;
    reg_decl_plugins(m);
    tst_rational(m);
    tst_algebraic(m);
    tst_open(m);
}
