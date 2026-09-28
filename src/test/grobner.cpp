#include "math/grobner/grobner.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "util/debug.h"

void tst_grobner() {
    constexpr unsigned coefficient_bits = 1024;
    ast_manager m;
    reg_decl_plugins(m);
    v_dependency_manager dm;
    arith_util a(m);
    expr_ref x(m.mk_const("x", a.mk_int()), m);
    expr_ref y(m.mk_const("y", a.mk_int()), m);
    expr_ref z(m.mk_const("z", a.mk_int()), m);
    expr_ref one(a.mk_int(1), m);
    rational big = rational::power_of_two(coefficient_bits);

    auto merge_cost = [&](rational const& coeff) {
        grobner g(m, dm);
        rational coeffs[] = { coeff, coeff };
        expr* monomials[] = { x, x };
        m.limit().reset_count();
        g.assert_eq_0(2, coeffs, monomials);
        return m.limit().count();
    };

    auto reduction_cost = [&](rational const& coeff) {
        grobner g(m, dm);
        g.set_weight(x, 1);
        rational source_coeffs[] = { rational(1), coeff };
        expr* source_monomials[] = { x, one };
        rational target_coeffs[] = { coeff, rational(1), rational(1) };
        expr* target_monomials[] = { x, y, z };
        g.assert_eq_0(2, source_coeffs, source_monomials);
        g.assert_eq_0(3, target_coeffs, target_monomials);
        m.limit().reset_count();
        g.compute_basis(1);
        return m.limit().count();
    };

    auto normalization_cost = [&](rational const& coeff) {
        grobner g(m, dm);
        rational coeffs[] = { rational(2), coeff };
        expr* monomials[] = { x, y };
        m.limit().reset_count();
        g.assert_eq_0(2, coeffs, monomials);
        return m.limit().count();
    };

    auto small_merge_cost = merge_cost(rational(1));
    ENSURE(merge_cost(big) > small_merge_cost);
    ENSURE(reduction_cost(big) > reduction_cost(rational(1)));
    ENSURE(normalization_cost(rational::power_of_two(512)) > normalization_cost(rational(1)));
}
