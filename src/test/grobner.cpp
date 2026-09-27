#include "math/grobner/grobner.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"

void tst_grobner() {
    constexpr unsigned coefficient_bits = 1024;
    ast_manager m;
    reg_decl_plugins(m);
    v_dependency_manager dm;
    grobner g(m, dm);
    arith_util a(m);
    expr_ref x(m.mk_const("x", a.mk_int()), m);
    expr_ref y(m.mk_const("y", a.mk_int()), m);
    expr_ref z(m.mk_const("z", a.mk_int()), m);
    expr_ref one(a.mk_int(1), m);
    rational big = rational::power_of_two(coefficient_bits);

    g.set_weight(x, 1);

    rational merge_coeffs[] = { big, big };
    expr* merge_monomials[] = { x, x };
    m.limit().reset_count();
    g.assert_eq_0(2, merge_coeffs, merge_monomials);
    ENSURE(m.limit().count() > 2);

    rational source_coeffs[] = { rational(1), big };
    expr* source_monomials[] = { x, one };
    rational target_coeffs[] = { big, rational(1), rational(1) };
    expr* target_monomials[] = { x, y, z };
    g.assert_eq_0(2, source_coeffs, source_monomials);
    g.assert_eq_0(3, target_coeffs, target_monomials);
    m.limit().reset_count();
    g.compute_basis(1);
    ENSURE(m.limit().count() > 6);
}
