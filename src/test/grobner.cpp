#include "math/grobner/grobner.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "util/debug.h"

void tst_grobner() {
    ast_manager m;
    reg_decl_plugins(m);
    v_dependency_manager dm;
    arith_util a(m);
    expr_ref x(m.mk_const("x", a.mk_int()), m);
    expr_ref y(m.mk_const("y", a.mk_int()), m);
    expr_ref z(m.mk_const("z", a.mk_int()), m);
    expr_ref one(a.mk_int(1), m);

    auto reduction_cost = [&](rational const& coeff) {
        grobner g(m, dm);
        g.set_weight(x, 1);
        rational source_coeffs[] = { rational(1), coeff };
        expr* source_monomials[] = { x, y };
        rational target_coeffs[] = { rational(1), rational(1), rational(1) };
        expr* target_monomials[] = { x, one, z };
        g.assert_eq_0(2, source_coeffs, source_monomials);
        g.assert_eq_0(3, target_coeffs, target_monomials);
        m.limit().reset_count();
        g.compute_basis(1);
        return m.limit().count();
    };

    rational large(1);
    for (unsigned i = 0; i < 1024; ++i)
        large *= rational(2);
    ENSURE(reduction_cost(large) > reduction_cost(rational(1)));
}
