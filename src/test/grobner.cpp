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
    expr_ref v(m.mk_const("v", a.mk_int()), m);
    expr_ref w(m.mk_const("w", a.mk_int()), m);
    expr_ref one(a.mk_int(1), m);

    auto reduction_cost = [&](bool extra_monomials) {
        grobner g(m, dm);
        g.set_weight(x, 1);
        rational source_coeffs[] = { rational(1), rational(1), rational(1), rational(1) };
        expr* source_monomials[] = { x, one, y, z };
        rational target_coeffs[] = { rational(1), rational(1), rational(1), rational(1), rational(1) };
        expr* target_monomials[] = { x, y, z, v, w };
        g.assert_eq_0(extra_monomials ? 4 : 2, source_coeffs, source_monomials);
        g.assert_eq_0(5, target_coeffs, target_monomials);
        m.limit().reset_count();
        g.compute_basis(1);
        return m.limit().count();
    };

    ENSURE(reduction_cost(true) > reduction_cost(false));
}
