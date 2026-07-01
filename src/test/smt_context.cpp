
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "smt/smt_context.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"

void tst_smt_context()
{
    smt_params params;

    ast_manager m;
    reg_decl_plugins(m);

    smt::context ctx(m, params);

    app_ref a1(m.mk_const(symbol("a"), m.mk_bool_sort()), m);
    app_ref b1(m.mk_const(symbol("b"), m.mk_bool_sort()), m);
    app_ref c1(m.mk_const(symbol("c"), m.mk_bool_sort()), m);
    app_ref na1(m.mk_not(a1), m);
    ctx.assert_expr(na1);

    app_ref b_or_c(m.mk_or(c1.get(), b1.get()), m);
    ctx.assert_expr(b_or_c);

    {
        app_ref nc(m.mk_not(c1), m);
        ptr_vector<expr> assumptions;
        assumptions.push_back(nc.get());

        ctx.check(assumptions.size(), assumptions.data());
    }

    ctx.check();

    {
        arith_util a(m);
        expr_ref x(m.mk_var(2, a.mk_int()), m);
        expr_ref x4(m.mk_var(1, a.mk_int()), m);
        expr_ref y(m.mk_var(0, a.mk_int()), m);
        expr_ref zero(a.mk_int(0), m);
        expr_ref two(a.mk_int(2), m);
        expr_ref_vector conjs(m);
        conjs.push_back(a.mk_gt(x, y));
        conjs.push_back(a.mk_gt(zero, x4));
        conjs.push_back(a.mk_gt(zero, a.mk_uminus(y)));
        conjs.push_back(a.mk_lt(zero, a.mk_uminus(a.mk_mul(two, y))));
        expr_ref body(m.mk_and(conjs), m);

        sort* y_sort = a.mk_int();
        symbol y_name("y");
        body = m.mk_exists(1, &y_sort, &y_name, body);

        sort* sorts[2] = { a.mk_int(), a.mk_int() };
        symbol names[2] = { symbol("x"), symbol("x4") };
        expr_ref q(m.mk_forall(2, sorts, names, body), m);

        smt::context qctx(m, params);
        qctx.assert_expr(q);
        VERIFY(l_false == qctx.check());
    }
}
