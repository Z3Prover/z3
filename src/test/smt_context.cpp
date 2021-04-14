
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "smt/smt_context.h"
#include "ast/reg_decl_plugins.h"

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
}
