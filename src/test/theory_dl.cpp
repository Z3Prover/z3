#include "smt_context.h"
#include "dl_decl_plugin.h"
#include "ast_pp.h"
#include "model_v2_pp.h"
#include "reg_decl_plugins.h"

void tst_theory_dl() {
    ast_manager m;
    smt_params params;
    params.m_model = true;
    datalog::dl_decl_util u(m);
    smt::context ctx(m, params);
    reg_decl_plugins(m);
    expr_ref a(m), b(m), c(m);
    sort_ref s(m);
    s = u.mk_sort(symbol("S"),111);
    a = m.mk_const(symbol("a"),s);
    b = m.mk_const(symbol("b"),s);
    ctx.assert_expr(u.mk_lt(a, b));
    ctx.check();
    ref<model> md;
    ctx.get_model(md);
    model_v2_pp(std::cout, *md.get());


    c = m.mk_const(symbol("c"),s);
    ctx.assert_expr(u.mk_lt(b, c));
    ctx.check();
    ctx.get_model(md);
    model_v2_pp(std::cout, *md.get());

    ctx.assert_expr(u.mk_lt(c, a));
    std::cout << ctx.check() << "\n";

    
}
