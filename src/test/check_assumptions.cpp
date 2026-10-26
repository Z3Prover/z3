
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "util/memory_manager.h"
#include "params/smt_params.h"
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "smt/smt_context.h"
#include "ast/reg_decl_plugins.h"

static void check_open_assumptions(ast_manager& m, smt_params& params) {
    sort_ref u(m.mk_uninterpreted_sort(symbol("U")), m);
    sort* domain[] = { u, u };
    func_decl_ref p(m.mk_func_decl(symbol("open-p"), 2, domain, m.mk_bool_sort()), m);
    expr_ref x(m.mk_var(1, u), m), y(m.mk_var(0, u), m);
    expr_ref a(m.mk_const("a", u), m), b(m.mk_const("b", u), m);
    expr_ref open(m.mk_app(p.get(), x.get(), y.get()), m);
    expr_ref pa(m.mk_app(p.get(), a.get(), b.get()), m), pb(m.mk_app(p.get(), b.get(), a.get()), m);
    expr_ref na(m.mk_not(pa), m), nb(m.mk_not(pb), m);
    expr_ref fml(m.mk_or(na, nb), m);
    smt::context ctx(m, params);
    ctx.assert_expr(fml);
    expr* asms[] = { open };
    VERIFY(ctx.check(1, asms) == l_false);
    VERIFY(ctx.get_unsat_core_size() == 2);
    for (unsigned i = 0; i < 2; ++i) {
        expr* e = ctx.get_unsat_core_expr(i);
        VERIFY(e == pa || e == pb);
    }
    VERIFY(ctx.check() == l_true);
    VERIFY(ctx.check(1, asms) == l_false);
}

void tst_check_assumptions()
{
    memory::initialize(0);
    smt_params params;
    ast_manager mgr;
    reg_decl_plugins(mgr);
    check_open_assumptions(mgr, params);

    sort_ref b(mgr.mk_bool_sort(), mgr);
    func_decl_ref pPred(mgr.mk_func_decl(symbol("p"), 0, static_cast<sort * const *>(nullptr), b), mgr);
    func_decl_ref qPred(mgr.mk_func_decl(symbol("q"), 0, static_cast<sort * const *>(nullptr), b), mgr);
    func_decl_ref rPred(mgr.mk_func_decl(symbol("r"), 0, static_cast<sort * const *>(nullptr), b), mgr);

    app_ref p(mgr.mk_app(pPred,0,static_cast<expr * const *>(nullptr)), mgr);
    app_ref q(mgr.mk_app(qPred,0,static_cast<expr * const *>(nullptr)), mgr);
    app_ref r(mgr.mk_app(rPred,0,static_cast<expr * const *>(nullptr)), mgr);
    app_ref pOqOr(mgr.mk_or(p,q,r), mgr);

    app_ref np(mgr.mk_not(p), mgr);
    app_ref nq(mgr.mk_not(q), mgr);
    app_ref nr(mgr.mk_not(r), mgr);

    smt::context ctx(mgr, params);
    ctx.assert_expr(pOqOr);

    expr * npE = np.get();
    lbool res1 = ctx.check(1, &npE);
    VERIFY(res1 == l_true);

    ctx.assert_expr(npE);


    expr * assumpt[] = { nq.get(), nr.get() };
    //here it should crash
    ctx.check(2, assumpt);
}
