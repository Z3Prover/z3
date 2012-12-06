#include "memory_manager.h"
#include "smt_params.h"
#include "ast.h"
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "smt_context.h"
#include "reg_decl_plugins.h"

void tst_check_assumptions()
{
    memory::initialize(0);
    smt_params params;
    ast_manager mgr;
    reg_decl_plugins(mgr);

    sort_ref b(mgr.mk_bool_sort(), mgr);
    func_decl_ref pPred(mgr.mk_func_decl(symbol("p"), 0, static_cast<sort * const *>(0), b), mgr);
    func_decl_ref qPred(mgr.mk_func_decl(symbol("q"), 0, static_cast<sort * const *>(0), b), mgr);
    func_decl_ref rPred(mgr.mk_func_decl(symbol("r"), 0, static_cast<sort * const *>(0), b), mgr);

    app_ref p(mgr.mk_app(pPred,0,static_cast<expr * const *>(0)), mgr);
    app_ref q(mgr.mk_app(qPred,0,static_cast<expr * const *>(0)), mgr);
    app_ref r(mgr.mk_app(rPred,0,static_cast<expr * const *>(0)), mgr);
    app_ref pOqOr(mgr.mk_or(p,q,r), mgr);

    app_ref np(mgr.mk_not(p), mgr);
    app_ref nq(mgr.mk_not(q), mgr);
    app_ref nr(mgr.mk_not(r), mgr);

    smt::context ctx(mgr, params);
    ctx.assert_expr(pOqOr);

    expr * npE = np.get();
    lbool res1 = ctx.check(1, &npE);
    SASSERT(res1==l_true);

    ctx.assert_expr(npE);


    expr * assumpt[] = { nq.get(), nr.get() };
    //here it should crash
    ctx.check(2, assumpt);
}

