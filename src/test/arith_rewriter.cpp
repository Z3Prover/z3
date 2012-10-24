#include "arith_rewriter.h"
#include "bv_decl_plugin.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"

void tst_arith_rewriter() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_rewriter ar(m);
    arith_util au(m);
    expr_ref t1(m), t2(m), result(m);
    t1 = au.mk_numeral(rational(0),false);
    t2 = au.mk_numeral(rational(-3),false);
    expr* args[2] = { t1, t2 };
    ar.mk_mul(2, args, result);
    std::cout << mk_pp(result, m) << "\n";
}
