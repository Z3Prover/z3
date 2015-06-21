
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "factor_rewriter.h"
#include "bv_decl_plugin.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"

void tst_factor_rewriter() {
    ast_manager m;
    reg_decl_plugins(m);

    factor_rewriter_star fw(m);
    arith_util a(m);    
    expr_ref fml1(m), fml2(m);
    expr_ref z(m.mk_const(symbol("z"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2),false),m);
    expr_ref zero(a.mk_numeral(rational(0),false),m);    
    fml1 = a.mk_le(zero, a.mk_mul(two, z, z));
    fw(fml1, fml2);
    std::cout << mk_pp(fml1, m) << " -> " << mk_pp(fml2, m) << "\n";
}
