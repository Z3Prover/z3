
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/expr_substitution.h"
#include "smt/params/smt_params.h"
#include "ast/substitution/substitution.h"
#include "ast/substitution/unifier.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include <iostream>

expr* mk_bv_xor(bv_util& bv, expr* a, expr* b) {
    expr* args[2];
    args[0] = a;
    args[1] = b;
    return bv.mk_bv_xor(2, args);
}

expr* mk_bv_and(bv_util& bv, expr* a, expr* b) {
    expr* args[2];
    args[0] = a;
    args[1] = b;
    ast_manager& m = bv.get_manager();
    return m.mk_app(bv.get_family_id(), OP_BAND, 2, args);
}

void tst_expr_substitution() {
    memory::initialize(0);
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);

    expr_ref a(m), b(m), c(m), d(m);
    expr_ref x(m);
    expr_ref   new_a(m);
    proof_ref  pr(m);
    x = m.mk_const(symbol("x"), bv.mk_sort(8));
    a = mk_bv_and(bv, mk_bv_xor(bv, x,bv.mk_numeral(8,8)), mk_bv_xor(bv,x,x));
    b = x;
    c = bv.mk_bv_sub(x, bv.mk_numeral(4, 8));

    expr_substitution subst(m);
    th_rewriter   rw(m);

    std::cout << mk_pp(c, m) << "\n";

    // normalizing c does not help.
    rw(c, d, pr);

    std::cout << mk_pp(d, m) << "\n";


// This portion diverges. It attempts to replace x by (bvadd #xfc x), which contains x.
//    subst.insert(b, d);

//    std::cout << mk_pp(a, m) << "\n";
//    rw.set_substitution(&subst);
   
//    enable_trace("th_rewriter_step");
//    rw(a, new_a, pr);

//    std::cout << mk_pp(new_a, m) << "\n";
    
}
