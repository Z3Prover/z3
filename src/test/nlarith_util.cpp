#include "nlarith_util.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"

void tst_nlarith_util() {
    ast_manager M;
    reg_decl_plugins(M);
    arith_util A(M);
    sort_ref R(A.mk_real(), M);
    app_ref one(A.mk_numeral(rational(1), false), M);
    app_ref two(A.mk_numeral(rational(2), false), M);
    app_ref ten(A.mk_numeral(rational(10), false), M);
    app_ref x(M.mk_const(symbol("x"), R), M);
    app_ref y(M.mk_const(symbol("y"), R), M);
    app_ref z(M.mk_const(symbol("z"), R), M);

    expr_ref p1(A.mk_le(A.mk_add(A.mk_mul(x,x,y), y), one), M);
    expr_ref p2(A.mk_le(A.mk_add(A.mk_mul(x,x,y), z), one), M);

    enable_trace("nlarith");
    nlarith::util u(M);
    nlarith::branch_conditions bc(M);


    expr_ref_vector preds(M), branches(M);
    vector<expr_ref_vector> substs;
    expr* lits[2] = { p1.get(), p2.get() };
    if (!u.create_branches(x.get(), 2, lits, bc)) {
        std::cout << "Failed to create branches\n";
        return;
    }
    
    for (unsigned i = 0; i < preds.size(); ++i) {
        std::cout << "Pred: " << mk_pp(preds[i].get(), M) << "\n";
    }

    for (unsigned i = 0; i < branches.size(); ++i) {
        std::cout << "Branch:\n" << mk_pp(branches[i].get(), M) << "\n";
        for (unsigned j = 0; j < substs[i].size(); ++j) {
            std::cout << mk_pp(preds[j].get(), M) << " |-> " 
                      << mk_pp(substs[i][j].get(), M) << "\n";
        }
    }

}
