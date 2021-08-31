
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "model/model2expr.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "model/model_smt2_pp.h"
#include "ast/reg_decl_plugins.h"

void tst_model2expr() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);

    ptr_vector<sort> ints;
    ints.push_back(a.mk_int());
    ints.push_back(a.mk_int());
    ints.push_back(a.mk_int());

    func_decl_ref p(m), q(m), x(m);
    p = m.mk_func_decl(symbol("p"), 2, ints.data(), a.mk_int());
    q = m.mk_func_decl(symbol("q"), 2, ints.data(), a.mk_int());
    x = m.mk_const_decl(symbol("x"), a.mk_int());
    expr_ref n0(m), n1(m), n2(m);
    n0 = a.mk_numeral(rational(0), true);
    n1 = a.mk_numeral(rational(1), true);
    n2 = a.mk_numeral(rational(2), true);

    model_ref md = alloc(model, m);
    func_interp* fip = alloc(func_interp, m, 2);
    func_interp* fiq = alloc(func_interp, m, 2);
    expr_ref_vector args(m);
    args.push_back(n1);
    args.push_back(n2);
    fip->insert_entry(args.data(), n1);
    fiq->insert_entry(args.data(), n1);
    args[0] = n0;
    args[1] = n1;
    fip->insert_entry(args.data(), n2);
    fiq->insert_entry(args.data(), n2);
   
    fip->set_else(n0);

    md->register_decl(x, a.mk_numeral(rational(0), true));
    md->register_decl(p, fip); // full
    md->register_decl(q, fiq); // partial

    expr_ref result(m);
    model2expr(md, result);
    
    model_smt2_pp(std::cout, m, *md,  0);
    std::cout << mk_pp(result, m) << "\n";
}
