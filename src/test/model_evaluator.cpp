#include "model.h"
#include "model_evaluator.h"
#include "model_pp.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "ast_pp.h"


void tst_model_evaluator() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);

    model mdl(m);

    sort* sI = a.mk_int();

    sort* dom[2] = { sI, m.mk_bool_sort() };
    func_decl_ref f(m.mk_func_decl(symbol("f"), 2, dom, sI), m);
    func_decl_ref g(m.mk_func_decl(symbol("g"), 2, dom, sI), m);
    func_decl_ref h(m.mk_func_decl(symbol("h"), 2, dom, sI), m);
    func_decl_ref F(m.mk_func_decl(symbol("F"), 2, dom, sI), m);
    func_decl_ref G(m.mk_func_decl(symbol("G"), 2, dom, sI), m);
    expr_ref vI0(m.mk_var(0, sI), m);
    expr_ref vI1(m.mk_var(1, sI), m);
    expr_ref vB0(m.mk_var(0, m.mk_bool_sort()), m);
    expr_ref vB1(m.mk_var(1, m.mk_bool_sort()), m);
    expr_ref vB2(m.mk_var(2, m.mk_bool_sort()), m);
    expr_ref f01(m.mk_app(f, vI0, vB1), m);
    expr_ref g01(m.mk_app(g, vI0, vB1), m);
    expr_ref h01(m.mk_app(h, vI0, vB1), m);
    func_interp* fi = alloc(func_interp, m, 2);
    func_interp* gi = alloc(func_interp, m, 2);
    func_interp* hi = alloc(func_interp, m, 2);
    hi->set_else(m.mk_ite(vB1, m.mk_app(f, vI0, vB1), m.mk_app(g, vI0, vB1)));
    mdl.register_decl(h, hi);
    

    model_evaluator eval(mdl);

    expr_ref e(m), v(m);

    {
        symbol nI("N");
        fi->set_else(m.mk_ite(m.mk_exists(1, &sI, &nI, a.mk_le(vI0, m.mk_app(F, vI1, vB2))), vI0, a.mk_int(1)));
        gi->set_else(m.mk_ite(m.mk_exists(1, &sI, &nI, a.mk_le(vI0, m.mk_app(G, vI1, vB2))), a.mk_int(2), vI0));
        mdl.register_decl(g, gi);
        mdl.register_decl(f, fi);
        model_pp(std::cout, mdl);
        e = m.mk_app(h, vI0, vB1);
        eval(e, v);
        std::cout << e << " " << v << "\n";
    }

    {
        fi->set_else(m.mk_app(F, vI0, vB1));
        gi->set_else(m.mk_app(G, vI0, vB1));
        mdl.register_decl(g, gi);
        mdl.register_decl(h, hi);
        model_pp(std::cout, mdl);
        e = m.mk_app(h, vI0, vB1);
        eval(e, v);
        std::cout << e << " " << v << "\n";
    }
    
}
