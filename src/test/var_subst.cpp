/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    var_subst.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-12.

Revision History:

--*/
#include "ast/rewriter/var_subst.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/reg_decl_plugins.h"

namespace find_q {
    struct proc {
        quantifier * m_q;
        proc():m_q(nullptr) {}
        void operator()(var * n) {}
        void operator()(app * n) {}
        void operator()(quantifier * n) { m_q = n; }
    };
};

quantifier * find_quantifier(expr * n) {
    find_q::proc p;
    for_each_expr(p, n);
    return p.m_q;
}

void tst_instantiate(ast_manager & m, expr * f) {
    if (is_quantifier(f)) {
        tst_instantiate(m, to_quantifier(f)->get_expr());
        return;
    }
    quantifier * q = find_quantifier(f);
    if (q) {
        expr_ref_vector cnsts(m);
        for (unsigned i = 0; i < q->get_num_decls(); i++) 
            cnsts.push_back(m.mk_fresh_const("a", q->get_decl_sort(i)));
        expr_ref r = instantiate(m, q, cnsts.c_ptr());
        TRACE("var_subst", tout << "quantifier:\n" << mk_pp(q, m) << "\nresult:\n" << mk_pp(r, m) << "\n";);
    }
}

void tst_subst(ast_manager& m) {
    func_decl_ref p(m);
    sort_ref s(m);
    obj_ref<var, ast_manager> x(m), y(m), z(m), u(m), v(m);
    expr_ref e1(m), e2(m), e3(m);
    expr_ref t1(m), t2(m), t3(m);
    s = m.mk_uninterpreted_sort(symbol("S"));
    sort* ss[2] = { s.get(), s.get() };
    symbol names[2] = { symbol("y"), symbol("x") };
    p = m.mk_func_decl(symbol("p"), 2, ss, m.mk_bool_sort());
    x = m.mk_var(0, s);
    y = m.mk_var(1, s);
    z = m.mk_var(2, s);
    u = m.mk_var(3, s);
    v = m.mk_var(4, s);
    e1 = m.mk_and(m.mk_app(p, x.get(), y.get()), m.mk_app(p, z.get(), u.get()));
    e2 = m.mk_forall(1, ss, names, e1);
    t1 = m.mk_forall(1, ss, names, 
                     m.mk_and(m.mk_app(p, x.get(), z.get()), m.mk_app(p, y.get(), u.get())));
    t2 = m.mk_forall(2, ss, names, 
                     m.mk_and(m.mk_app(p, x.get(), y.get()), m.mk_app(p, u.get(), z.get())));
    
    var_subst subst(m);
    expr_ref_vector sub1(m);
    sub1.push_back(x);
    sub1.push_back(y);
    // replace #1 -> #2, #2 -> #1
    e3 = subst(e2, 2, sub1.c_ptr());
    std::cout << mk_pp(e2, m) << "\n";
    std::cout << mk_pp(e3, m) << "\n";
    std::cout << mk_pp(t1, m) << "\n";
    ENSURE(e3.get() == t1.get());

    // replace #2 -> #3, #3 -> #2
    e2 = m.mk_forall(2, ss, names, e1);
    e3 = subst(e2, 2, sub1.c_ptr());
    std::cout << mk_pp(e2, m) << "\n";
    std::cout << mk_pp(e3, m) << "\n";
    std::cout << mk_pp(t2, m) << "\n";
    ENSURE(e3.get() == t2.get());

}

void tst_var_subst() {
    ast_manager m;
    reg_decl_plugins(m);
    tst_subst(m);
}
