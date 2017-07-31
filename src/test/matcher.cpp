/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    matcher.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-16.

Revision History:

--*/
#ifdef _WINDOWS
#include "ast/substitution/matcher.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"


void tst_match(ast_manager & m, app * t, app * i) {
    substitution s(m);
    s.reserve(2, 10); // reserving a big number of variables to be safe.

    matcher      match;
    std::cout << "Is " << mk_pp(i, m) << " an instance of " << mk_pp(t, m) << "\n";
    if (match(t, i, s)) {
        std::cout << "yes\n";
        s.display(std::cout);
    }
    else {
        std::cout << "no\n";
    }

    s.reset();
    
    if (t->get_decl() == i->get_decl()) {
        // trying to match the arguments of t and i
        std::cout << "Are the arguments of " << mk_pp(i, m) << " an instance of the arguments of " << mk_pp(t, m) << "\n";
        unsigned num_args = t->get_num_args();
        unsigned j;
        for (j = 0; j < num_args; j++) {
            if (!match(t->get_arg(j), i->get_arg(j), s))
                break;
        }
        if (j == num_args) {
            std::cout << "yes\n";
            s.display(std::cout);
            
            // create some dummy term to test for applying the substitution.
            sort_ref S(          m.mk_uninterpreted_sort(symbol("S")),    m);
            sort * domain[3]   = {S, S, S};
            func_decl_ref r(     m.mk_func_decl(symbol("r"), 3, domain, S), m);
            expr_ref x1(         m.mk_var(0, S), m);
            expr_ref x2(         m.mk_var(1, S), m);
            expr_ref x3(         m.mk_var(2, S), m);
            app_ref  rxyzw(      m.mk_app(r, x1.get(), x2.get(), x3.get()), m);
            expr_ref result(m);
            unsigned deltas[2] = {0,0};
            s.apply(2, deltas, expr_offset(rxyzw, 0), result);
            std::cout << "applying substitution to\n" << mk_pp(rxyzw,m) << "\nresult:\n" << mk_pp(result,m) << "\n";
        }
        else {
            std::cout << "no\n";
        }
    }
    
    std::cout << "\n";
}

void tst1() {
    ast_manager m;
    reg_decl_plugins(m);
    sort_ref s(          m.mk_uninterpreted_sort(symbol("S")),    m);
    func_decl_ref g(     m.mk_func_decl(symbol("g"), s, s), m);
    func_decl_ref h(     m.mk_func_decl(symbol("h"), s, s), m);
    sort * domain[2]   = {s, s};
    func_decl_ref f(     m.mk_func_decl(symbol("f"), 2, domain, s), m);
    app_ref a(           m.mk_const(symbol("a"), s), m);
    app_ref b(           m.mk_const(symbol("b"), s), m);
    expr_ref x(          m.mk_var(0, s), m);
    expr_ref y(          m.mk_var(1, s), m);
    app_ref gx(          m.mk_app(g, x), m);
    app_ref fgx_x(       m.mk_app(f, gx.get(), x.get()), m);
    app_ref ha(          m.mk_app(h, a.get()), m);
    app_ref gha(         m.mk_app(g, ha.get()), m);
    app_ref fgha_ha(     m.mk_app(f, gha.get(), ha.get()), m);
    tst_match(m, fgx_x, fgha_ha);

    app_ref fgha_gha(    m.mk_app(f, gha.get(), gha.get()), m);
    tst_match(m, fgx_x, fgha_gha);

    app_ref fxy(         m.mk_app(f, x.get(), y.get()), m);
    app_ref fyx(         m.mk_app(f, y.get(), x.get()), m);
    tst_match(m, fxy, fyx);

    app_ref fygx(        m.mk_app(f, y.get(), gx.get()), m);
    tst_match(m, fxy, fygx);

    tst_match(m, fygx, fxy);

}



void tst_matcher() {
    tst1();
}
#else
void tst_matcher() {
}
#endif
