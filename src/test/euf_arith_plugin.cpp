/*++
Copyright (c) 2023 Microsoft Corporation

--*/

#include "util/util.h"
#include "util/timer.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_arith_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <iostream>

unsigned s_var = 0;

static euf::enode* get_node(euf::egraph& g, arith_util& a, expr* e) {
    auto* n = g.find(e);
    if (n)
        return n;
    euf::enode_vector args;
    for (expr* arg : *to_app(e))
        args.push_back(get_node(g, a, arg));
    n = g.mk(e, 0, args.size(), args.data());
    g.add_th_var(n, s_var++, a.get_family_id());
    return n;
}

// 
static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::arith_plugin, g));
    arith_util a(m);
    sort_ref I(a.mk_int(), m);

    expr_ref x(m.mk_const("x", I), m);
    expr_ref y(m.mk_const("y", I), m);
    auto* nx = get_node(g, a, a.mk_add(a.mk_add(y, y), a.mk_add(x, x)));
    auto* ny = get_node(g, a, a.mk_add(a.mk_add(y, x), x));
    TRACE("plugin", tout << "before merge\n" << g << "\n");
    g.merge(nx, ny, nullptr);

    TRACE("plugin", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("plugin", tout << "after propagate\n" << g << "\n");
    g.merge(get_node(g, a, a.mk_add(x, a.mk_add(y, y))), get_node(g, a, a.mk_add(y, x)), nullptr);
    g.propagate();
    std::cout << g << "\n";
}

static void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::arith_plugin, g));
    arith_util a(m);
    sort_ref I(a.mk_int(), m);

    expr_ref x(m.mk_const("x", I), m);
    expr_ref y(m.mk_const("y", I), m);
    auto* nxy = get_node(g, a, a.mk_add(x, y));
    auto* nyx = get_node(g, a, a.mk_add(y, x));
    auto* nx = get_node(g, a, x);
    auto* ny = get_node(g, a, y);
    
    TRACE("plugin", tout << "before merge\n" << g << "\n");
    g.merge(nxy, nx, nullptr);
    g.merge(nyx, ny, nullptr);
    TRACE("plugin", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("plugin", tout << "after propagate\n" << g << "\n");
    SASSERT(nx->get_root() == ny->get_root());
    g.merge(get_node(g, a, a.mk_add(x, a.mk_add(y, y))), get_node(g, a, a.mk_add(y, x)), nullptr);
    g.propagate();
    std::cout << g << "\n";
}

static void test3() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::arith_plugin, g));
    arith_util a(m);
    sort_ref I(a.mk_int(), m);

    expr_ref x(m.mk_const("x", I), m);
    expr_ref y(m.mk_const("y", I), m);
    auto* nxyy = get_node(g, a, a.mk_add(a.mk_add(x, y), y));
    auto* nyxx = get_node(g, a, a.mk_add(a.mk_add(y, x), x));
    auto* nx = get_node(g, a, x);
    auto* ny = get_node(g, a, y);
    g.merge(nxyy, nx, nullptr);
    g.merge(nyxx, ny, nullptr);
    TRACE("plugin", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("plugin", tout << "after propagate\n" << g << "\n");
    std::cout << g << "\n";
}

void tst_euf_arith_plugin() {
    enable_trace("plugin");
    test1();
    test2();
    test3();
}
