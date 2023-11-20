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

static euf::enode* get_node(euf::egraph& g, expr* e) {
    auto* n = g.find(e);
    if (n)
        return n;
    euf::enode_vector args;
    for (expr* arg : *to_app(e))
        args.push_back(get_node(g, arg));
    return g.mk(e, 0, args.size(), args.data());
}

// 
static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugins();
    arith_util a(m);
    sort_ref I(a.mk_int(), m);

    expr_ref x(m.mk_const("x", I), m);
    expr_ref y(m.mk_const("y", I), m);
    auto* nx = get_node(g, a.mk_add(a.mk_add(y, y), a.mk_add(x, x)));
    auto* ny = get_node(g, a.mk_add(a.mk_add(y, x), x));
    TRACE("plugin", tout << "before merge\n" << g << "\n");
    g.merge(nx, ny, nullptr);

    TRACE("plugin", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("plugin", tout << "after propagate\n" << g << "\n");
    g.merge(get_node(g, a.mk_add(x, a.mk_add(y, y))), get_node(g, a.mk_add(y, x)), nullptr);
    g.propagate();
    std::cout << g << "\n";
}

static void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugins();
    arith_util a(m);
    sort_ref I(a.mk_int(), m);

    expr_ref x(m.mk_const("x", I), m);
    expr_ref y(m.mk_const("y", I), m);
    auto* nx = get_node(g, a.mk_add(x, y));
    auto* ny = get_node(g, a.mk_add(y, x));
    TRACE("plugin", tout << "before merge\n" << g << "\n");
    g.merge(nx, get_node(g, x), nullptr);
    g.merge(ny, get_node(g, y), nullptr);

    TRACE("plugin", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("plugin", tout << "after propagate\n" << g << "\n");
    SASSERT(get_node(g, x)->get_root() == get_node(g, y)->get_root());
    g.merge(get_node(g, a.mk_add(x, a.mk_add(y, y))), get_node(g, a.mk_add(y, x)), nullptr);
    g.propagate();
    std::cout << g << "\n";
}

void tst_euf_arith_plugin() {
    enable_trace("plugin");
    test1();
    test2();
}
