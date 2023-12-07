/*++
Copyright (c) 2023 Microsoft Corporation

--*/

#include "util/util.h"
#include "util/timer.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_bv_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include <iostream>

static unsigned s_var = 0;
static euf::enode* get_node(euf::egraph& g, bv_util& b, expr* e) {
    auto* n = g.find(e);
    if (n)
        return n;
    euf::enode_vector args;
    for (expr* arg : *to_app(e))
        args.push_back(get_node(g, b, arg));
    n = g.mk(e, 0, args.size(), args.data());
    g.add_th_var(n, s_var++, b.get_family_id());
    return n;
}

// align slices, and propagate extensionality
static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::bv_plugin, g));
    bv_util bv(m);
    sort_ref u32(bv.mk_sort(32), m);

    expr_ref x(m.mk_const("x", u32), m);
    expr_ref y(m.mk_const("y", u32), m);
    expr_ref x3(bv.mk_extract(31, 16, x), m);
    expr_ref x2(bv.mk_extract(15, 8, x), m);
    expr_ref x1(bv.mk_extract(7, 0, x), m);
    expr_ref y3(bv.mk_extract(31, 24, y), m);
    expr_ref y2(bv.mk_extract(23, 8, y), m);
    expr_ref y1(bv.mk_extract(7, 0, y), m);
    expr_ref xx(bv.mk_concat(x1, bv.mk_concat(x2, x3)), m);
    expr_ref yy(bv.mk_concat(y1, bv.mk_concat(y2, y3)), m);
    auto* nx = get_node(g, bv, xx);
    auto* ny = get_node(g, bv, yy);
    TRACE("bv", tout << "before merge\n" << g << "\n");
    g.merge(nx, ny, nullptr);
    TRACE("bv", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("bv", tout << "after propagate\n" << g << "\n");
    std::cout << g << "\n";
    SASSERT(nx->get_root() == ny->get_root());
}

// propagate values down
static void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::bv_plugin, g));
    bv_util bv(m);
    sort_ref u32(bv.mk_sort(32), m);

    expr_ref x(m.mk_const("x", u32), m);
    expr_ref x3(bv.mk_extract(31, 16, x), m);
    expr_ref x2(bv.mk_extract(15, 8, x), m);
    expr_ref x1(bv.mk_extract(7, 0, x), m);
    expr_ref xx(bv.mk_concat(x1, bv.mk_concat(x2, x3)), m);
    g.merge(get_node(g, bv, xx), get_node(g, bv, bv.mk_numeral((1 << 27) + (1 << 17) + (1 << 3), 32)), nullptr);
    g.propagate();
    SASSERT(get_node(g, bv, x1)->get_root()->interpreted());
    SASSERT(get_node(g, bv, x2)->get_root()->interpreted());
    SASSERT(get_node(g, bv, x3)->get_root()->interpreted());
    SASSERT(get_node(g, bv, x)->get_root()->interpreted());
}


// propagate values up
static void test3() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::bv_plugin, g));
    bv_util bv(m);
    sort_ref u32(bv.mk_sort(32), m);

    expr_ref x(m.mk_const("x", u32), m);
    expr_ref x3(bv.mk_extract(31, 16, x), m);
    expr_ref x2(bv.mk_extract(15, 8, x), m);
    expr_ref x1(bv.mk_extract(7, 0, x), m);
    expr_ref xx(bv.mk_concat(bv.mk_concat(x1, x2), x3), m);
    expr_ref y(m.mk_const("y", u32), m);
    g.merge(get_node(g, bv, xx), get_node(g, bv, y), nullptr);
    g.merge(get_node(g, bv, x1), get_node(g, bv, bv.mk_numeral(2, 8)), nullptr);
    g.merge(get_node(g, bv, x2), get_node(g, bv, bv.mk_numeral(8, 8)), nullptr);
    g.propagate();
    SASSERT(get_node(g, bv, bv.mk_concat(x1, x2))->get_root()->interpreted());
    SASSERT(get_node(g, bv, x1)->get_root()->interpreted());
    SASSERT(get_node(g, bv, x2)->get_root()->interpreted());
}

// propagate extract up
static void test4() {
    // concat(a, x[J]), a = x[I] => x[IJ] = concat(x[I],x[J])
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::bv_plugin, g));
    bv_util bv(m);
    sort_ref u32(bv.mk_sort(32), m);
    sort_ref u8(bv.mk_sort(8), m);
    sort_ref u16(bv.mk_sort(16), m);
    expr_ref a(m.mk_const("a", u8), m);
    expr_ref x(m.mk_const("x", u32), m);
    expr_ref y(m.mk_const("y", u16), m);
    expr_ref x1(bv.mk_extract(15, 8, x), m);
    expr_ref x2(bv.mk_extract(23, 16, x), m);
    g.merge(get_node(g, bv, bv.mk_concat(a, x2)), get_node(g, bv, y), nullptr);
    g.merge(get_node(g, bv, x1), get_node(g, bv, a), nullptr);
    g.propagate();
    TRACE("bv", tout << g << "\n");
    SASSERT(get_node(g, bv, bv.mk_extract(23, 8, x))->get_root() == get_node(g, bv, y)->get_root());
}

// iterative slicing
static void test5() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::bv_plugin, g));
    bv_util bv(m);
    sort_ref u32(bv.mk_sort(32), m);

    expr_ref x(m.mk_const("x", u32), m);
    expr_ref x1(bv.mk_extract(31, 4, x), m);
    expr_ref x2(bv.mk_extract(27, 0, x), m);
    auto* nx = get_node(g, bv, x1);
    auto* ny = get_node(g, bv, x2);
    TRACE("bv", tout << "before merge\n" << g << "\n");
    g.merge(nx, ny, nullptr);
    TRACE("bv", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("bv", tout << "after propagate\n" << g << "\n");
    std::cout << g << "\n";
}

// iterative slicing
static void test6() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    g.add_plugin(alloc(euf::bv_plugin, g));
    bv_util bv(m);
    sort_ref u32(bv.mk_sort(32), m);

    expr_ref x(m.mk_const("x", u32), m);
    expr_ref x1(bv.mk_extract(31, 3, x), m);
    expr_ref x2(bv.mk_extract(28, 0, x), m);
    auto* nx = get_node(g, bv, x1);
    auto* ny = get_node(g, bv, x2);
    TRACE("bv", tout << "before merge\n" << g << "\n");
    g.merge(nx, ny, nullptr);
    TRACE("bv", tout << "before propagate\n" << g << "\n");
    g.propagate();
    TRACE("bv", tout << "after propagate\n" << g << "\n");
    std::cout << g << "\n";
}


void tst_euf_bv_plugin() {
    enable_trace("bv");
    enable_trace("plugin");
    test6();
    return;
    test1();
    test2();
    test3();
    test4();
    test5();
    test6();
}
