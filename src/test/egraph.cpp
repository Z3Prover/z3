/*++
Copyright (c) 2020 Microsoft Corporation

--*/

#include "util/util.h"
#include "util/timer.h"
#include "ast/euf/euf_egraph.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "ast/arith_decl_plugin.h"

static expr_ref mk_const(ast_manager& m, char const* name, sort* s) {
    return expr_ref(m.mk_const(symbol(name), s), m);
}

static expr_ref mk_app(char const* name, expr_ref const& arg, sort* s) {
    ast_manager& m = arg.m();
    func_decl_ref f(m.mk_func_decl(symbol(name), arg->get_sort(), s), m);
    return expr_ref(m.mk_app(f, arg.get()), m);
}

#if 0
static expr_ref mk_app(char const* name, expr_ref const& arg1, expr_ref const& arg2, sort* s) {
    ast_manager& m = arg1.m();
    func_decl_ref f(m.mk_func_decl(symbol(name), m.get_sort(arg1), m.get_sort(arg2), s), m);
    return expr_ref(m.mk_app(f, arg1.get(), arg2.get()), m);
}
#endif

static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    sort_ref S(m.mk_uninterpreted_sort(symbol("S")), m);
    expr_ref a = mk_const(m, "a", S);
    expr_ref fa = mk_app("f", a, S);
    expr_ref ffa = mk_app("f", fa, S);
    expr_ref fffa = mk_app("f", ffa, S);
    euf::enode* na = g.mk(a, 0, 0, nullptr); 
    euf::enode* nfa = g.mk(fa, 0, 1, &na);
    euf::enode* nffa = g.mk(ffa, 0, 1, &nfa);
    euf::enode* nfffa = g.mk(fffa, 0, 1, &nffa);
    std::cout << g << "\n";
    g.merge(na, nffa, nullptr);
    g.merge(na, nfffa, nullptr);
    std::cout << g << "\n";
    g.propagate();
    std::cout << g << "\n";
}

static void test2() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    sort_ref S(m.mk_uninterpreted_sort(symbol("S")), m);
    unsigned d = 100, w = 100;
    euf::enode_vector nodes, top_nodes;
    expr_ref_vector pinned(m);
    for (unsigned i = 0; i < w; ++i) {
        std::string xn("x");
        xn += std::to_string(i);
        expr_ref x = mk_const(m, xn.c_str(), S);
        euf::enode* n = g.mk(x, 0, 0, nullptr); 
        nodes.push_back(n);
        for (unsigned j = 0; j < d; ++j) {
            std::string f("f");
            f += std::to_string(j);
            x = mk_app(f.c_str(), x, S);
            n = g.mk(x, 0, 1, &n);
        }
        top_nodes.push_back(n);
        pinned.push_back(x);
    }
    std::cout << "merge\n";
    timer t;
    for (euf::enode* n : nodes) {
        g.merge(n, nodes[0], nullptr);
    }
    std::cout << "merged " << t.get_seconds() << "\n";
    g.propagate();
    std::cout << "propagated " << t.get_seconds() << "\n";
    for (euf::enode* n : top_nodes) {
        VERIFY(n->get_root() == top_nodes[0]->get_root());
    }    
}



static void test3() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    euf::egraph g(m);
    sort_ref I(a.mk_int(), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref x = mk_const(m, "x", I);
    expr_ref y = mk_const(m, "y", I);
    expr_ref z = mk_const(m, "z", I);
    expr_ref u = mk_const(m, "u", I);
    expr_ref fx = mk_app("f", x, I);
    expr_ref fy = mk_app("f", y, I);
    euf::enode* nx = g.mk(x, 0, 0, nullptr);
    euf::enode* ny = g.mk(y, 0, 0, nullptr);
    euf::enode* nz = g.mk(z, 0, 0, nullptr);
    euf::enode* nu = g.mk(u, 0, 0, nullptr);
    euf::enode* n0 = g.mk(zero, 0, 0, nullptr);
    euf::enode* n1 = g.mk(one, 0, 0, nullptr);
    euf::enode* nfx = g.mk(fx, 0, 1, &nx);
    euf::enode* nfy = g.mk(fy, 0, 1, &ny);
    int justifications[5] = { 1, 2, 3, 4, 5 };
    g.merge(nfx, n0, justifications + 0);
    g.merge(nfy, n1, justifications + 1);
    g.merge(nx,  nz, justifications + 2);
    g.merge(nx,  nu, justifications + 3);
    g.propagate();
    SASSERT(!g.inconsistent());
    g.merge(nx, ny, justifications + 4);
    std::cout << g << "\n";
    g.propagate();
    std::cout << g << "\n";
    SASSERT(g.inconsistent());
    ptr_vector<int> js;
    g.begin_explain();
    g.explain<int>(js);
    g.end_explain();
    for (int* j : js) 
        std::cout << "conflict: " << *j << "\n";
}

void tst_egraph() {
    enable_trace("euf");
    test3();
    test1();
    test2();
}
