/*++
Copyright (c) 2020 Microsoft Corporation

--*/

#include "util/timer.h"
#include "ast/euf/euf_egraph.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"

static expr_ref mk_const(ast_manager& m, char const* name, sort* s) {
    return expr_ref(m.mk_const(symbol(name), s), m);
}

static expr_ref mk_app(char const* name, expr_ref const& arg, sort* s) {
    ast_manager& m = arg.m();
    func_decl_ref f(m.mk_func_decl(symbol(name), m.get_sort(arg), s), m);
    return expr_ref(m.mk_app(f, arg), m);
}

static expr_ref mk_app(char const* name, expr_ref const& arg1, expr_ref const& arg2, sort* s) {
    ast_manager& m = arg1.m();
    func_decl_ref f(m.mk_func_decl(symbol(name), m.get_sort(arg1), m.get_sort(arg2), s), m);
    return expr_ref(m.mk_app(f, arg1, arg2), m);
}

static void test1() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    sort_ref S(m.mk_uninterpreted_sort(symbol("S")), m);
    expr_ref a = mk_const(m, "a", S);
    expr_ref fa = mk_app("f", a, S);
    expr_ref ffa = mk_app("f", fa, S);
    expr_ref fffa = mk_app("f", ffa, S);
    euf::enode* na = g.mk(a, nullptr); 
    euf::enode* nfa = g.mk(fa, &na);
    euf::enode* nffa = g.mk(ffa, &nfa);
    euf::enode* nfffa = g.mk(fffa, &nffa);
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
        euf::enode* n = g.mk(x, nullptr); 
        nodes.push_back(n);
        for (unsigned j = 0; j < d; ++j) {
            std::string f("f");
            f += std::to_string(j);
            x = mk_app(f.c_str(), x, S);
            n = g.mk(x, &n);
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
        SASSERT(n->get_root() == top_nodes[0]->get_root());
    }    
}

static void test3() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph g(m);
    sort_ref S(m.mk_uninterpreted_sort(symbol("S")), m);

}

void tst_egraph() {
    enable_trace("euf");
    test1();
    test2();
}
