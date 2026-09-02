/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.cpp (test)

Abstract:

    Unit tests for `seq::mem_facet`.

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_mem_facet.h"
#include <iostream>

namespace {

    struct fixture {
        ast_manager     m;
        seq_rewriter*   rw;
        seq_util*        u;
        trail_stack      trail;
        seq::live_states* live;
        fixture() { reg_decl_plugins(m); rw = alloc(seq_rewriter, m); u = alloc(seq_util, m); live = alloc(seq::live_states, *rw, seq::transition_mode::brzozowski_tm); }
        ~fixture() { dealloc(live); dealloc(u); dealloc(rw); }
    };

    stx::search_result solve_mem(fixture& f, std::function<void(seq::eq_tree&, seq::eq_tree::node*, stx::facet_id, stx::facet_id)> init, unsigned depth = 12) {
        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, f.m, *f.u);
        stx::facet_id mem_id = tree.register_facet<seq::mem_facet>(*root, f.m, *f.u);
        init(tree, root, eq_id, mem_id);
        seq::eq_propagation eprop(eq_id);
        seq::word_eq_split esplit(f.m, *f.u, eq_id);
        seq::mem_propagation mprop(f.m, *f.u, mem_id, *f.rw, *f.live);
        seq::mem_var_split vsplit(f.m, *f.u, mem_id, eq_id);
        seq::mem_monadic_split msplit(f.m, *f.u, mem_id, *f.rw, f.trail);
        tree.add_propagation_plugin(&eprop);
        tree.add_propagation_plugin(&mprop);
        tree.add_split_plugin(&vsplit);
        tree.add_split_plugin(&msplit);
        tree.add_split_plugin(&esplit);
        tree.set_max_search_depth(depth);
        return tree.solve();
    }

    static void tst_trivial_sat() {
        fixture f;
        expr_ref word(f.u->str.mk_string(zstring("ab")), f.m);
        expr_ref re(f.u->re.mk_concat(f.u->re.mk_to_re(f.u->str.mk_string(zstring("a"))),
                                      f.u->re.mk_to_re(f.u->str.mk_string(zstring("b")))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree&, seq::eq_tree::node* root, stx::facet_id, stx::facet_id mem_id) {
            root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(f.m, word, seq::view::membership(re)));
        }) == stx::search_result::sat);
    }

    static void tst_dead_unsat() {
        fixture f;
        expr_ref word(f.u->str.mk_string(zstring("a")), f.m);
        expr_ref re(f.u->re.mk_to_re(f.u->str.mk_string(zstring("a"))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree&, seq::eq_tree::node* root, stx::facet_id, stx::facet_id mem_id) {
            root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(f.m, word, seq::view::membership(re)));
        }) == stx::search_result::sat);
    }

    static void tst_single_var_sat() {
        fixture f;
        sort* s = f.u->str.mk_string_sort();
        expr_ref X(f.m.mk_fresh_const("X", s), f.m);
        expr_ref a(f.u->str.mk_string(zstring("a")), f.m);
        expr_ref star_a(f.u->re.mk_star(f.u->re.mk_to_re(a)), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree&, seq::eq_tree::node* root, stx::facet_id eq_id, stx::facet_id mem_id) {
            root->facet_as<seq::eq_facet>(eq_id).add_equation(X, a);
            root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(f.m, X, seq::view::membership(star_a)));
        }) == stx::search_result::sat);
    }

    static void tst_two_var_monadic_sat() {
        fixture f;
        sort* s = f.u->str.mk_string_sort();
        expr_ref X(f.m.mk_fresh_const("X", s), f.m);
        expr_ref Y(f.m.mk_fresh_const("Y", s), f.m);
        expr_ref term(f.u->str.mk_concat(X, Y), f.m);
        expr_ref re(f.u->re.mk_concat(f.u->re.mk_star(f.u->re.mk_to_re(f.u->str.mk_string(zstring("a")))),
                                      f.u->re.mk_star(f.u->re.mk_to_re(f.u->str.mk_string(zstring("b"))))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree&, seq::eq_tree::node* root, stx::facet_id, stx::facet_id mem_id) {
            root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(f.m, term, seq::view::membership(re)));
        }, 16) == stx::search_result::sat);
    }
}

void tst_seq_mem_facet() {
    tst_trivial_sat();
    tst_dead_unsat();
    tst_single_var_sat();
    tst_two_var_monadic_sat();
    std::cout << "seq_mem_facet: all tests passed\n";
}
