/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ncontains_facet.cpp (test)

Abstract:

    Unit test for `seq::ncontains_facet` / `seq::ncontains_propagation` /
    `seq::ncontains_split` (ast/seq/seq_ncontains_facet.h): the
    negative str.contains facet, combined with `eq_facet`/`solver_facet`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_ncontains_facet.h"
#include "smt/seq_solver_facet.h"
#include <iostream>

namespace {

    struct fixture {
        ast_manager      m;
        seq_util         u;
        arith_util       a;
        sort*            s;
        trail_stack      trail;
        seq::eq_tree     tree;
        seq::eq_tree::node* root;
        seq::sub_solver solver;
        stx::facet_id    eq_id;
        stx::facet_id    arith_id;
        stx::facet_id    nc_id;
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), a(m), s(u.str.mk_string_sort()),
            tree(trail, m.limit()),
            root(tree.mk_root()),
            solver(m, a, tree.dep_mgr()),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            arith_id(tree.register_facet<seq::solver_facet>(*root, m, u, solver)),
            nc_id(tree.register_facet<seq::ncontains_facet>(*root, m, u, tree.dep_mgr())),
            ac(m, u, trail)
        {
            ac.set_eq_id(eq_id);
            ac.set_arith_id(arith_id);
            ac.set_ncontains_id(nc_id);
            tree.set_ambient_context(&ac);
            tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::ncontains_propagation, m, u, a));
            tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
            tree.set_max_search_depth(12);
        }
    };

    // `len(h) < len(n)` is asserted directly: `not contains("a","ab")`
    // must be vacuously satisfied by the length-gate propagation alone
    // (no split needed).
    static void tst_ncontains_length_gate_discharges() {
        fixture fx;
        expr_ref h(fx.u.str.mk_string(zstring("a")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("ab")), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, n);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // `not contains(h, "")` (empty needle) is always false - the empty
    // string is contained in everything - so this must be unsat.
    static void tst_ncontains_empty_needle_conflict() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref empty(fx.u.str.mk_empty(fx.s), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(X, empty);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Ground negative containment with no matching position should be sat.
    static void tst_ncontains_ground_no_occurrence_sat() {
        fixture fx;
        expr_ref h(fx.u.str.mk_string(zstring("abc")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("d")), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, n);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Ground/ground case where the needle DOES occur as a genuine infix:
    // `not contains("abc", "b")` must be unsat - the deterministic
    // prefix-unrolling propagation must find the alignment (at position
    // 1) and report a conflict.
    static void tst_ncontains_ground_occurrence_unsat() {
        fixture fx;
        expr_ref h(fx.u.str.mk_string(zstring("abc")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("b")), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, n);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // After solving `X = "b"`, the substitution must be reflected in
    // `not contains(X, "b")`, yielding a conflict.
    static void tst_ncontains_resolved_by_substitution_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref b(fx.u.str.mk_string(zstring("b")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("b")), fx.m);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X, b);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(X, n);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // A definite match at a later position should still make
    // `not contains(X ++ "b", "b")` unsat.
    static void tst_ncontains_match_not_at_first_position_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref b(fx.u.str.mk_string(zstring("b")), fx.m);
        expr_ref h(fx.u.str.mk_concat(X, b), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, b);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

} // namespace

void tst_seq_ncontains_facet() {
    tst_ncontains_length_gate_discharges();
    tst_ncontains_empty_needle_conflict();
    tst_ncontains_ground_no_occurrence_sat();
    tst_ncontains_ground_occurrence_unsat();
    tst_ncontains_resolved_by_substitution_unsat();
    tst_ncontains_match_not_at_first_position_unsat();
    std::cout << "seq_ncontains_facet: all tests passed\n";
}
