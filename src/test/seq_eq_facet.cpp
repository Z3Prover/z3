/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.cpp (test)

Abstract:

    Unit test for `seq::eq_facet` / `seq::eq_propagation` / `seq::word_eq_split`
    (ast/rewriter/seq_eq_facet.h): word-equation solving via the Nielsen
    transformation, running on top of the generic `stx::search_tree` core
    (util/stx_search_tree.h).

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_eq_facet.h"
#include <iostream>

namespace {

    stx::search_result solve_eq(ast_manager& m, seq_util& u, expr* lhs, expr* rhs, unsigned max_depth = 12) {
        seq::eq_tree tree;
        stx::facet_id id = tree.register_facet();
        seq::eq_propagation prop(id);
        seq::word_eq_split split(tree, id);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);

        seq::eq_facet* f = alloc(seq::eq_facet, m, u);
        f->add_equation(lhs, rhs);
        tree.mk_root()->set_facet(id, f);
        tree.set_max_search_depth(max_depth);
        return tree.solve();
    }

    static void tst_trivial_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref lhs(u.str.mk_string(zstring("ab")), m);
        expr_ref rhs(u.str.mk_string(zstring("ab")), m);
        (void)s;
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::sat);
    }

    static void tst_symbol_clash_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref lhs(u.str.mk_string(zstring("ab")), m);
        expr_ref rhs(u.str.mk_string(zstring("ba")), m);
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::unsat);
    }

    // X ++ "a" = "a" ++ X is satisfiable (e.g. X = epsilon), and reachable
    // via the Nielsen transformation in a single branch.
    static void tst_commute_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref lhs(u.str.mk_concat(X, a), m);
        expr_ref rhs(u.str.mk_concat(a, X), m);
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::sat);
    }

    // Same variable forced to two different constants ("X = a" and "X = b"
    // combined into one equation via a shared X) is unsatisfiable: this
    // exercises the two/three-way Nielsen split and backtracking across
    // all-conflicting children, not just an immediate symbol clash.
    static void tst_branch_then_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        seq::eq_tree tree;
        stx::facet_id id = tree.register_facet();
        seq::eq_propagation prop(id);
        seq::word_eq_split split(tree, id);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);

        seq::eq_facet* f = alloc(seq::eq_facet, m, u);
        f->add_equation(X, a);
        f->add_equation(X, b);
        tree.mk_root()->set_facet(id, f);
        tree.set_max_search_depth(12);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    static void tst_depth_cutoff_unknown() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);
        expr_ref lhs(u.str.mk_concat(X, Y), m);
        expr_ref rhs(u.str.mk_string(zstring("abc")), m);
        ENSURE(solve_eq(m, u, lhs, rhs, 0) == stx::search_result::unknown);
    }

} // namespace

void tst_seq_eq_facet() {
    tst_trivial_sat();
    tst_symbol_clash_unsat();
    tst_commute_sat();
    tst_branch_then_unsat();
    tst_depth_cutoff_unknown();
    std::cout << "seq_eq_facet: all tests passed\n";
}
