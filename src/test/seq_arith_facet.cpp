/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_arith_facet.cpp (test)

Abstract:

    Unit test for `seq::arith_facet` / `seq::arith_propagation`
    (smt/seq_arith_facet.h): a real incremental-SMT-backed length facet,
    push/pop synced to DFS backtracking via a `scope_trail` trail object
    registered on the shared `trail_stack` (see util/stx_search_tree.h),
    combined with `eq_facet` (ast/seq/seq_eq_facet.h).

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "smt/seq_arith_facet.h"
#include <iostream>

namespace {

    // `X = "ab"` is satisfiable via eq_facet alone (X := "ab"), but this
    // test additionally asserts the explicit numeric constraint
    // `len(X) = 3` directly into the shared incremental backend up
    // front, contradicting the (implicit) actual length of the solution
    // - arith_facet's real incremental solver must catch this
    // arithmetic-only conflict that eq_facet's Nielsen transformation
    // alone has no way to see (it never reasons about lengths).
    static void tst_arith_length_conflict() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();

        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref ab(u.str.mk_string(zstring("ab")), m);

        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u);
        seq::arith_sub_solver solver(m, a);
        stx::facet_id arith_id = tree.register_facet<seq::arith_facet>(*root, m, u, solver);

        root->facet_as<seq::eq_facet>(eq_id).add_equation(X, ab);
        root->facet_as<seq::arith_facet>(arith_id).add_constraint(m.mk_eq(u.str.mk_length(X), a.mk_int(3)));

        seq::eq_propagation eprop(eq_id);
        seq::word_eq_split esplit(m, u, eq_id);
        seq::arith_propagation aprop(arith_id, eq_id);
        tree.add_propagation_plugin(&eprop);
        tree.add_propagation_plugin(&aprop);
        tree.add_split_plugin(&esplit);
        tree.set_max_search_depth(8);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    // Same equation without the conflicting explicit length assertion:
    // eq_facet resolves `X ++ "a" = "b"` to a symbol clash immediately
    // (leading token 'a' of the singleton "b" side after eq_facet's
    // simplify would need len(X)=0 then compare "a" vs "b" - a plain
    // symbol clash), independent of arith_facet, so the combination
    // should still find unsat and arith_facet must not introduce a false
    // sat/unknown verdict.
    static void tst_arith_facet_does_not_break_eq_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();

        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref ca(u.str.mk_string(zstring("a")), m);
        expr_ref cb(u.str.mk_string(zstring("b")), m);
        expr_ref lhs(u.str.mk_concat(X, ca), m);
        expr_ref rhs(cb, m);

        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u);
        seq::arith_sub_solver solver(m, a);
        stx::facet_id arith_id = tree.register_facet<seq::arith_facet>(*root, m, u, solver);

        root->facet_as<seq::eq_facet>(eq_id).add_equation(lhs, rhs);

        seq::eq_propagation eprop(eq_id);
        seq::word_eq_split esplit(m, u, eq_id);
        seq::arith_propagation aprop(arith_id, eq_id);
        tree.add_propagation_plugin(&eprop);
        tree.add_propagation_plugin(&aprop);
        tree.add_split_plugin(&esplit);
        tree.set_max_search_depth(8);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    // A satisfiable equation (`X = "ab"`) combined with a consistent
    // explicit length assertion (`len(X) = 2`) must still succeed: this
    // exercises that arith_facet's push/pop discipline does not leave the
    // shared backend permanently polluted/broken across sibling branches
    // (a bug here would show up as a false unsat/unknown).
    static void tst_arith_facet_consistent_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();

        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref ab(u.str.mk_string(zstring("ab")), m);

        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u);
        seq::arith_sub_solver solver(m, a);
        stx::facet_id arith_id = tree.register_facet<seq::arith_facet>(*root, m, u, solver);

        root->facet_as<seq::eq_facet>(eq_id).add_equation(X, ab);
        root->facet_as<seq::arith_facet>(arith_id).add_constraint(m.mk_eq(u.str.mk_length(X), a.mk_int(2)));

        seq::eq_propagation eprop(eq_id);
        seq::word_eq_split esplit(m, u, eq_id);
        seq::arith_propagation aprop(arith_id, eq_id);
        tree.add_propagation_plugin(&eprop);
        tree.add_propagation_plugin(&aprop);
        tree.add_split_plugin(&esplit);
        tree.set_max_search_depth(8);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

} // namespace

void tst_seq_arith_facet() {
    tst_arith_length_conflict();
    tst_arith_facet_does_not_break_eq_unsat();
    tst_arith_facet_consistent_sat();
    std::cout << "seq_arith_facet: all tests passed\n";
}
