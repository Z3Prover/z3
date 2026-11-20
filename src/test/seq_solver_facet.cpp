/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_solver_facet.cpp (test)

Abstract:

    Unit test for `seq::solver_facet` / `seq::arith_propagation`
    (smt/seq_solver_facet.h): a real incremental-SMT-backed length facet,
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
#include "smt/seq_solver_facet.h"
#include <iostream>

namespace {

    // A conflicting explicit length constraint should be caught by the
    // arithmetic backend even when the equation itself is satisfiable.
    static void tst_arith_length_conflict() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();

        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref ab(u.str.mk_string(zstring("ab")), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        root->facet_as<seq::eq_facet>(eq_id).add_equation(X, ab);
        root->facet_as<seq::solver_facet>(arith_id).add_constraint(m.mk_eq(u.str.mk_length(X), a.mk_int(3)));

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.set_max_search_depth(8);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    // solver_facet must not interfere with an unsat equation already
    // detected by eq_facet.
    static void tst_solver_facet_does_not_break_eq_unsat() {
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

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        root->facet_as<seq::eq_facet>(eq_id).add_equation(lhs, rhs);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.set_max_search_depth(8);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    // A consistent explicit length constraint should preserve the sat
    // result.
    static void tst_solver_facet_consistent_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();

        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref ab(u.str.mk_string(zstring("ab")), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        root->facet_as<seq::eq_facet>(eq_id).add_equation(X, ab);
        root->facet_as<seq::solver_facet>(arith_id).add_constraint(m.mk_eq(u.str.mk_length(X), a.mk_int(2)));

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.set_max_search_depth(8);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

} // namespace

void tst_seq_solver_facet() {
    tst_arith_length_conflict();
    tst_solver_facet_does_not_break_eq_unsat();
    tst_solver_facet_consistent_sat();
    std::cout << "seq_solver_facet: all tests passed\n";
}
