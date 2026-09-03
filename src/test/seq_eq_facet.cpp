/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.cpp (test)

Abstract:

    Unit test for `seq::eq_facet` / `seq::eq_propagation` / `seq::word_eq_split`
    (ast/seq/seq_eq_facet.h): word-equation solving via the Nielsen
    transformation, running on top of the generic `stx::search_tree` core
    (util/stx_search_tree.h).

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
    static expr_ref mk_unit_char(ast_manager& m, seq_util& u, char ch) {
        return expr_ref(u.str.mk_unit(u.str.mk_char(static_cast<unsigned>(ch))), m);
    }

    stx::search_result solve_eq(ast_manager& m, seq_util& u, expr* lhs, expr* rhs, unsigned max_depth = 12) {
        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::eq_facet>(id).add_equation(lhs, rhs);

        seq::eq_propagation prop(id);
        seq::word_eq_split split(m, u, id);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);

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
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        auto& f = root->facet_as<seq::eq_facet>(id);
        f.add_equation(X, a);
        f.add_equation(X, b);

        seq::eq_propagation prop(id);
        seq::word_eq_split split(m, u, id);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
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

    // A disequation between two distinct constants is immediately
    // discharged (proved satisfiable-distinct) with no branching needed.
    static void tst_deq_trivial_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(a, b);

        seq::deq_propagation dprop(id);
        tree.add_propagation_plugin(&dprop);
        tree.set_max_search_depth(4);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // A disequation between a constant and itself is an immediate
    // conflict (both sides prefix-strip to empty: forced equal).
    static void tst_deq_trivial_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref a1(u.str.mk_string(zstring("a")), m);
        expr_ref a2(u.str.mk_string(zstring("a")), m);

        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(a1, a2);

        seq::deq_propagation dprop(id);
        tree.add_propagation_plugin(&dprop);
        tree.set_max_search_depth(4);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    // eq_facet and deq_facet share the same node/variable pool: solving
    // `X = "a"` (via eq_facet's Nielsen split) must broadcast the chosen
    // substitution to `deq_facet`'s pending `X != "b"`, which then gets
    // discharged once X is resolved far enough to see a symbol clash
    // against "b" - this exercises subst_sink_i cross-facet wiring.
    static void tst_deq_reacts_to_eq_branch_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        seq::eq_tree tree;
        auto* root = tree.mk_root();
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::eq_facet>(eq_id).add_equation(X, a);
        root->facet_as<seq::deq_facet>(deq_id).add_disequation(X, b);

        seq::eq_propagation eprop(eq_id);
        seq::word_eq_split esplit(m, u, eq_id);
        seq::deq_propagation dprop(deq_id);
        tree.add_propagation_plugin(&eprop);
        tree.add_propagation_plugin(&dprop);
        tree.add_split_plugin(&esplit);
        tree.set_max_search_depth(12);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // Direct unit test of eq_split::find_eq_split_point (the ported
    // c3-branch balance-tracking algorithm), independent of the full
    // search: LHS = [a, X, Y], RHS = [X, a, Y] (a is a constant char, X
    // and Y are distinct variables). Tracing the algorithm by hand: the
    // running signed balance of variable tokens returns to zero (nz==0)
    // at the interior point (li=2, ri=2) with const_diff=0 - i.e. the
    // split "a.X | Y" vs "X.a | Y" - which is the minimal-|padding|
    // choice (padding=0) since an earlier candidate at (li=2, ri=1) had
    // |const_diff|=1. This confirms the ported algorithm finds a valid,
    // minimal-padding interior split rather than stopping at the first
    // nz==0 point it encounters.
    static void tst_eq_split_find_point() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);

        expr_ref_vector lhs(m), rhs(m);
        lhs.push_back(mk_unit_char(m, u, 'a')); lhs.push_back(X); lhs.push_back(Y);
        rhs.push_back(X); rhs.push_back(mk_unit_char(m, u, 'a')); rhs.push_back(Y);

        unsigned split_lhs = 0, split_rhs = 0;
        int padding = 0;
        bool found = seq::eq_split::find_eq_split_point(u, lhs, rhs, split_lhs, split_rhs, padding);
        ENSURE(found);
        ENSURE(split_lhs == 2);
        ENSURE(split_rhs == 2);
        ENSURE(padding == 0);
    }

    // No split point exists when there is only one variable-length
    // token total (find_eq_split_point requires lhs_len>1 && rhs_len>1,
    // and also requires an interior point where the variable balance is
    // zero) - LHS = [X], RHS = [a] never reaches the `lhs_len<=1`
    // guard's else-branch productively since lhs has just one token.
    // Confirms the short-circuit guard for trivially-short sides.
    static void tst_eq_split_find_point_none() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);

        expr_ref_vector lhs(m), rhs(m);
        lhs.push_back(X);
        rhs.push_back(mk_unit_char(m, u, 'a'));

        unsigned split_lhs = 0, split_rhs = 0;
        int padding = 0;
        ENSURE(!seq::eq_split::find_eq_split_point(u, lhs, rhs, split_lhs, split_rhs, padding));
    }

    // eq_split (mid-equation split with padding variable): "X ++ a ++ Y =
    // Y ++ a ++ X" is satisfiable (e.g. X = Y = epsilon, or X = Y = any
    // common value) - find_eq_split_point finds a balanced interior
    // point around the shared "a" token (X, Y both consumed once on
    // each side, net zero balance), splitting into "X = Y" and "Y = X"
    // (up to padding), which then re-enter eq_facet/word_eq_split and
    // resolve to sat. This exercises eq_split's own splitting logic
    // (not just word_eq_split's single-token peel, which alone cannot
    // make progress here since neither side starts/ends with a
    // resolvable constant-vs-constant or matching-variable head token
    // pair beyond the shared "a" in the middle).
    static void tst_eq_split_progress_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);
        expr_ref ch(u.str.mk_string(zstring("a")), m);
        expr_ref lhs(u.str.mk_concat(u.str.mk_concat(X, ch), Y), m);
        expr_ref rhs(u.str.mk_concat(u.str.mk_concat(Y, ch), X), m);

        seq::eq_tree tree;
        auto* root = tree.mk_root();
        seq::arith_sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::arith_facet>(*root, m, u, solver);
        root->facet_as<seq::eq_facet>(eq_id).add_equation(lhs, rhs);

        seq::eq_propagation eprop(eq_id);
        seq::word_eq_split esplit(m, u, eq_id);
        seq::arith_propagation aprop(arith_id, eq_id);
        seq::eq_split split(m, u, eq_id, arith_id);
        tree.add_propagation_plugin(&eprop);
        tree.add_propagation_plugin(&aprop);
        tree.add_split_plugin(&esplit);
        tree.add_split_plugin(&split);
        tree.set_max_search_depth(20);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

} // namespace

void tst_seq_eq_facet() {
    tst_trivial_sat();
    tst_symbol_clash_unsat();
    tst_commute_sat();
    tst_branch_then_unsat();
    tst_depth_cutoff_unknown();
    tst_deq_trivial_sat();
    tst_deq_trivial_unsat();
    tst_deq_reacts_to_eq_branch_sat();
    tst_eq_split_find_point();
    tst_eq_split_find_point_none();
    tst_eq_split_progress_sat();
    std::cout << "seq_eq_facet: all tests passed\n";
}
