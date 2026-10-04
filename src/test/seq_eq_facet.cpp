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
#include "ast/seq/seq_assumption_facet.h"
#include "smt/seq_solver_facet.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"
#include <iostream>

namespace {
    static expr_ref mk_unit_char(ast_manager& m, seq_util& u, char ch) {
        return expr_ref(u.str.mk_unit(u.str.mk_char(static_cast<unsigned>(ch))), m);
    }

    // deq_facet::add_disequation only takes token vectors (no expr*/expr*
    // convenience overload); tests that build a disequation from whole
    // terms go through get_concat_units themselves.
    static expr_ref_vector mk_toks(seq_util& u, ast_manager& m, expr* e) {
        expr_ref_vector ts(m);
        u.str.get_concat_units(e, ts);
        return ts;
    }

    stx::search_result solve_eq(ast_manager& m, seq_util& u, expr* lhs, expr* rhs, unsigned max_depth = 12) {
        trail_stack tr;
        arith_util a(m);
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);
        root->facet_as<seq::eq_facet>(id).add_equation(lhs, rhs);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(id);
        ac.set_arith_id(arith_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));

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

    // Shared variable forced equal to two different constants.
    // Exercises Nielsen splitting and backtracking before reporting unsat.
    static void tst_branch_then_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        trail_stack tr;
        arith_util au(m);

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, au, tree.dep_mgr());
        stx::facet_id id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        auto& f = root->facet_as<seq::eq_facet>(id);
        f.add_equation(X, a);
        f.add_equation(X, b);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.set_max_search_depth(12);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    static void tst_depth_cutoff() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);
        expr_ref lhs(u.str.mk_concat(X, Y), m);
        expr_ref rhs(u.str.mk_string(zstring("abc")), m);
        ENSURE(solve_eq(m, u, lhs, rhs, 0) == stx::search_result::depth_cutoff);
    }

    // A disequation between two distinct constants is immediately
    // discharged (proved satisfiable-distinct) with no branching needed.
    static void tst_deq_trivial_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(mk_toks(u, m, a), mk_toks(u, m, b));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_deq_id(id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.set_max_search_depth(4);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    static void tst_deq_unit_nonempty_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref a(u.str.mk_char('a'), m);
        expr_ref unit(u.str.mk_unit(a), m);
        expr_ref empty(u.str.mk_empty(u.str.mk_string_sort()), m);

        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(mk_toks(u, m, unit), mk_toks(u, m, empty));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_deq_id(id);
        tree.set_ambient_context(&ac);
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
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

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(mk_toks(u, m, a1), mk_toks(u, m, a2));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_deq_id(id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.set_max_search_depth(4);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    // A substitution produced by eq_facet must propagate to deq_facet so
    // `X != "b"` is discharged after solving `X = "a"`.
    static void tst_deq_reacts_to_eq_branch_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        trail_stack tr;
        arith_util au(m);

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, au, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        root->facet_as<seq::eq_facet>(eq_id).add_equation(X, a);
        root->facet_as<seq::deq_facet>(deq_id).add_disequation(mk_toks(u, m, X), mk_toks(u, m, b));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_deq_id(deq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.set_max_search_depth(12);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // Symbolic char equality must substitute `c := 'a'`, reducing the
    // equation to `X = X`.
    static void tst_word_eq_split_char_eq_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* char_s = u.mk_char_sort();
        sort* s = u.str.mk_string_sort();
        expr_ref c(m.mk_fresh_const("c", char_s), m);
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref ca(u.mk_char('a'), m);
        expr_ref lhs(u.str.mk_concat(u.str.mk_unit(c), X), m);
        expr_ref rhs(u.str.mk_concat(u.str.mk_unit(ca), X), m);
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::sat);
    }

    // Check that find_eq_split_point chooses the balanced interior split
    // for `[a, X, Y] = [X, a, Y]`, with zero padding.
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

    // No interior split exists for `[X] = [a]`.
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

    // Balanced interior split on `X ++ a ++ Y = Y ++ a ++ X` should make
    // progress and preserve satisfiability.
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

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        root->facet_as<seq::eq_facet>(eq_id).add_equation(lhs, rhs);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.add_split_plugin(alloc(seq::eq_split, m, u));
        tree.set_max_search_depth(20);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // `X != Y` over two unconstrained variables should be discharged by
    // deq_split rather than getting stuck as unknown.
    static void tst_deq_split_free_vars_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(deq_id).add_disequation(mk_toks(u, m, X), mk_toks(u, m, Y));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        ac.set_deq_id(deq_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.add_split_plugin(alloc(seq::eq_split, m, u));
        tree.add_split_plugin(alloc(seq::deq_split, m, u));
        tree.set_max_search_depth(20);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // `a != a` should remain an immediate conflict even when deq_split is
    // enabled.
    static void tst_deq_split_equal_consts_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        expr_ref ca(mk_unit_char(m, u, 'a'));

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(deq_id).add_disequation(mk_toks(u, m, ca), mk_toks(u, m, ca));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        ac.set_deq_id(deq_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.add_split_plugin(alloc(seq::eq_split, m, u));
        tree.add_split_plugin(alloc(seq::deq_split, m, u));
        tree.set_max_search_depth(20);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    static void tst_deq_split_multiple_units_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        auto eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        auto deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        auto arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        auto assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_deq_id(deq_id);
        ac.set_arith_id(arith_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);

        expr_ref x(m.mk_const("x", a.mk_int()), m);
        expr_ref y(m.mk_const("y", a.mk_int()), m);
        expr_ref z(m.mk_const("z", a.mk_int()), m);
        expr_ref ux(u.str.mk_unit(x), m), uy(u.str.mk_unit(y), m), uz(u.str.mk_unit(z), m);
        auto& df = root->facet_as<seq::deq_facet>(deq_id);
        df.add_disequation(mk_toks(u, m, ux), mk_toks(u, m, uy));
        df.add_disequation(mk_toks(u, m, uy), mk_toks(u, m, uz));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::deq_split, m, u));
        tree.set_max_nodes(32);
        ENSURE(tree.solve() == stx::search_result::sat);
        ENSURE(df.disequations()[0].active() && df.disequations()[1].active());
        ENSURE(root->facet_as<seq::assumption_facet>(assumption_id).assumptions().empty());
    }

    static void check_length_model(ast_manager& m, expr* element, unsigned length, bool word_equation) {
        seq_util u(m);
        arith_util a(m);
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        p.set_bool("model", true);
        ref<solver> s = mk_smt_solver(m, p, symbol("ALL"));
        sort_ref seq_sort(u.str.mk_seq(element->get_sort()), m);
        expr_ref x(m.mk_const("x", seq_sort), m), y(m.mk_const("y", seq_sort), m);
        expr_ref_vector assertions(m);
        assertions.push_back(m.mk_eq(u.str.mk_length(x), a.mk_int(length)));
        if (word_equation) {
            expr_ref unit(u.str.mk_unit(element), m);
            assertions.push_back(m.mk_eq(u.str.mk_concat(x, unit), u.str.mk_concat(unit, y)));
        }
        for (expr* assertion : assertions)
            s->assert_expr(assertion);
        ENSURE(s->check_sat(0, nullptr) == l_true);
        model_ref md;
        s->get_model(md);
        ENSURE(md);
        for (expr* assertion : assertions)
            ENSURE(md->is_true(assertion));
    }

    static void tst_nseq_length_model() {
        ast_manager m;
        reg_decl_plugins(m);
        arith_util a(m);
        seq_util u(m);
        expr_ref_vector elements(m);
        elements.push_back(a.mk_int(1));
        elements.push_back(m.mk_true());
        elements.push_back(u.str.mk_char('a'));
        for (expr* element : elements)
            for (unsigned length : { 0u, 1u, 3u })
                for (bool word_equation : { false, true })
                    check_length_model(m, element, length, word_equation);
    }

} // namespace

    // Block compression should solve `X.a.Y = aaaa.b` within depth 1.
    static void tst_block_compression_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m), Y(m.mk_fresh_const("Y", s), m);
        expr_ref lhs(u.str.mk_concat(X, u.str.mk_concat(u.str.mk_string(zstring("a")), Y)), m);
        expr_ref rhs(u.str.mk_string(zstring("aaaab")), m);
        ENSURE(solve_eq(m, u, lhs, rhs, 1) == stx::search_result::sat);
    }

void tst_seq_eq_facet() {
    tst_trivial_sat();
    tst_symbol_clash_unsat();
    tst_commute_sat();
    tst_branch_then_unsat();
    tst_depth_cutoff();
    tst_deq_trivial_sat();
    tst_deq_unit_nonempty_sat();
    tst_deq_trivial_unsat();
    tst_deq_reacts_to_eq_branch_sat();
    tst_eq_split_find_point();
    tst_eq_split_find_point_none();
    tst_eq_split_progress_sat();
    tst_deq_split_free_vars_sat();
    tst_deq_split_equal_consts_unsat();
    tst_deq_split_multiple_units_sat();
    tst_word_eq_split_char_eq_sat();
    tst_block_compression_sat();
    tst_nseq_length_model();
    std::cout << "seq_eq_facet: all tests passed\n";
}
