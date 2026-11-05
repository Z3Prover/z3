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
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_skolem.h"
#include "ast/rewriter/th_rewriter.h"
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
        seq_rewriter     rw;
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac;
        stx::facet_id    eq_id;
        stx::facet_id    deq_id;
        stx::facet_id    arith_id;
        stx::facet_id    nc_id;
        stx::facet_id    mem_id;
        stx::facet_id    assumption_id;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), a(m), s(u.str.mk_string_sort()),
            tree(trail, m.limit()),
            root(tree.mk_root()),
            solver(m, a, tree.dep_mgr()),
            rw(m), ac(m, u, trail),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            deq_id(tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr())),
            arith_id(tree.register_facet<seq::solver_facet>(*root, m, u, solver)),
            nc_id(tree.register_facet<seq::ncontains_facet>(*root, m, u, tree.dep_mgr())),
            mem_id(tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr(), rw, ac)),
            assumption_id(tree.register_facet<seq::assumption_facet>(*root, m))
        {
            ac.set_eq_id(eq_id);
            ac.set_deq_id(deq_id);
            ac.set_arith_id(arith_id);
            ac.set_ncontains_id(nc_id);
            ac.set_mem_id(mem_id);
            ac.set_assumption_id(assumption_id);
            tree.set_ambient_context(&ac);
            tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::ncontains_propagation, m, u, a));
            tree.add_propagation_plugin(alloc(seq::mem_propagation, m, u, rw));
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

    // An indexof-style guarded equation can contain self-referential
    // skolems, so equation propagation cannot substitute X. The exposed
    // literal still directly contradicts not-contains(X, "=").
    static void tst_ncontains_conflicts_with_cyclic_equation() {
        fixture fx;
        th_rewriter rw(fx.m);
        seq::skolem sk(fx.m, rw);
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref eq(fx.u.str.mk_string(zstring("=")), fx.m);
        expr_ref lhs(sk.mk_indexof_left(X, eq), fx.m);
        expr_ref rhs(sk.mk_indexof_right(X, eq), fx.m);
        expr_ref decomposition(fx.u.str.mk_concat(lhs, eq, rhs), fx.m);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X, decomposition);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(X, eq);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    static void tst_ncontains_joint_witness() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        expr_ref bc(fx.u.str.mk_string("bc"), fx.m);
        expr_ref a(fx.u.str.mk_string("a"), fx.m);
        expr_ref first(fx.u.re.mk_to_re(ab), fx.m);
        expr_ref second(fx.u.re.mk_to_re(bc), fx.m);
        expr_ref language(fx.u.re.mk_union(first, second), fx.m);
        fx.root->facet_as<seq::mem_facet>(fx.mem_id).add(
            seq::str_mem(fx.m, x, seq::view::membership(language, fx.m)));
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(x, a);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
        auto* snapshot = fx.tree.sat_snapshot();
        ENSURE(snapshot);
        expr_ref word(fx.m);
        ENSURE(snapshot->facet_as<seq::mem_facet>(fx.mem_id).get_witness(x, word));
        th_rewriter normalize(fx.m);
        normalize(word);
        ENSURE(word == bc);
    }

    static void tst_ncontains_cross_boundary_conflict() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
        expr_ref h(fx.u.str.mk_concat(x, y), fx.m);
        expr_ref a(fx.u.str.mk_string("a"), fx.m);
        expr_ref b(fx.u.str.mk_string("b"), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& ef = fx.root->facet_as<seq::eq_facet>(fx.eq_id);
        nf.add_ncontains(h, ab, fx.tree.dep_mgr().mk_leaf(1));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(nf.is_satisfied());
        ef.add_equation(x, a, fx.tree.dep_mgr().mk_leaf(2));
        ef.add_equation(y, b, fx.tree.dep_mgr().mk_leaf(3));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
        auto& dm = fx.tree.dep_mgr();
        ENSURE(dm.contains(fx.root->conflict_dep(), 1));
        ENSURE(dm.contains(fx.root->conflict_dep(), 2));
        ENSURE(dm.contains(fx.root->conflict_dep(), 3));
    }

    static void tst_ncontains_substitution_scope() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref needle(fx.m.mk_fresh_const("needle", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
        auto& dm = fx.tree.dep_mgr();
        nf.add_ncontains(x, needle, dm.mk_leaf(4));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(!nf.is_satisfied() && mf.memberships().empty());
        fx.trail.push_scope();
        expr_ref_vector tokens(fx.m);
        fx.u.str.get_concat_units(ab, tokens);
        nf.apply_subst(needle, tokens, dm.mk_leaf(5));
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(nf.is_satisfied() && mf.memberships().size() == 1);
        ENSURE(dm.contains(mf.memberships()[0].m_dep, 4));
        ENSURE(dm.contains(mf.memberships()[0].m_dep, 5));
        fx.trail.pop_scope(1);
        ENSURE(!nf.is_satisfied() && mf.memberships().empty());
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(!nf.is_satisfied() && mf.memberships().empty());
    }

    static void tst_ncontains_deferred_literal_scope() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
        expr_ref h(fx.m.mk_fresh_const("h", fx.s), fx.m);
        expr_ref needle(fx.m.mk_fresh_const("needle", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        auto& ef = fx.root->facet_as<seq::eq_facet>(fx.eq_id);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
        auto& dm = fx.tree.dep_mgr();
        ef.add_equation(x, y);
        nf.add_ncontains(h, needle);
        nf.add_ncontains(h, ab, dm.mk_leaf(7));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::proceed);
        ENSURE(nf.qhead() == 2 && mf.memberships().empty());
        fx.trail.push_scope();
        ef.remove_equation_trailed(0);
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::noop);
        fx.root->facet_as<seq::assumption_facet>(fx.assumption_id).block_model_completion();
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::proceed);
        ENSURE(!nf.ncontains()[1].active() && mf.memberships().size() == 1);
        ENSURE(dm.contains(mf.memberships()[0].m_dep, 7));
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::noop);
        fx.trail.pop_scope(1);
        ENSURE(!ef.is_satisfied() && nf.ncontains()[1].active());
        ENSURE(nf.qhead() == 2 && mf.memberships().empty());
        ENSURE(!fx.root->facet_as<seq::assumption_facet>(fx.assumption_id).model_completion_blocked());
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::noop);
    }

    static void tst_ncontains_character_projection_scope() {
        for (unsigned code : { 97u, 0x1f600u }) {
            fixture fx;
            expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
            expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
            expr_ref c(fx.m.mk_fresh_const("c", fx.u.mk_char_sort()), fx.m);
            expr_ref unit(fx.u.str.mk_unit(c), fx.m);
            expr_ref haystack(fx.u.str.mk_concat(x, unit, y), fx.m);
            expr_ref forbidden(fx.u.str.mk_char(code), fx.m);
            expr_ref needle(fx.u.str.mk_unit(forbidden), fx.m);
            auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
            auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
            auto& sf = fx.root->facet_as<seq::solver_facet>(fx.arith_id);
            auto& af = fx.root->facet_as<seq::assumption_facet>(fx.assumption_id);
            auto& dm = fx.tree.dep_mgr();
            nf.add_ncontains(haystack, needle, dm.mk_leaf(8));
            fx.trail.push_scope();
            seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
            ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::satisfied);
            ENSURE(mf.memberships().size() == 2 && af.assumptions().size() == 1);
            for (auto const& membership : mf.memberships())
                ENSURE(dm.contains(membership.m_dep, 8));
            expr_ref equal(fx.m.mk_eq(c, forbidden), fx.m);
            sf.add_constraint(equal, dm.mk_leaf(9));
            ENSURE(sf.has_conflict());
            ENSURE(dm.contains(sf.conflict_dep(), 8));
            ENSURE(dm.contains(sf.conflict_dep(), 9));
            fx.trail.pop_scope(1);
            ENSURE(!nf.is_satisfied() && mf.memberships().empty());
            ENSURE(af.assumptions().empty() && !sf.has_conflict());
            expr_ref other(fx.u.str.mk_char(code + 1), fx.m);
            expr_ref different(fx.m.mk_eq(c, other), fx.m);
            sf.add_constraint(different);
            ENSURE(fx.tree.solve() == stx::search_result::sat);
        }
    }

} // namespace

void tst_seq_ncontains_facet() {
    tst_ncontains_length_gate_discharges();
    tst_ncontains_empty_needle_conflict();
    tst_ncontains_ground_no_occurrence_sat();
    tst_ncontains_ground_occurrence_unsat();
    tst_ncontains_resolved_by_substitution_unsat();
    tst_ncontains_match_not_at_first_position_unsat();
    tst_ncontains_conflicts_with_cyclic_equation();
    tst_ncontains_joint_witness();
    tst_ncontains_cross_boundary_conflict();
    tst_ncontains_substitution_scope();
    tst_ncontains_deferred_literal_scope();
    tst_ncontains_character_projection_scope();
    std::cout << "seq_ncontains_facet: all tests passed\n";
}
