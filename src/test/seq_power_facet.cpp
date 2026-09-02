/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_power_facet.cpp (test)

Abstract:

    Unit test for `seq::power_facet` / `seq::power_propagation` /
    `seq::power_split` (ast/seq/seq_power_facet.h): the `seq.power`
    (`s^n`) facet, combined with `eq_facet`/`arith_facet`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_power_facet.h"
#include "smt/seq_arith_facet.h"
#include <iostream>

namespace {

    struct fixture {
        ast_manager      m;
        seq_util         u;
        arith_util       a;
        sort*            s;
        seq::eq_tree     tree;
        seq::eq_tree::node* root;
        seq::arith_sub_solver solver;
        stx::facet_id    eq_id;
        stx::facet_id    arith_id;
        stx::facet_id    pow_id;

        seq::eq_propagation      eprop;
        seq::word_eq_split       esplit;
        seq::arith_propagation   aprop;
        seq::power_propagation   pprop;
        seq::power_split         psplit;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), a(m), s(u.str.mk_string_sort()),
            root(tree.mk_root()),
            solver(m, a),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            arith_id(tree.register_facet<seq::arith_facet>(*root, m, u, solver)),
            pow_id(tree.register_facet<seq::power_facet>(*root, m, u, a, tree.dep_mgr())),
            eprop(eq_id), esplit(m, u, eq_id), aprop(arith_id, eq_id),
            pprop(m, u, a, pow_id, eq_id, arith_id), psplit(m, u, a, pow_id, eq_id, arith_id)
        {
            tree.add_propagation_plugin(&eprop);
            tree.add_propagation_plugin(&aprop);
            tree.add_propagation_plugin(&pprop);
            tree.add_split_plugin(&psplit);
            tree.add_split_plugin(&esplit);
            tree.set_max_search_depth(20);
        }
    };

    // Known exponent, exact unfold: "ab"^2 = "abab" must be sat -
    // power_propagation unfolds "ab"^2 directly into the eq_facet
    // equation "ab"++"ab" = "abab", which eq_propagation then solves
    // deterministically.
    static void tst_power_known_exponent_sat() {
        fixture fx;
        expr_ref ab(fx.u.str.mk_string(zstring("ab")), fx.m);
        expr_ref abab(fx.u.str.mk_string(zstring("abab")), fx.m);
        expr_ref two(fx.a.mk_int(2), fx.m);
        expr_ref e(fx.u.str.mk_power(ab, two), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e, ab, two);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e, abab);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Known exponent, exact unfold, conflicting lengths: "ab"^2 = "aba"
    // must be unsat - the unfolded equation "ab"++"ab" = "aba" is a
    // ground mismatch that eq_propagation's own simplification detects.
    static void tst_power_known_exponent_conflict() {
        fixture fx;
        expr_ref ab(fx.u.str.mk_string(zstring("ab")), fx.m);
        expr_ref aba(fx.u.str.mk_string(zstring("aba")), fx.m);
        expr_ref two(fx.a.mk_int(2), fx.m);
        expr_ref e(fx.u.str.mk_power(ab, two), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e, ab, two);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e, aba);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Zero exponent: s^0 = "a" must be unsat - power_propagation unfolds
    // s^0 to epsilon, and epsilon = "a" is a trivial ground mismatch.
    static void tst_power_zero_exponent_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref zero(fx.a.mk_int(0), fx.m);
        expr_ref e(fx.u.str.mk_power(X, zero), fx.m);
        expr_ref a_str(fx.u.str.mk_string(zstring("a")), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e, X, zero);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e, a_str);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Symbolic exponent, length-only conflict: len(s) = 3 and
    // len(e) = 4 with e = s^n has no solution, since len(e) must be a
    // multiple of len(s) once n >= 1, and n <= 0 forces len(e) = 0. This
    // exercises power_propagation's length-only axiomatization into
    // arith_facet without ever needing to unfold/split.
    static void tst_power_symbolic_length_conflict_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e(fx.u.str.mk_power(X, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e, X, N);
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(3)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e), fx.a.mk_int(4)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Symbolic exponent, split finds a solution: x^n = "aaaa" with
    // |x| = 2 must be sat via power_split unfolding to n = 2 (x = "aa").
    static void tst_power_symbolic_split_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e(fx.u.str.mk_power(X, N), fx.m);
        expr_ref aaaa(fx.u.str.mk_string(zstring("aaaa")), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e, aaaa);
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(2)));
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Symbolic exponent, split exhausts without a solution: x^n = "aaaa"
    // with |x| = 3 must be unsat - no j in [1,bound] with 3*j = 4, and
    // the n<=0/e=epsilon branch conflicts with e = "aaaa" too.
    static void tst_power_symbolic_split_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e(fx.u.str.mk_power(X, N), fx.m);
        expr_ref aaaa(fx.u.str.mk_string(zstring("aaaa")), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e, aaaa);
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(3)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

} // namespace

void tst_seq_power_facet() {
    tst_power_known_exponent_sat();
    tst_power_known_exponent_conflict();
    tst_power_zero_exponent_unsat();
    tst_power_symbolic_length_conflict_unsat();
    std::cout << "=== test5 ===\n" << std::flush;
    tst_power_symbolic_split_sat();
    tst_power_symbolic_split_unsat();
    std::cout << "seq_power_facet: all tests passed\n";
}
