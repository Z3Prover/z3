/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_power_facet.cpp (test)

Abstract:

    Unit test for `seq::power_facet` / `seq::power_propagation` /
    `seq::power_split` (ast/seq/seq_power_facet.h): the `seq.power`
    (`s^n`) facet, combined with `eq_facet`/`solver_facet`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_power_facet.h"
#include "ast/seq/seq_assumption_facet.h"
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
        stx::facet_id    pow_id;
        stx::facet_id    assumption_id;
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), a(m), s(u.str.mk_string_sort()),
            tree(trail, m.limit()),
            root(tree.mk_root()),
            solver(m, a, tree.dep_mgr()),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            arith_id(tree.register_facet<seq::solver_facet>(*root, m, u, solver)),
            pow_id(tree.register_facet<seq::power_facet>(*root, m, u, a, tree.dep_mgr())),
            assumption_id(tree.register_facet<seq::assumption_facet>(*root, m)),
            ac(m, u, trail)
        {
            ac.set_eq_id(eq_id);
            ac.set_arith_id(arith_id);
            ac.set_pow_id(pow_id);
            ac.set_assumption_id(assumption_id);
            tree.set_ambient_context(&ac);
            tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::power_propagation, m, u, a));
            tree.add_split_plugin(alloc(seq::power_split, m, u, a));
            tree.add_split_plugin(alloc(seq::power_fine_wilf, m, u, a));
            tree.add_split_plugin(alloc(seq::power_split_elim, m, u, a));
            tree.add_split_plugin(alloc(seq::power_var_decompose, m, u, a));
            tree.add_split_plugin(alloc(seq::power_peel, m, u, a));
            tree.add_split_plugin(alloc(seq::power_gpower_intro, m, u, a));
            tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
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
    // solver_facet without ever needing to unfold/split.
    static void tst_power_symbolic_length_conflict_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e(fx.u.str.mk_power(X, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e, X, N);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(3)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
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
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
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
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(3)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Large equal-length powers beyond the unfolding bound must not be
    // spuriously refuted.
    static void tst_fine_wilf_large_exponent_not_refuted() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref M(fx.m.mk_fresh_const("M", fx.a.mk_int()), fx.m);
        expr_ref e_u(fx.u.str.mk_power(X, N), fx.m);
        expr_ref e_w(fx.u.str.mk_power(Y, M), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_u, X, N);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_w, Y, M);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_u, e_w);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e_u), fx.a.mk_int(1000)));
        ENSURE(fx.tree.solve() != stx::search_result::unsat);
    }

    // Same trigger pattern but a satisfiable instance: e_u = X^n,
    // e_w = Y^m, X and Y both length 1, with equation e_u = e_w and no
    // additional constraint pinning down the (equal, but otherwise
    // free) common length - sat via n = m = 0 (both sides epsilon).
    static void tst_fine_wilf_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref M(fx.m.mk_fresh_const("M", fx.a.mk_int()), fx.m);
        expr_ref e_u(fx.u.str.mk_power(X, N), fx.m);
        expr_ref e_w(fx.u.str.mk_power(Y, M), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_u, X, N);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_w, Y, M);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_u, e_w);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Constrain the lengths so Fine-Wilf must use a progress case rather
    // than the short-overlap case; the instance remains satisfiable.
    static void tst_fine_wilf_progress_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref M(fx.m.mk_fresh_const("M", fx.a.mk_int()), fx.m);
        expr_ref e_u(fx.u.str.mk_power(X, N), fx.m);
        expr_ref e_w(fx.u.str.mk_power(Y, M), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_u, X, N);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_w, Y, M);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_u, e_w);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e_u), fx.a.mk_int(5)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e_w), fx.a.mk_int(5)));
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Same-base powers with unconstrained exponents are satisfiable.
    static void tst_power_num_cmp_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref M(fx.m.mk_fresh_const("M", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        expr_ref e_m(fx.u.str.mk_power(X, M), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_m, X, M);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, e_m);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Same-base powers with a nonempty base and unequal exponents are
    // unsatisfiable.
    static void tst_power_num_cmp_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref M(fx.m.mk_fresh_const("M", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        expr_ref e_m(fx.u.str.mk_power(X, M), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_m, X, M);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, e_m);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(fx.a.mk_ge(N, fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(fx.a.mk_ge(M, fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_not(fx.m.mk_eq(N, M)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Eliminate a power against an explicit run of its base on the other
    // side: `X^N = X.X.V` is satisfiable.
    static void tst_power_split_elim_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref V(fx.m.mk_fresh_const("V", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        expr_ref rhs(fx.u.str.mk_concat(X, fx.u.str.mk_concat(X, V)), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, rhs);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // power_split_elim, forced unsat: same shape as above but with
    // len(X)=1, len(V)=0 (so the only consistent exponent is N=2) and
    // N pinned to a conflicting value (5) - no witness in either of
    // power_split_elim's two branches (nor anywhere else).
    static void tst_power_split_elim_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref V(fx.m.mk_fresh_const("V", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        expr_ref rhs(fx.u.str.mk_concat(X, fx.u.str.mk_concat(X, V)), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, rhs);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(V), fx.a.mk_int(0)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(N, fx.a.mk_int(5)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // power_peel should make progress on `X^N = Y` when Y is a plain
    // variable.
    static void tst_power_peel_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, Y);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // power_peel, forced unsat: X^N = Y with len(X)=2, len(Y)=5 (not
    // a multiple of len(X)) - power_propagation's own length-only axiom
    // (len(e)=n*len(X) once n>=1, len(e)=0 once n<=0) already refutes
    // this regardless of how power_peel's own two branches are
    // explored, so this exercises that power_peel's presence doesn't
    // introduce an unsound path around that conflict.
    static void tst_power_peel_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, Y);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(2)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(5)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // A variable opposite a multi-token power base should be decomposable
    // at an interior base position.
    static void tst_power_var_decompose_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string(zstring("ab")), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(ab, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, ab, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X, e_n);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // power_var_decompose, forced unsat: X = ("ab")^N together with
    // X = "cd" - no decomposition/extend branch of the power side can
    // ever produce a string starting with 'c' (every branch's
    // replacement for X begins with either "ab"'s own repeated content
    // or, in the plain-char branch, the literal base tokens 'a'/'b'),
    // so this is refuted by ordinary unit-clash detection
    // (word_eq_split/eq_propagation) regardless of which
    // power_var_decompose branch is explored.
    static void tst_power_var_decompose_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string(zstring("ab")), fx.m);
        expr_ref cd(fx.u.str.mk_string(zstring("cd")), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(ab, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, ab, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X, e_n);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X, cd);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // A self-cycle `X = a.b.X` is unsatisfiable by length, and
    // gpower_intro should expose that case.
    static void tst_power_gpower_intro_self_cycle_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref a_(fx.u.str.mk_string(zstring("a")), fx.m);
        expr_ref b_(fx.u.str.mk_string(zstring("b")), fx.m);
        expr_ref ab_X(fx.u.str.mk_concat(a_, fx.u.str.mk_concat(b_, X)), fx.m);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X.get(), ab_X.get());
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // The same self-cycle with `a.a.a.a` should first compress to base
    // `"a"` and remain unsatisfiable.
    static void tst_power_gpower_intro_period_compress_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref a_(fx.u.str.mk_string(zstring("a")), fx.m);
        expr_ref aaaa_X(fx.m);
        {
            expr_ref tail(X);
            for (unsigned i = 0; i < 4; ++i)
                tail = expr_ref(fx.u.str.mk_concat(a_, tail), fx.m);
            aaaa_X = tail;
        }
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X.get(), aaaa_X.get());
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

} // namespace

    // power_facet as subst sink: idempotent add, base rebased on substitution,
    // power token discharged and nested power registered when substituted away.
    static void tst_power_sink_registers_and_rebases() {
        fixture fx;
        auto& pf = fx.root->facet_as<seq::power_facet>(fx.pow_id);
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Xp(fx.m.mk_fresh_const("Xp", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref c(fx.u.str.mk_unit(fx.u.str.mk_char('c')), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        pf.add_power(e_n, X, N);
        pf.add_power(e_n, X, N);
        unsigned idx;
        ENSURE(pf.find_power(e_n, idx));
        ENSURE(pf.powers().size() == 1);

        expr_ref_vector repl(fx.m);
        repl.push_back(c);
        repl.push_back(Xp);
        seq::broadcast_subst(*fx.root, X, repl, nullptr);
        ENSURE(pf.find_power(e_n, idx));
        expr_ref_vector base(fx.m);
        fx.u.str.get_concat_units(pf.powers()[idx].m_s.get(), base);
        ENSURE(base.size() == 2 && base.get(0) == c.get() && base.get(1) == Xp.get());

        expr_ref N1(fx.a.mk_sub(N, fx.a.mk_int(1)), fx.m);
        expr_ref nested(fx.u.str.mk_power(pf.powers()[idx].m_s.get(), N1), fx.m);
        expr_ref_vector repl2(fx.m);
        repl2.push_back(c);
        repl2.push_back(Xp);
        repl2.push_back(nested);
        seq::broadcast_subst(*fx.root, e_n, repl2, nullptr);
        ENSURE(!pf.find_power(e_n, idx));
        ENSURE(pf.find_power(nested, idx));
        ENSURE(pf.powers()[idx].m_n.get() == N1.get());
    }

    // `("ab")^N = Y` with `len(Y) = 12` should stay satisfiable even
    // though solving requires progress beyond the initial split bound.
    static void tst_power_beyond_bound_sat() {
        fixture fx;
        expr_ref ab(fx.u.str.mk_string(zstring("ab")), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(ab, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, ab, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, Y);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(12)));
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // "ab"^N = Y with len(Y)=5: odd length, must be unsat (not unknown).
    static void tst_power_beyond_bound_unsat() {
        fixture fx;
        expr_ref ab(fx.u.str.mk_string(zstring("ab")), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(ab, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, ab, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, Y);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(5)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Length axioms alone should refute `len(X^N) = 3` and `len(X) = 2`.
    static void tst_power_length_only_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e_n), fx.a.mk_int(3)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(2)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // `Y^M = X X X` with unit-length bases should be satisfiable, even
    // when the opposite variable is shorter than one base copy.
    static void tst_power_peel_short_var_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref M(fx.m.mk_fresh_const("M", fx.a.mk_int()), fx.m);
        expr_ref e_m(fx.u.str.mk_power(Y, M), fx.m);
        expr_ref xxx(fx.u.str.mk_concat(X, fx.u.str.mk_concat(X, X)), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_m, Y, M);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_m, xxx);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(1)));
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // `X.Y = ("ab")^N` with `len(Y) = 1` and large `N` should be solved
    // by decomposition rather than repeated peeling.
    static void tst_power_decompose_far_exponent_sat() {
        fixture fx;
        expr_ref ab(fx.u.str.mk_string(zstring("ab")), fx.m);
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m), Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(ab, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, ab, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(fx.u.str.mk_concat(X, Y), e_n);
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(1)));
        fx.root->facet_as<seq::solver_facet>(fx.arith_id).add_constraint(fx.a.mk_ge(N, fx.a.mk_int(100)));
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

void tst_seq_power_facet() {
    tst_power_known_exponent_sat();
    tst_power_known_exponent_conflict();
    tst_power_zero_exponent_unsat();
    tst_power_symbolic_length_conflict_unsat();
    std::cout << "=== test5 ===\n" << std::flush;
    tst_power_symbolic_split_sat();
    std::cout << "=== test5b ===\n" << std::flush;
    tst_power_symbolic_split_unsat();
    std::cout << "=== test5c ===\n" << std::flush;
    tst_fine_wilf_sat();
    std::cout << "=== test5d ===\n" << std::flush;
    tst_fine_wilf_large_exponent_not_refuted();
    std::cout << "=== test5e ===\n" << std::flush;
    tst_fine_wilf_progress_sat();
    std::cout << "=== test5f ===\n" << std::flush;
    tst_power_num_cmp_sat();
    std::cout << "=== test5g ===\n" << std::flush;
    tst_power_num_cmp_unsat();
    std::cout << "=== test5h ===\n" << std::flush;
    tst_power_split_elim_sat();
    std::cout << "=== test5i ===\n" << std::flush;
    tst_power_split_elim_unsat();
    std::cout << "=== test5j ===\n" << std::flush;
    tst_power_peel_sat();
    std::cout << "=== test5k ===\n" << std::flush;
    tst_power_peel_unsat();
    std::cout << "=== test5l ===\n" << std::flush;
    tst_power_var_decompose_sat();
    std::cout << "=== test5m ===\n" << std::flush;
    tst_power_var_decompose_unsat();
    std::cout << "=== test5n ===\n" << std::flush;
    tst_power_gpower_intro_self_cycle_unsat();
    std::cout << "=== test5o ===\n" << std::flush;
    tst_power_gpower_intro_period_compress_unsat();
    std::cout << "=== test6 ===\n" << std::flush;
    tst_power_sink_registers_and_rebases();
    std::cout << "=== test6b ===\n" << std::flush;
    tst_power_beyond_bound_sat();
    std::cout << "=== test6c ===\n" << std::flush;
    tst_power_beyond_bound_unsat();
    std::cout << "=== test6d ===\n" << std::flush;
    tst_power_length_only_unsat();
    std::cout << "=== test6e ===\n" << std::flush;
    tst_power_peel_short_var_sat();
    std::cout << "=== test6f ===\n" << std::flush;
    tst_power_decompose_far_exponent_sat();
    std::cout << "seq_power_facet: all tests passed\n";
}
