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
        seq::power_fine_wilf     pfw;
        seq::power_num_cmp       pnc;
        seq::power_split_elim    pse;
        seq::power_var_peel      pvp;
        seq::power_var_decompose pvd;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), a(m), s(u.str.mk_string_sort()),
            root(tree.mk_root()),
            solver(m, a, tree.dep_mgr()),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            arith_id(tree.register_facet<seq::arith_facet>(*root, m, u, solver)),
            pow_id(tree.register_facet<seq::power_facet>(*root, m, u, a, tree.dep_mgr())),
            eprop(eq_id), esplit(m, u, eq_id), aprop(arith_id, eq_id),
            pprop(m, u, a, pow_id, eq_id, arith_id), psplit(m, u, a, pow_id, eq_id, arith_id),
            pfw(m, u, a, pow_id, eq_id, arith_id),
            pnc(m, u, a, pow_id, eq_id, arith_id),
            pse(m, u, a, pow_id, eq_id, arith_id),
            pvp(m, u, a, pow_id, eq_id, arith_id),
            pvd(m, u, a, pow_id, eq_id, arith_id)
        {
            tree.add_propagation_plugin(&eprop);
            tree.add_propagation_plugin(&aprop);
            tree.add_propagation_plugin(&pprop);
            tree.add_split_plugin(&psplit);
            tree.add_split_plugin(&pfw);
            tree.add_split_plugin(&pnc);
            tree.add_split_plugin(&pse);
            tree.add_split_plugin(&pvp);
            tree.add_split_plugin(&pvd);
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

    // Fine & Wilf trigger, arithmetic-only conflict: e_u = X^n (base X),
    // e_w = Y^m (base Y, distinct term from X) with equation e_u = e_w
    // (Y-run empty, so this is exactly power_fine_wilf's trigger
    // pattern with two *distinct* bases). Forcing len(e_u) way past any
    // bound power_split could ever unfold to (n is left otherwise
    // unconstrained) must still be refutable: arith_propagation's
    // automatic add_length_constraint over this same equation forces
    // len(e_u)=len(e_w), and power_fine_wilf's case-1 side constraint
    // `len(e_u)-0 < T \/ len(e_w) < T` (T = len(X)+len(Y) = 2, since X,Y
    // are both length-1 fresh string constants) then has no way to hold
    // once len(e_u)=len(e_w)=1000, exercising the plugin's arithmetic
    // path directly rather than power_split's bounded combinatorial
    // unfold (whose default bound of 5 could never itself witness or
    // refute an exponent this large).
    static void tst_fine_wilf_large_exponent_unsat() {
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
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e_u), fx.a.mk_int(1000)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
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

    // Force Fine & Wilf's progress cases (2/3), not case 1: X, Y both
    // fixed-length-1 constants, and e_u/e_w's *lengths* are pinned to
    // values that make case 1's disjunction
    // (len(e_u)-Ly<T \/ len(e_w)<T, with Ly=0, T=len(X)+len(Y)=2)
    // false outright (both len(e_u), len(e_w) forced to 5 >= T), so the
    // only way this equation can be satisfied is via case 2 or case 3's
    // string-level elimination (introducing R1/R2 or S1/S2 and relating
    // them back to eq_facet/arith_facet) - must still be sat, since
    // n=m=5 with X=Y-as-strings-of-equal-content is a genuine solution
    // once the fresh split variables are unified consistently.
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
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e_u), fx.a.mk_int(5)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(e_w), fx.a.mk_int(5)));
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Same-base power-vs-power comparison (`apply_num_cmp`): X^n = X^m
    // for the *same* base X, with n and m otherwise unconstrained -
    // must be sat regardless of which of power_num_cmp's two branches
    // (n<m or m<=n) is explored, since n=m=0 (both sides epsilon) is
    // always a witness.
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

    // Same-base power-vs-power comparison, forced unsat: X^n = X^m with
    // len(X) pinned to 1 and n, m forced *disequal* (n >= m+1 or
    // m >= n+1 via a disjunction that excludes n=m) - since X is a
    // fixed nonempty base, X^n = X^m forces n=m, so no witness exists
    // in either of power_num_cmp's two branches.
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
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(fx.a.mk_ge(N, fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(fx.a.mk_ge(M, fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_not(fx.m.mk_eq(N, M)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // power_split_elim ("apply_split_power_elim" in c3): X^N = X.X.V
    // where the *other* side (X.X.V) contains a literal run of X's own
    // base pattern (matched token-by-token via comm_power) rather than
    // a single opposing power token (power_num_cmp's territory) - must
    // be sat, e.g. via N=2, V=epsilon.
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
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(1)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(V), fx.a.mk_int(0)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(N, fx.a.mk_int(5)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // power_var_peel ("apply_var_num_unwinding_eq" in c3): X^N = Y where
    // Y is a plain Nielsen-substitutable variable (not a unit, not a
    // power) - word_eq_split itself explicitly skips any equation whose
    // head is a power, so without power_var_peel this equation could
    // never make progress. Must be sat, e.g. via N=0 (X^0=epsilon=Y).
    static void tst_power_var_peel_sat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, Y);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // power_var_peel, forced unsat: X^N = Y with len(X)=2, len(Y)=5 (not
    // a multiple of len(X)) - power_propagation's own length-only axiom
    // (len(e)=n*len(X) once n>=1, len(e)=0 once n<=0) already refutes
    // this regardless of how power_var_peel's own two branches are
    // explored, so this exercises that power_var_peel's presence doesn't
    // introduce an unsound path around that conflict.
    static void tst_power_var_peel_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref Y(fx.m.mk_fresh_const("Y", fx.s), fx.m);
        expr_ref N(fx.m.mk_fresh_const("N", fx.a.mk_int()), fx.m);
        expr_ref e_n(fx.u.str.mk_power(X, N), fx.m);
        fx.root->facet_as<seq::power_facet>(fx.pow_id).add_power(e_n, X, N);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(e_n, Y);
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(X), fx.a.mk_int(2)));
        fx.root->facet_as<seq::arith_facet>(fx.arith_id).add_constraint(
            fx.m.mk_eq(fx.u.str.mk_length(Y), fx.a.mk_int(5)));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // power_var_decompose ("apply_power_split" in c3): a variable facing
    // a power whose base is multi-token allows decomposing the base at
    // an interior position - e.g. X = ("ab")^N with X a Nielsen variable
    // should be sat, exercising both a "plain-char" decomposition branch
    // (position 1: X := ("ab")^m . "a") and the final "extend past"
    // branch.
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

} // namespace

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
    tst_fine_wilf_large_exponent_unsat();
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
    tst_power_var_peel_sat();
    std::cout << "=== test5k ===\n" << std::flush;
    tst_power_var_peel_unsat();
    std::cout << "=== test5l ===\n" << std::flush;
    tst_power_var_decompose_sat();
    std::cout << "=== test5m ===\n" << std::flush;
    tst_power_var_decompose_unsat();
    std::cout << "seq_power_facet: all tests passed\n";
}
