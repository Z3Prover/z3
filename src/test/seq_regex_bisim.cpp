// Regression test for the seq::derive::intersect_intervals bug.
//
// Background: derive uses a path-tracking interval set to compute symbolic
// derivatives.  The intersect_intervals routine used to react to a single
// disjoint interval by dropping the entire kept suffix and skipping the rest
// of the list, which silently killed valid branches in derivatives such as
// D(a|b).  That made the bisimulation procedure conclude bogus equalities
// like a* == (a|b)*.
//
// This test asserts the basic shape of the derivative and the bisim result
// for that minimal case, so the bug cannot silently regress.
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_regex_bisim.h"
#include <iostream>

static void test_a_star_neq_ab_star() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);

    sort_ref str_sort(u.str.mk_string_sort(), m);

    zstring sa("a"), sb("b");
    expr_ref re_a(u.re.mk_to_re(u.str.mk_string(sa)), m);
    expr_ref re_b(u.re.mk_to_re(u.str.mk_string(sb)), m);
    expr_ref a_star(u.re.mk_star(re_a), m);
    expr_ref ab(u.re.mk_union(re_a, re_b), m);
    expr_ref ab_star(u.re.mk_star(ab), m);

    expr_ref d_ab = rw.mk_brz_derivative(ab);
    std::cout << "D(a|b) = " << mk_pp(d_ab, m) << "\n";

    // Both the 'a' branch and the 'b' branch of D(a|b) must reach epsilon.
    // Collect the regex leaves of the symbolic derivative and require at
    // least two distinct accepting leaves (one for 'a' and one for 'b').
    expr_ref_vector leaves(m);
    auto collect = [&](expr* e, auto&& self) -> void {
        expr* c, *t, *f;
        if (m.is_ite(e, c, t, f) || u.re.is_union(e, t, f) || u.re.is_antimirov_union(e, t, f)) {
            self(t, self);
            self(f, self);
            return;
        }
        if (u.re.is_empty(e)) return;
        leaves.push_back(e);
    };
    collect(d_ab, collect);
    unsigned nullable_leaves = 0;
    for (expr* l : leaves) {
        expr_ref n = rw.is_nullable(l);
        if (m.is_true(n)) ++nullable_leaves;
    }
    std::cout << "D(a|b) leaves=" << leaves.size()
              << " nullable=" << nullable_leaves << "\n";
    ENSURE(nullable_leaves >= 2);

    // Bisim must report the two languages are not equivalent.
    seq::regex_bisim bisim(rw);
    lbool eq = bisim.are_equivalent(a_star, ab_star);
    std::cout << "bisim(a*, (a|b)*) = "
              << (eq == l_true ? "true" : eq == l_false ? "false" : "undef") << "\n";
    ENSURE(eq == l_false);
}

void tst_seq_regex_bisim() {
    test_a_star_neq_ab_star();
}
