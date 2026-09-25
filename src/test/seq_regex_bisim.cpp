// Regression test for the seq::derive::intersect_intervals bug.
//
// Background: derive uses a path-tracking interval set to compute symbolic
// derivatives.  The intersect_intervals routine used to react to a single
// disjoint interval by dropping the entire kept suffix and skipping the rest
// of the list, which silently killed valid branches in derivatives such as
// D(a|b).  That made the bisimulation procedure conclude bogus equalities
// like a* == (a|b)*.
//
// This file also covers the seq::derive top-level-cache poisoning bug.
// `m_top_cache` is keyed only by the regex; the routine used to populate it
// while `m_ele` was set to a *concrete* character, baking that character
// into the cached "symbolic" derivative.  Subsequent calls with the same
// regex but a different ele then returned a stale concrete answer instead
// of the true symbolic derivative.  The simplest victim is
//   (str.in_re "aP" (re.++ (re.* "a") "P"))
// which used to return false because the derivative wrt 'a' was cached and
// re-used as the derivative wrt 'P'.
//
// Derivative unions must also use the rewriter's ordered, right-associated
// normal form so equivalent operand orderings share the same residual.
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_regex_bisim.h"
#include "ast/rewriter/th_rewriter.h"
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
        if (m.is_ite(e, c, t, f) || u.re.is_union(e, t, f)) {
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

// Regression for the derive top-level-cache poisoning bug.
// Take r = (re.* "a") ++ "P" and check str.in_re "aP" r.  Before the fix
// the first per-char derivative call (wrt 'a') populated m_top_cache with
// 'a' baked into the symbolic ITE-tree, so the next call (wrt 'P') returned
// that stale cached value instead of computing D_P(r) = epsilon, making
// str.in_re wrongly return false.
static void test_derive_cache_per_ele() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);

    sort_ref str_sort(u.str.mk_string_sort(), m);

    zstring sa("a"), sP("P"), s_aP("aP");
    expr_ref re_a(u.re.mk_to_re(u.str.mk_string(sa)), m);
    expr_ref re_P(u.re.mk_to_re(u.str.mk_string(sP)), m);
    expr_ref a_star(u.re.mk_star(re_a), m);
    expr_ref r(u.re.mk_concat(a_star, re_P), m);
    expr_ref aP(u.str.mk_string(s_aP), m);

    // Compute D_'a'(a*P) and D_'P'(a*P) directly via mk_derivative.
    // Before the fix, m_top_cache was populated while m_ele = ele (the
    // concrete char), so the second call hit the stale cached answer from
    // the first.  After the fix the cache is keyed by a symbolic var, so
    // each concrete-ele substitution produces the right answer.
    expr_ref ch_a(u.mk_char('a'), m);
    expr_ref ch_P(u.mk_char('P'), m);
    expr_ref d_a = rw.mk_derivative(ch_a, r);
    expr_ref d_P = rw.mk_derivative(ch_P, r);
    std::cout << "D_a(a*P) = " << mk_pp(d_a, m) << "\n";
    std::cout << "D_P(a*P) = " << mk_pp(d_P, m) << "\n";

    // D_P(a*P) must be nullable (it accepts the empty suffix), while
    // D_a(a*P) must not be (it still needs a trailing 'P').
    expr_ref n_a = rw.is_nullable(d_a);
    expr_ref n_P = rw.is_nullable(d_P);
    th_rewriter trw(m);
    trw(n_a);
    trw(n_P);
    std::cout << "nullable(D_a) = " << mk_pp(n_a, m) << "\n";
    std::cout << "nullable(D_P) = " << mk_pp(n_P, m) << "\n";
    ENSURE(m.is_false(n_a));
    ENSURE(m.is_true(n_P));
}

static void test_derive_union_normalization() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);
    auto literal = [&](char const* s) {
        return expr_ref(u.re.mk_to_re(u.str.mk_string(zstring(s))), m);
    };

    // Multi-character residuals prevent character-range collapsing from
    // hiding a noncanonical union tree.
    expr_ref axx = literal("axx"), ayy = literal("ayy"), azz = literal("azz");
    expr_ref xx = literal("xx"), yy = literal("yy"), zz = literal("zz");
    expr_ref xy(u.re.mk_union(axx, ayy), m);
    expr_ref yx(u.re.mk_union(ayy, axx), m);
    expr_ref yz(u.re.mk_union(ayy, azz), m);
    expr_ref_vector inputs(m);
    inputs.push_back(u.re.mk_union(xy, azz));
    inputs.push_back(u.re.mk_union(azz, yx));
    inputs.push_back(u.re.mk_union(axx, yz));
    inputs.push_back(u.re.mk_union(inputs.get(0), axx));
    expr_ref expected = rw.mk_union(xx, rw.mk_union(yy, zz));
    expr_ref ch_a(u.mk_char('a'), m);

    for (expr* input : inputs) {
        for (auto kind : {seq::derivative_kind::antimirov_t, seq::derivative_kind::brzozowski_t}) {
            expr_ref derivative = rw.get_derive()(kind, ch_a, input);
            ENSURE(derivative == expected);
        }

        expr_ref_pair_vector cofactors(m);
        rw.brz_derivative_cofactors(input, cofactors);
        unsigned nonempty_targets = 0;
        for (auto const& cofactor : cofactors) {
            if (u.re.is_empty(cofactor.second))
                continue;
            ++nonempty_targets;
            ENSURE(cofactor.second == expected);
        }
        ENSURE(nonempty_targets == 1);
    }

    expr_ref not_axx(u.re.mk_complement(axx), m);
    expr_ref complemented(u.re.mk_union(yz, not_axx), m);
    expected = rw.mk_union(rw.mk_complement(xx), rw.mk_union(yy, zz));
    expr_ref derivative = rw.get_derive()(seq::derivative_kind::brzozowski_t, ch_a, complemented);
    ENSURE(derivative == expected);

    expr_ref a = literal("a");
    expr_ref optional_a(u.re.mk_opt(a), m);
    expr_ref tail = rw.mk_union(axx, rw.mk_union(ayy, azz));
    expr_ref nullable_concat(u.re.mk_concat(optional_a, tail), m);
    expected = rw.mk_union(tail, rw.mk_union(xx, rw.mk_union(yy, zz)));
    for (auto kind : {seq::derivative_kind::antimirov_t, seq::derivative_kind::brzozowski_t}) {
        derivative = rw.get_derive()(kind, ch_a, nullable_concat);
        ENSURE(derivative == expected);
    }
}

static void test_derive_reverse_union_normalization() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);
    sort_ref re_sort(u.re.mk_re(u.str.mk_string_sort()), m);
    expr_ref digit(u.re.mk_range(re_sort, '0', '1'), m);
    expr_ref ab(u.re.mk_range(re_sort, 'a', 'b'), m);
    expr_ref cd(u.re.mk_range(re_sort, 'c', 'd'), m);
    expr_ref ef(u.re.mk_range(re_sort, 'e', 'f'), m);
    expr_ref dab(u.re.mk_concat(digit, ab), m);
    expr_ref dcd(u.re.mk_concat(digit, cd), m);
    expr_ref def(u.re.mk_concat(digit, ef), m);
    expr_ref abd(u.re.mk_concat(ab, digit), m);
    expr_ref cdd(u.re.mk_concat(cd, digit), m);
    expr_ref efd(u.re.mk_concat(ef, digit), m);
    expr_ref reversed_body = rw.mk_union(abd, rw.mk_union(cdd, efd));
    expr_ref reversed_star(u.re.mk_star(reversed_body), m);
    expr_ref expected(u.re.mk_concat(digit, reversed_star), m);

    expr_ref first_two(u.re.mk_union(dab, dcd), m);
    expr_ref last_two(u.re.mk_union(dcd, def), m);
    expr_ref_vector inputs(m);
    inputs.push_back(u.re.mk_union(first_two, def));
    inputs.push_back(u.re.mk_union(def, first_two));
    inputs.push_back(u.re.mk_union(dab, last_two));

    // The union survives inside the star tail of each derivative.
    for (expr* body : inputs) {
        expr_ref star(u.re.mk_star(body), m);
        expr_ref reversed(u.re.mk_reverse(star), m);
        for (unsigned c : {'a', 'c', 'e'}) {
            expr_ref ch(u.mk_char(c), m);
            for (auto kind : {seq::derivative_kind::antimirov_t, seq::derivative_kind::brzozowski_t}) {
                expr_ref derivative = rw.get_derive()(kind, ch, reversed);
                ENSURE(derivative == expected);
            }
        }
    }
}

void tst_seq_regex_bisim() {
    test_a_star_neq_ab_star();
    test_derive_cache_per_ele();
    test_derive_union_normalization();
    test_derive_reverse_union_normalization();
}
