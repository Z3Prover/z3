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

static void test_derive_concat_normalization() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);
    sort_ref re_sort(u.re.mk_re(u.str.mk_string_sort()), m);
    expr_ref full(u.re.mk_full_seq(re_sort), m);
    expr_ref ab(u.re.mk_range(re_sort, 'a', 'b'), m);
    expr_ref cd(u.re.mk_range(re_sort, 'c', 'd'), m);
    expr_ref ef(u.re.mk_range(re_sort, 'e', 'f'), m);
    expr_ref body = rw.mk_re_append(full, rw.mk_re_append(ab, full));
    expr_ref ch_z(u.mk_char('z'), m), ch_a(u.mk_char('a'), m);
    auto literal = [&](char const* s) {
        return expr_ref(u.re.mk_to_re(u.str.mk_string(zstring(s))), m);
    };

    for (auto kind : {seq::derivative_kind::antimirov_t, seq::derivative_kind::brzozowski_t}) {
        for (unsigned n : {3u, 30u, 40u, 50u}) {
            expr_ref loop(u.re.mk_loop(body, n, n), m);
            expr_ref derivative = rw.get_derive()(kind, ch_z, loop);
            ENSURE(derivative == loop);
        }
        expr_ref loop(u.re.mk_loop(body, 2, 4), m);
        ENSURE(rw.get_derive()(kind, ch_z, loop) == loop);

        expr_ref ax = literal("ax"), yz = literal("yz"), xyz = literal("xyz");
        expr_ref strings(u.re.mk_concat(ax, yz), m);
        ENSURE(rw.get_derive()(kind, ch_a, strings) == xyz);

        expr_ref left(u.re.mk_concat(literal("a"), ab), m);
        left = u.re.mk_concat(left, cd);
        left = u.re.mk_concat(left, ef);
        expr_ref expected = rw.mk_re_append(ab, rw.mk_re_append(cd, ef));
        ENSURE(rw.get_derive()(kind, ch_a, left) == expected);
    }
}

static void test_derive_repetition_normalization() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);
    sort_ref re_sort(u.re.mk_re(u.str.mk_string_sort()), m);
    expr_ref ab(u.re.mk_range(re_sort, 'a', 'b'), m);
    expr_ref star(u.re.mk_star(ab), m), plus(u.re.mk_plus(ab), m);
    expr_ref ch_a(u.mk_char('a'), m);
    expr_ref_vector inputs(m);
    inputs.push_back(u.re.mk_star(star));
    inputs.push_back(u.re.mk_star(plus));
    inputs.push_back(u.re.mk_plus(star));
    inputs.push_back(u.re.mk_loop(ab, 1));

    for (auto kind : {seq::derivative_kind::antimirov_t, seq::derivative_kind::brzozowski_t}) {
        for (expr* input : inputs)
            ENSURE(rw.get_derive()(kind, ch_a, input) == star);

        expr_ref twice(u.re.mk_loop(ab, 2, 2), m);
        expr_ref six(u.re.mk_loop(twice, 3, 3), m);
        expr_ref five(u.re.mk_loop(ab, 5, 5), m);
        ENSURE(rw.get_derive()(kind, ch_a, six) == five);
    }
}

static void test_derive_reverse_smart_constructors() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);
    sort_ref re_sort(u.re.mk_re(u.str.mk_string_sort()), m);
    expr_ref ab(u.re.mk_range(re_sort, 'a', 'b'), m);
    expr_ref af(u.re.mk_range(re_sort, 'a', 'f'), m);
    expr_ref cz(u.re.mk_range(re_sort, 'c', 'z'), m);
    expr_ref cf(u.re.mk_range(re_sort, 'c', 'f'), m);
    expr_ref cf_star(u.re.mk_star(cf), m);
    expr_ref ab_star(u.re.mk_star(ab), m);
    expr_ref ch_a(u.mk_char('a'), m), ch_c(u.mk_char('c'), m);
    expr_ref twice(u.re.mk_loop(ab, 2, 2), m);
    expr_ref repeated(u.re.mk_concat(ab, twice), m);
    expr_ref reversed(u.re.mk_reverse(repeated), m);

    for (auto kind : {seq::derivative_kind::antimirov_t, seq::derivative_kind::brzozowski_t}) {
        ENSURE(rw.get_derive()(kind, ch_a, reversed) == twice);

        expr_ref_vector bodies(m);
        bodies.push_back(u.re.mk_inter(af, cz));
        bodies.push_back(u.re.mk_diff(af, ab));
        for (expr* body : bodies) {
            expr_ref input(u.re.mk_reverse(u.re.mk_star(body)), m);
            ENSURE(rw.get_derive()(kind, ch_c, input) == cf_star);
        }
        bodies.reset();
        bodies.push_back(u.re.mk_complement(u.re.mk_complement(ab)));
        bodies.push_back(u.re.mk_loop(ab, 0u));
        bodies.push_back(u.re.mk_opt(ab));
        for (expr* body : bodies) {
            expr_ref input(u.re.mk_reverse(u.re.mk_star(body)), m);
            ENSURE(rw.get_derive()(kind, ch_a, input) == ab_star);
        }

        expr_ref ba(u.re.mk_to_re(u.str.mk_string(zstring("ba"))), m);
        expr_ref b(u.re.mk_to_re(u.str.mk_string(zstring("b"))), m);
        expr_ref reverse_ba(u.re.mk_reverse(ba), m);
        ENSURE(rw.get_derive()(kind, ch_a, reverse_ba) == b);
    }
}

static void test_cofactor_smart_constructors() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);
    sort_ref re_sort(u.re.mk_re(u.str.mk_string_sort()), m);
    expr_ref ele(m.mk_var(0, u.mk_char_sort()), m);
    expr_ref guard(m.mk_eq(ele, u.mk_char('a')), m);
    expr_ref empty(u.re.mk_empty(re_sort), m);
    expr_ref full(u.re.mk_full_seq(re_sort), m);
    expr_ref epsilon(u.re.mk_to_re(u.str.mk_string(zstring(""))), m);
    expr_ref ab(u.re.mk_range(re_sort, 'a', 'b'), m);
    expr_ref twice(u.re.mk_loop(ab, 2, 2), m);
    expr_ref thrice(u.re.mk_loop(ab, 3, 3), m);

    auto check = [&](expr* input, expr* first, expr* second = nullptr) {
        expr_ref_pair_vector cofactors(m);
        rw.get_cofactors(ele, input, cofactors);
        ENSURE(cofactors.size() == (second ? 2u : first ? 1u : 0u));
        bool found_first = false, found_second = false;
        for (auto const& [condition, target] : cofactors) {
            ENSURE(target == first || target == second);
            found_first |= target == first;
            found_second |= target == second;
        }
        ENSURE(!first || found_first);
        ENSURE(!second || found_second);
    };

    expr_ref conditional_ab(m.mk_ite(guard, ab, empty), m);
    expr_ref concat(u.re.mk_concat(conditional_ab, twice), m);
    check(concat, thrice);

    expr_ref conditional(m.mk_ite(guard, full, empty), m);
    expr_ref complement(u.re.mk_complement(conditional), m);
    check(complement, full);
    expr_ref plus(u.re.mk_plus(conditional), m);
    check(plus, full);
    expr_ref optional(u.re.mk_opt(conditional), m);
    check(optional, full, epsilon);
    expr_ref star(u.re.mk_star(conditional), m);
    check(star, full, epsilon);
    expr_ref loop(u.re.mk_loop(conditional, 0u), m);
    check(loop, full, epsilon);
    expr_ref xor_re(u.re.mk_xor(conditional, full), m);
    check(xor_re, full);

    expr_ref nested(u.re.mk_complement(u.re.mk_complement(concat)), m);
    check(nested, thrice);

    expr_ref unknown(m.mk_fresh_const("R", re_sort), m);
    expr_ref stuck(u.re.mk_derivative(ele, unknown), m);
    check(stuck, stuck);
}

static void test_shared_regex_constructor_boundaries() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    seq_rewriter rw(m);
    sort_ref re_sort(u.re.mk_re(u.str.mk_string_sort()), m);
    expr_ref ab(u.re.mk_range(re_sort, 'a', 'b'), m);
    expr_ref full(u.re.mk_full_seq(re_sort), m);
    expr_ref dot(u.re.mk_full_char(re_sort), m);
    expr_ref dot_plus(u.re.mk_plus(dot), m);
    expr_ref epsilon = rw.mk_to_re(u.str.mk_string(zstring("")));
    ENSURE(rw.mk_plus(dot) == dot_plus);
    ENSURE(rw.mk_re_append(dot, full) == dot_plus);
    ENSURE(rw.mk_re_append(full, dot) == dot_plus);
    ENSURE(rw.mk_complement(epsilon) == dot_plus);
    ENSURE(rw.mk_star(dot_plus) == full);
    ENSURE(rw.mk_re_xor_simplified(full, rw.mk_complement(ab)) == ab);

    expr_ref max_loop = rw.mk_loop(ab, UINT_MAX, UINT_MAX);
    expr_ref almost_max = rw.mk_loop(ab, UINT_MAX - 1, UINT_MAX - 1);
    expr_ref twice = rw.mk_loop(ab, 2, 2);
    ENSURE(rw.mk_re_append(ab, almost_max) == max_loop);
    ENSURE(rw.mk_re_append(almost_max, ab) == max_loop);
    ENSURE(u.re.is_concat(rw.mk_re_append(ab, max_loop)));
    ENSURE(u.re.is_concat(rw.mk_re_append(max_loop, ab)));
    ENSURE(u.re.is_concat(rw.mk_re_append(max_loop, twice)));
    expr_ref unbounded = rw.mk_loop(ab, UINT_MAX);
    expr_ref one_or_more = rw.mk_loop(ab, 1);
    ENSURE(u.re.is_concat(rw.mk_re_append(unbounded, one_or_more)));
    ENSURE(u.re.is_concat(rw.mk_re_append(unbounded, twice)));

    expr_ref many = rw.mk_loop(ab, 65536, 65536);
    expr_ref nested = rw.mk_loop(many, 65536, 65536);
    expr* inner = nullptr;
    unsigned lo = 0, hi = 0;
    ENSURE(u.re.is_loop(nested, inner, lo, hi));
    ENSURE(inner == many && lo == 65536 && hi == 65536);
    many = rw.mk_loop(ab, 65536);
    nested = rw.mk_loop(many, 65536);
    ENSURE(u.re.is_loop(nested, inner, lo));
    ENSURE(inner == many && lo == 65536);

    expr_ref at_least_two = rw.mk_loop(ab, 2);
    expr_ref zero_or_at_least_two = rw.mk_loop(at_least_two, 0);
    ENSURE(u.re.is_star(zero_or_at_least_two, inner) && inner == at_least_two);
    expr_ref ch_a(u.mk_char('a'), m);
    for (auto kind : {seq::derivative_kind::antimirov_t, seq::derivative_kind::brzozowski_t}) {
        expr_ref derivative = rw.get_derive()(kind, ch_a, zero_or_at_least_two);
        ENSURE(m.is_false(rw.is_nullable(derivative)));
    }
}

void tst_seq_regex_bisim() {
    test_a_star_neq_ab_star();
    test_derive_cache_per_ele();
    test_derive_union_normalization();
    test_derive_reverse_union_normalization();
    test_derive_concat_normalization();
    test_derive_repetition_normalization();
    test_derive_reverse_smart_constructors();
    test_cofactor_smart_constructors();
    test_shared_regex_constructor_boundaries();
}
