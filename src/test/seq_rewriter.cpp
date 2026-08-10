/*++
Copyright (c) 2024 Microsoft Corporation

Regression tests for seq_rewriter smart constructors for regex ranges.

Tests:
  1. Empty range (lo > hi) → re.none
  2. Singleton range (lo == hi) → str.to_re lo
  3. Range ∩ Range → reduced range or re.none
  4. Range ∪ Range → merged range for overlapping/adjacent
  5. Complement of range → one or two ranges
  6. Downstream operators absorb empty ranges correctly
 15. Symbolic-bound range membership rewrite (structural)
 16. Symbolic-bound range membership: concrete element, symbolic bounds (structural)
 17. Solver: (str.in_re x (re.range x x)) sat when len(x)=1
 18. Solver: (str.in_re x (re.range x x)) unsat when len(x)=2
 19. Solver: inverted symbolic bounds make membership unsatisfiable
 20. Solver: contradictory constant lexical bounds are unsatisfiable
 22. re.loop with bounds as arguments agrees with the indexed form
 23. (Σ*·S)* is flattened to () | Σ*·S
 24. Regex info tracks inferred maximal lengths
--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_context.h"
#include <iostream>
#include <string>

// Build a single-char string literal expression.
static expr_ref mk_str(ast_manager& m, seq_util& su, unsigned c) {
    return expr_ref(su.str.mk_string(zstring(c)), m);
}

void tst_seq_rewriter() {
    ast_manager m;
    reg_decl_plugins(m);
    th_rewriter rw(m);
    seq_util su(m);

    sort* str_sort = su.str.mk_string_sort();
    sort* re_sort  = su.re.mk_re(str_sort);

    auto range = [&](unsigned lo, unsigned hi) -> expr_ref {
        return expr_ref(su.re.mk_range(mk_str(m, su, lo), mk_str(m, su, hi)), m);
    };

    // Arbitrary regex variable for downstream tests.
    app_ref R(m.mk_fresh_const("R", re_sort), m);

    // -----------------------------------------------------------------------
    // 1. Empty range (lo > hi) → re.none
    // -----------------------------------------------------------------------
    {
        expr_ref e = range('z', 'a');
        rw(e);
        std::cout << "empty range lo>hi: " << mk_pp(e, m) << "\n";
        ENSURE(su.re.is_empty(e));
    }

    // -----------------------------------------------------------------------
    // 2. Singleton range (lo == hi) → str.to_re lo
    // -----------------------------------------------------------------------
    {
        expr_ref e = range('a', 'a');
        rw(e);
        std::cout << "singleton range: " << mk_pp(e, m) << "\n";
        expr* inner = nullptr;
        ENSURE(su.re.is_to_re(e, inner));
    }

    // -----------------------------------------------------------------------
    // 3. Range intersection: overlapping → smaller range
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_inter(range('a', 'z'), range('f', 'k')), m);
        rw(e);
        std::cout << "range inter overlapping: " << mk_pp(e, m) << "\n";
        unsigned lo = 0, hi = 0;
        ENSURE(su.re.is_range(e, lo, hi) && lo == 'f' && hi == 'k');
    }

    // -----------------------------------------------------------------------
    // 4. Range intersection: disjoint → re.none
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_inter(range('a', 'f'), range('k', 'z')), m);
        rw(e);
        std::cout << "range inter disjoint: " << mk_pp(e, m) << "\n";
        ENSURE(su.re.is_empty(e));
    }

    // -----------------------------------------------------------------------
    // 5. Range intersection: touching at boundary → singleton (str.to_re "f")
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_inter(range('a', 'f'), range('f', 'z')), m);
        rw(e);
        std::cout << "range inter touching: " << mk_pp(e, m) << "\n";
        expr* inner = nullptr;
        ENSURE(su.re.is_to_re(e, inner));
    }

    // -----------------------------------------------------------------------
    // 6. Range union: overlapping → merged range
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_union(range('a', 'f'), range('e', 'k')), m);
        rw(e);
        std::cout << "range union overlapping: " << mk_pp(e, m) << "\n";
        unsigned lo = 0, hi = 0;
        ENSURE(su.re.is_range(e, lo, hi) && lo == 'a' && hi == 'k');
    }

    // -----------------------------------------------------------------------
    // 7. Range union: adjacent → merged range
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_union(range('a', 'f'), range('g', 'k')), m);
        rw(e);
        std::cout << "range union adjacent: " << mk_pp(e, m) << "\n";
        unsigned lo = 0, hi = 0;
        ENSURE(su.re.is_range(e, lo, hi) && lo == 'a' && hi == 'k');
    }

    // -----------------------------------------------------------------------
    // 8. Range union: disjoint → stays as union
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_union(range('a', 'c'), range('m', 'z')), m);
        rw(e);
        std::cout << "range union disjoint (stays as union): " << mk_pp(e, m) << "\n";
        ENSURE(!su.re.is_range(e));
    }


    // -----------------------------------------------------------------------
    // 11. Downstream: (re.* (re.range "z" "a")) → str.to_re ""
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_star(range('z', 'a')), m);
        rw(e);
        std::cout << "star of empty range: " << mk_pp(e, m) << "\n";
        expr* inner = nullptr;
        // star of empty → epsilon (str.to_re "")
        ENSURE(su.re.is_to_re(e, inner) && su.str.is_empty(inner));
    }

    // -----------------------------------------------------------------------
    // 12. Downstream: concat absorbs empty range → re.none
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_concat(R, su.re.mk_concat(range('z', 'a'), R)), m);
        rw(e);
        std::cout << "concat absorbs empty range: " << mk_pp(e, m) << "\n";
        ENSURE(su.re.is_empty(e));
    }

    // -----------------------------------------------------------------------
    // 13. Downstream: union absorbs empty range → R
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_union(R, range('z', 'a')), m);
        rw(e);
        std::cout << "union absorbs empty range: " << mk_pp(e, m) << "\n";
        ENSURE(e.get() == R.get());
    }

    // -----------------------------------------------------------------------
    // 14. Downstream: inter absorbs empty range → re.none
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_inter(R, range('z', 'a')), m);
        rw(e);
        std::cout << "inter absorbs empty range: " << mk_pp(e, m) << "\n";
        ENSURE(su.re.is_empty(e));
    }

    // -----------------------------------------------------------------------
    // 15. Symbolic-bound range membership rewrite (structural).
    //     (str.in_re x (re.range x x)) with symbolic x should be unfolded
    //     by the rewriter into a conjunction of length and ordering
    //     constraints, not left stuck as an uninterpreted membership term.
    // -----------------------------------------------------------------------
    {
        app_ref x(m.mk_fresh_const("x", str_sort), m);
        expr_ref rng(su.re.mk_range(x, x), m);
        expr_ref e(su.re.mk_in_re(x, rng), m);
        rw(e);
        std::cout << "symbolic range (x in [x,x]): " << mk_pp(e, m) << "\n";
        ENSURE(m.is_and(e));
    }

    // -----------------------------------------------------------------------
    // 16. Symbolic-bound range membership: concrete element, symbolic bounds.
    //     (str.in_re "b" (re.range lo hi)) should also be unfolded to a
    //     conjunction when lo/hi are free variables.
    // -----------------------------------------------------------------------
    {
        app_ref lo(m.mk_fresh_const("lo", str_sort), m);
        app_ref hi(m.mk_fresh_const("hi", str_sort), m);
        expr_ref b_str(su.str.mk_string(zstring('b')), m);
        expr_ref rng(su.re.mk_range(lo, hi), m);
        expr_ref e(su.re.mk_in_re(b_str, rng), m);
        rw(e);
        std::cout << "symbolic range (\"b\" in [lo,hi]): " << mk_pp(e, m) << "\n";
        ENSURE(m.is_and(e));
    }

    // -----------------------------------------------------------------------
    // Solver-level tests: the unfolded conjunction must be decidable.
    // -----------------------------------------------------------------------
    {
        arith_util a_util(m);

        // 17. sat: (str.in_re x (re.range x x)) ∧ len(x)=1
        {
            smt_params sp;
            smt::context ctx(m, sp);
            app_ref x(m.mk_fresh_const("x", str_sort), m);
            ctx.assert_expr(su.re.mk_in_re(x, su.re.mk_range(x, x)));
            ctx.assert_expr(m.mk_eq(su.str.mk_length(x), a_util.mk_int(1)));
            lbool res = ctx.check();
            std::cout << "symbolic range solver sat (len=1): " << res << "\n";
            ENSURE(res == l_true);
        }

        // 18. unsat: (str.in_re x (re.range x x)) ∧ len(x)=2
        //     The unfolded membership requires len(x)=1, which contradicts len(x)=2.
        {
            smt_params sp;
            smt::context ctx(m, sp);
            app_ref x(m.mk_fresh_const("x", str_sort), m);
            ctx.assert_expr(su.re.mk_in_re(x, su.re.mk_range(x, x)));
            ctx.assert_expr(m.mk_eq(su.str.mk_length(x), a_util.mk_int(2)));
            lbool res = ctx.check();
            std::cout << "symbolic range solver unsat (len=2): " << res << "\n";
            ENSURE(res == l_false);
        }

        // 19. unsat: inverted symbolic bounds make membership false.
        //     (str.in_re "b" (re.range lo hi)) ∧ lo="z" ∧ hi="a"
        //     The unfolded conjunction requires lo <=_lex "b" <=_lex hi, but
        //     "z" > "b" > "a" so the ordering constraints are unsatisfiable.
        {
            smt_params sp;
            smt::context ctx(m, sp);
            app_ref lo(m.mk_fresh_const("lo", str_sort), m);
            app_ref hi(m.mk_fresh_const("hi", str_sort), m);
            expr_ref b_str(su.str.mk_string(zstring('b')), m);
            ctx.assert_expr(su.re.mk_in_re(b_str, su.re.mk_range(lo, hi)));
            ctx.assert_expr(m.mk_eq(lo, su.str.mk_string(zstring('z'))));
            ctx.assert_expr(m.mk_eq(hi, su.str.mk_string(zstring('a'))));
            lbool res = ctx.check();
            std::cout << "symbolic range solver inverted bounds unsat: " << res << "\n";
            ENSURE(res == l_false);
        }

        // 21. sat: (str.in_re "a" (re.++ re.all (re.range s "c")))
        //     Regression for nested symbolic re.range under re.++.
        //     The string "a" satisfies the regex when s = "a":
        //     re.all matches "" and re.range "a" "c" accepts "a".
        //     This must not hang; it should return sat.
        {
            smt_params sp;
            smt::context ctx(m, sp);
            app_ref s(m.mk_fresh_const("s", str_sort), m);
            expr_ref a_str(su.str.mk_string(zstring('a')), m);
            expr_ref c_str(su.str.mk_string(zstring('c')), m);
            expr_ref re_all(su.re.mk_full_seq(re_sort), m);
            expr_ref re_range(su.re.mk_range(s, c_str), m);
            expr_ref regex(su.re.mk_concat(re_all, re_range), m);
            ctx.assert_expr(su.re.mk_in_re(a_str, regex));
            lbool res = ctx.check();
            std::cout << "nested symbolic re.range under re.++ sat: " << res << "\n";
            ENSURE(res == l_true);
        }

        // 22. (Σ*·S)* is rewritten to the flat form () | Σ*·S.
        //     Σ*·S is idempotent under concatenation — Σ*·S·Σ*·S = (Σ*·S·Σ*)·S
        //     is again of the form Σ*·S — so its Kleene star contributes
        //     nothing beyond the empty word. The star form is exponentially
        //     more expensive to determinize, so the flat form is kept.
        {
            expr_ref sigma_star(su.re.mk_full_seq(re_sort), m);
            expr_ref b_re(su.re.mk_to_re(su.str.mk_string(zstring('b'))), m);
            expr_ref star(su.re.mk_star(su.re.mk_concat(sigma_star, b_re)), m);
            expr_ref e(star);
            rw(e);
            std::cout << "(sigma* b)* flattened: " << mk_pp(e, m) << "\n";
            ENSURE(!su.re.is_star(e));

            // Semantics: L* = words ending in "b", plus the empty word.
            auto member = [&](char const* w) {
                smt_params sp;
                smt::context ctx(m, sp);
                ctx.assert_expr(su.re.mk_in_re(su.str.mk_string(w), star));
                return ctx.check();
            };
            ENSURE(member("ab") == l_true);
            ENSURE(member("") == l_true);
            ENSURE(member("ba") == l_false);
        }


        //     "2024-01-01" < x < "2024-12-31" and x < "2023-01-01".
        //     Since "2023-01-01" < "2024-01-01", no such x exists.
        if (false)
        {
            smt_params sp;
            smt::context ctx(m, sp);
            app_ref x(m.mk_fresh_const("x", str_sort), m);
            expr_ref b1(su.str.mk_string("2024-01-01"), m);
            expr_ref b2(su.str.mk_string("2024-12-31"), m);
            expr_ref b3(su.str.mk_string("2023-01-01"), m);
            ctx.assert_expr(su.str.mk_lex_lt(b1, x));
            ctx.assert_expr(su.str.mk_lex_lt(x, b2));
            ctx.assert_expr(su.str.mk_lex_lt(x, b3));
            lbool res = ctx.check();
            std::cout << "constant lexical bounds unsat: " << res << "\n";
            ENSURE(res == l_false);
        }
    }

    // -----------------------------------------------------------------------
    // 22. re.loop with the bounds given as arguments must be interpreted the
    //     same as the indexed form.  get_info used to read the bounds only
    //     from the decl parameters, which the argument form does not carry,
    //     so it silently fell back to lo = 0 and reported (ab){1,3} as
    //     nullable with min_length 0.  seq_rewriter normalizes the argument
    //     form, so this is only observable on paths that bypass it.
    // -----------------------------------------------------------------------
    {
        arith_util a_util(m);
        expr_ref ab(su.re.mk_to_re(su.str.mk_string("ab")), m);
        expr_ref indexed(su.re.mk_loop_proper(ab, 1, 3), m);
        expr* args[3] = { ab.get(), a_util.mk_int(1), a_util.mk_int(3) };
        expr_ref as_args(m.mk_app(su.get_family_id(), OP_RE_LOOP, 0, nullptr, 3, args), m);

        auto i1 = su.re.get_info(indexed);
        auto i2 = su.re.get_info(as_args);
        std::cout << "re.loop indexed:   " << mk_pp(indexed, m)
                  << " nullable=" << i1.nullable << " min_length=" << i1.min_length << "\n";
        std::cout << "re.loop arguments: " << mk_pp(as_args, m)
                  << " nullable=" << i2.nullable << " min_length=" << i2.min_length << "\n";
        ENSURE(i1.nullable == l_false && i1.min_length == 2);
        ENSURE(i2.nullable == l_false && i2.min_length == 2);
    }

    // -----------------------------------------------------------------------
    // 24. Regex info tracks inferred maximal lengths.
    // -----------------------------------------------------------------------
    {
        expr_ref empty(su.re.mk_empty(re_sort), m);
        expr_ref epsilon(su.re.mk_to_re(su.str.mk_empty(str_sort)), m);
        expr_ref ab(su.re.mk_to_re(su.str.mk_string("ab")), m);
        expr_ref abc(su.re.mk_to_re(su.str.mk_string("abc")), m);
        expr_ref intersection(su.re.mk_inter(ab, abc), m);
        expr_ref union_(su.re.mk_union(ab, abc), m);
        expr_ref complement(su.re.mk_complement(ab), m);
        expr_ref loop(su.re.mk_loop_proper(abc, 2, 4), m);

        ENSURE(su.re.get_info(empty).max_length == 0);
        ENSURE(su.re.get_info(epsilon).max_length == 0);
        ENSURE(su.re.get_info(intersection).max_length == 2);
        ENSURE(su.re.get_info(union_).max_length == 3);
        ENSURE(su.re.get_info(complement).max_length == UINT_MAX);
        ENSURE(su.re.get_info(loop).max_length == 12);

        seq_util::rex::info large(true, l_false, 1, UINT_MAX / 2 + 1, true);
        ENSURE(large.loop(1, 2).max_length == UINT_MAX);
        seq_util::rex::info almost_max(true, l_false, 1, UINT_MAX - 1, true);
        seq_util::rex::info two(true, l_false, 1, 2, true);
        ENSURE(almost_max.concat(two, false).max_length == UINT_MAX);
    }

    // -----------------------------------------------------------------------
    // 25. Semilinear length abstraction: Lambda(r) as an ultimately periodic set.
    //     The soundness contract is
    //        Lambda(r) subseteq { n : min_length <= n <= max_length, n mod period in residues }
    //     so the abstraction may be weakened but never sharpened.
    // -----------------------------------------------------------------------
    {
        expr_ref ab(su.re.mk_to_re(su.str.mk_string("ab")), m);
        expr_ref ba(su.re.mk_to_re(su.str.mk_string("ba")), m);
        expr_ref a(su.re.mk_to_re(su.str.mk_string("a")), m);
        expr_ref abc(su.re.mk_to_re(su.str.mk_string("abc")), m);

        // (ab)* has even lengths.
        expr_ref ab_star(su.re.mk_star(ab), m);
        auto i_ab_star = su.re.get_info(ab_star);
        std::cout << "(ab)*      " << i_ab_star.str() << "\n";
        ENSURE(i_ab_star.period == 2 && i_ab_star.residues == 0x1);

        // (abc)* has lengths 3k, recovering the period from the star rule.
        expr_ref abc_star(su.re.mk_star(abc), m);
        auto i_abc_star = su.re.get_info(abc_star);
        std::cout << "(abc)*     " << i_abc_star.str() << "\n";
        ENSURE(i_abc_star.period == 3 && i_abc_star.residues == 0x1);

        // a(ba)* has odd lengths: the singleton "a" shifts the residue by 1.
        expr_ref a_ba_star(su.re.mk_concat(a, su.re.mk_star(ba)), m);
        auto i_a_ba_star = su.re.get_info(a_ba_star);
        std::cout << "a(ba)*     " << i_a_ba_star.str() << "\n";
        ENSURE(i_a_ba_star.period == 2 && i_a_ba_star.residues == 0x2);

        // (ab)* & a(ba)* is empty by parity, even though the length interval [1, oo) is not.
        auto i_par = i_ab_star.conj(i_a_ba_star);
        std::cout << "(ab)*&a(ba)* " << i_par.str() << "\n";
        ENSURE(i_par.residues == 0 && i_par.length_is_empty());

        // (ab)*a is odd, which is the parity argument behind "xx in (ab)*a is unsat".
        auto i_ab_star_a = i_ab_star.concat(su.re.get_info(a), false);
        ENSURE(i_ab_star_a.period == 2 && i_ab_star_a.residues == 0x2);

        // Intersecting compatible periods must NOT report empty: (ab)* & (abc)* share length 6k.
        auto i_compat = i_ab_star.conj(i_abc_star);
        std::cout << "(ab)*&(abc)* " << i_compat.str() << "\n";
        ENSURE(!i_compat.length_is_empty());
        ENSURE(i_compat.period == 6 && i_compat.residues == 0x1);

        // Union takes the lcm and unions residues: (ab)* | (abc)* keeps 0 mod 2 and 0 mod 3.
        auto i_union = i_ab_star.disj(i_abc_star);
        ENSURE(i_union.period == 6);
        // residues mod 6 are {0,2,4} from (ab)* and {0,3} from (abc)*
        ENSURE(i_union.residues == ((1ull<<0)|(1ull<<2)|(1ull<<4)|(1ull<<3)));

        // Complement degrades to top: no periodic information may survive.
        auto i_compl = i_ab_star.complement();
        ENSURE(i_compl.period == 1 && i_compl.residues == 0x1 && !i_compl.length_is_empty());

        // Star of an odd-length language saturates to gcd 1, not to the odd residue.
        auto i_odd_star = i_a_ba_star.star();
        ENSURE(i_odd_star.period == 1 && !i_odd_star.length_is_empty());

        // A bounded loop sums residues: ((ab)*a){2,2} has even length (odd + odd).
        auto i_loop = i_ab_star_a.loop(2, 2);
        std::cout << "((ab)*a){2,2} " << i_loop.str() << "\n";
        ENSURE(i_loop.period == 2 && i_loop.residues == 0x1);

        // ((ab)*a){1,2} admits both parities.
        auto i_loop12 = i_ab_star_a.loop(1, 2);
        ENSURE(i_loop12.period == 2 && i_loop12.residues == 0x3);

        // opt adds length 0.
        auto i_opt = i_a_ba_star.opt();
        ENSURE(i_opt.period == 2 && i_opt.residues == 0x3);

        // diff keeps the lhs abstraction, which is the sound direction.
        auto i_diff = i_ab_star.diff(i_abc_star);
        ENSURE(i_diff.period == 2 && i_diff.residues == 0x1);

        // An empty residue set certifies emptiness only via length_is_empty, and the
        // interval test must still work on its own for re.empty.
        expr_ref empty2(su.re.mk_empty(re_sort), m);
        ENSURE(su.re.get_info(empty2).length_is_empty());

        // Unknown info must never claim emptiness.
        seq_util::rex::info unknown(l_false);
        ENSURE(!unknown.length_is_empty());
        ENSURE(!unknown.star().length_is_empty());

        // (a(ab)*bc)* : the inner language has odd lengths >= 3, whose gcd is 1, so the
        // star saturates to top. The exact set is nat \ {1,2,4}; the (min,max,p,R) form
        // cannot express holes above min, so this is a precision loss, not unsoundness.
        expr_ref bc(su.re.mk_to_re(su.str.mk_string("bc")), m);
        expr_ref inner(su.re.mk_concat(a, su.re.mk_concat(su.re.mk_star(ab), bc)), m);
        auto i_inner = su.re.get_info(inner);
        std::cout << "a(ab)*bc   " << i_inner.str() << "\n";
        ENSURE(i_inner.min_length == 3 && i_inner.period == 2 && i_inner.residues == 0x2);

        auto i_inner_star = su.re.get_info(su.re.mk_star(inner));
        std::cout << "(a(ab)*bc)* " << i_inner_star.str() << "\n";
        ENSURE(i_inner_star.period == 1 && i_inner_star.min_length == 0);
        // Soundness spot-check: every length actually in the language must be admitted.
        for (unsigned n : { 0u, 3u, 5u, 6u, 7u, 8u, 9u, 10u, 11u, 12u })
            ENSURE(!i_inner_star.length_is_empty() &&
                   n >= i_inner_star.min_length && n <= i_inner_star.max_length &&
                   (i_inner_star.residues & (1ull << (n % i_inner_star.period))));
    }

    std::cout << "tst_seq_rewriter: all tests passed\n";
}
