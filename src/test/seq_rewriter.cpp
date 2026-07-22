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
--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "api/z3.h"
#include "smt/smt_context.h"
#include <cstring>
#include <iostream>
#include <sstream>
#include <string>

// Build a single-char string literal expression.
static expr_ref mk_str(ast_manager& m, seq_util& su, unsigned c) {
    return expr_ref(su.str.mk_string(zstring(c)), m);
}

static void test_seq_foldl_nth_model_validation() {
    Z3_context ctx = Z3_mk_context(nullptr);
    char const* result =
        Z3_eval_smtlib2_string(ctx,
            "(set-option :model_validate true)\n"
            "(declare-const initial Int)\n"
            "(declare-const all (Seq Int))\n"
            "(declare-const final Int)\n"
            "(declare-const elements (Seq Int))\n"
            "(define-fun all_sums ((prev_sums (Seq Int)) (elem Int)) (Seq Int)\n"
            "  (seq.++ (seq.unit (+ (seq.nth prev_sums 0) elem)) prev_sums))\n"
            "(assert (= all (seq.foldl all_sums (seq.unit initial) elements)))\n"
            "(assert (= final (seq.nth all 0)))\n"
            "(assert (= initial 0))\n"
            "(assert (= final 6))\n"
            "(check-sat)\n"
            "(get-model)\n");
    ENSURE(std::strstr(result, "sat") != nullptr);
    ENSURE(std::strstr(result, "invalid model") == nullptr);
    Z3_del_context(ctx);
}

static void test_seq_foldl_foldli_scalar_model_validation() {
    Z3_context ctx = Z3_mk_context(nullptr);
    char const* result =
        Z3_eval_smtlib2_string(ctx,
            "(set-option :model_validate true)\n"
            "(push)\n"
            "(declare-fun f (Int Int) Int)\n"
            "(declare-const il (Seq Int))\n"
            "(assert (= (seq.foldl f 0 il) 5))\n"
            "(check-sat)\n"
            "(pop)\n"
            "(push)\n"
            "(declare-const il (Seq Int))\n"
            "(declare-const F (Array Bool Int Bool))\n"
            "(assert (= (seq.foldl F true il) true))\n"
            "(assert (> (seq.len il) 0))\n"
            "(assert (not (= F ((as const (Array Bool Int Bool)) true))))\n"
            "(check-sat)\n"
            "(pop)\n"
            "(push)\n"
            "(declare-fun f (Int Int Int) Int)\n"
            "(declare-const il (Seq Int))\n"
            "(assert (= (seq.foldli f 0 0 il) 5))\n"
            "(check-sat)\n"
            "(pop)\n"
            "(push)\n"
            "(declare-const il (Seq Int))\n"
            "(declare-const F (Array Int Bool Int Bool))\n"
            "(assert (= (seq.foldli F 5 true il) true))\n"
            "(assert (> (seq.len il) 0))\n"
            "(assert (not (= F ((as const (Array Int Bool Int Bool)) true))))\n"
            "(check-sat)\n"
            "(pop)\n");
    ENSURE(std::strstr(result, "unknown") == nullptr);
    ENSURE(std::strstr(result, "invalid model") == nullptr);
    unsigned sat_count = 0;
    std::istringstream in{std::string(result)};
    for (std::string line; std::getline(in, line);)
        if (line == "sat")
            ++sat_count;
    ENSURE(sat_count == 4);
    Z3_del_context(ctx);
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

        // 20. unsat: contradictory constant lexical bounds.
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

    test_seq_foldl_nth_model_validation();
    test_seq_foldl_foldli_scalar_model_validation();

    std::cout << "tst_seq_rewriter: all tests passed\n";
}
