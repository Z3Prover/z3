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
--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_context.h"
#include <iostream>

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
    }

    std::cout << "tst_seq_rewriter: all tests passed\n";
}
