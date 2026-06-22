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
--*/

#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq_decl_plugin.h"
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
    // 9. Range complement (general): no longer a complement node
    // -----------------------------------------------------------------------
    {
        expr_ref e(su.re.mk_complement(range('b', 'y')), m);
        rw(e);
        std::cout << "range comp general: " << mk_pp(e, m) << "\n";
        ENSURE(!su.re.is_complement(e));
    }

    // -----------------------------------------------------------------------
    // 10. Range complement (lo = 0): single range e union [hi+1, max].*
    // -----------------------------------------------------------------------
    {
        expr_ref lo_str(su.str.mk_string(zstring(0u)), m);
        expr_ref hi_str(su.str.mk_string(zstring((unsigned)'f')), m);
        expr_ref e(su.re.mk_complement(su.re.mk_range(lo_str, hi_str)), m);
        rw(e);
        std::cout << "range comp lo=min: " << mk_pp(e, m) << "\n";
        ENSURE(!su.re.is_complement(e));
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

    std::cout << "tst_seq_rewriter: all tests passed\n";
}
