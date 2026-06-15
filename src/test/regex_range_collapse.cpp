/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    regex_range_collapse.cpp - unit tests

--*/

#include "ast/rewriter/regex_range_collapse.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "util/util.h"

#include <iostream>

namespace {

    using seq::range_predicate;
    using seq::regex_to_range_predicate;
    using seq::range_predicate_to_regex;

    static void check(bool ok, char const* what) {
        if (!ok) {
            std::cerr << "regex_range_collapse FAILED: " << what << "\n";
            ENSURE(false);
        }
    }

    static expr_ref mk_singleton_str(seq_util& u, unsigned c) {
        return expr_ref(u.str.mk_string(zstring(c)), u.get_manager());
    }

    static bool extract_range_chars(seq_util& u, expr* e, unsigned& lo, unsigned& hi) {
        expr* lo_e = nullptr; expr* hi_e = nullptr;
        if (!u.re.is_range(e, lo_e, hi_e))
            return false;
        // Accept either string-constant or (seq.unit (Char N)) bound form.
        if (u.re.is_range(e, lo, hi))
            return true;
        expr* lc = nullptr; expr* hc = nullptr;
        if (u.str.is_unit(lo_e, lc) && u.is_const_char(lc, lo) &&
            u.str.is_unit(hi_e, hc) && u.is_const_char(hc, hi))
            return true;
        return false;
    }

    static void run() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        unsigned const M = u.max_char();

        sort* str_sort = u.str.mk_string_sort();
        sort* re_sort  = u.re.mk_re(str_sort);

        // primitives
        {
            range_predicate p(M);
            check(regex_to_range_predicate(u, u.re.mk_empty(re_sort), p) && p.is_empty(),
                  "re.empty -> empty");
            check(regex_to_range_predicate(u, u.re.mk_full_char(re_sort), p) && p.is_top(),
                  "re.full_char -> top");
        }
        // re.range "a" "z"
        {
            range_predicate p(M);
            expr_ref a = mk_singleton_str(u, 'a');
            expr_ref z = mk_singleton_str(u, 'z');
            expr_ref r(u.re.mk_range(a, z), m);
            check(regex_to_range_predicate(u, r, p) && p.num_ranges() == 1 &&
                  p[0].first == 'a' && p[0].second == 'z',
                  "re.range a z -> [a,z]");
        }
        // Disjoint union: (a..z) | (0..9)
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'z')), m);
            expr_ref r2(u.re.mk_range(mk_singleton_str(u, '0'), mk_singleton_str(u, '9')), m);
            expr_ref un(u.re.mk_union(r1, r2), m);
            check(regex_to_range_predicate(u, un, p) && p.num_ranges() == 2,
                  "(a-z)|(0-9) -> 2 ranges");
            // canonical order: lower lo first
            check(p[0].first == '0' && p[0].second == '9' && p[1].first == 'a' && p[1].second == 'z',
                  "(a-z)|(0-9) ranges in canonical order");
        }
        // Overlapping union: (a..c) | (b..f) -> (a..f)
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'c')), m);
            expr_ref r2(u.re.mk_range(mk_singleton_str(u, 'b'), mk_singleton_str(u, 'f')), m);
            expr_ref un(u.re.mk_union(r1, r2), m);
            check(regex_to_range_predicate(u, un, p) && p.num_ranges() == 1 &&
                  p[0].first == 'a' && p[0].second == 'f',
                  "(a-c)|(b-f) -> (a-f)");
        }
        // Adjacent union: (a..c) | (d..f) -> (a..f) (canonical predicate merges adjacent)
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'c')), m);
            expr_ref r2(u.re.mk_range(mk_singleton_str(u, 'd'), mk_singleton_str(u, 'f')), m);
            expr_ref un(u.re.mk_union(r1, r2), m);
            check(regex_to_range_predicate(u, un, p) && p.num_ranges() == 1 &&
                  p[0].first == 'a' && p[0].second == 'f',
                  "(a-c)|(d-f) -> (a-f) via adjacency");
        }
        // Disjoint intersection: (a..z) & (0..9) -> empty
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'z')), m);
            expr_ref r2(u.re.mk_range(mk_singleton_str(u, '0'), mk_singleton_str(u, '9')), m);
            expr_ref ix(u.re.mk_inter(r1, r2), m);
            check(regex_to_range_predicate(u, ix, p) && p.is_empty(),
                  "(a-z)&(0-9) -> empty");
        }
        // Overlapping intersection: (a..f) & (c..z) -> (c..f)
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'f')), m);
            expr_ref r2(u.re.mk_range(mk_singleton_str(u, 'c'), mk_singleton_str(u, 'z')), m);
            expr_ref ix(u.re.mk_inter(r1, r2), m);
            check(regex_to_range_predicate(u, ix, p) && p.num_ranges() == 1 &&
                  p[0].first == 'c' && p[0].second == 'f',
                  "(a-f)&(c-z) -> (c-f)");
        }
        // Complement: re.complement is intentionally NOT a char-class op
        // (it operates over Σ*), so it must NOT be translated.
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'z')), m);
            expr_ref cmp(u.re.mk_complement(r1), m);
            check(!regex_to_range_predicate(u, cmp, p),
                  "re.comp of range is NOT translatable (sequence-level complement)");
        }
        // Diff: (a..f) \ (c..z) -> (a..b)
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'f')), m);
            expr_ref r2(u.re.mk_range(mk_singleton_str(u, 'c'), mk_singleton_str(u, 'z')), m);
            expr_ref df(u.re.mk_diff(r1, r2), m);
            check(regex_to_range_predicate(u, df, p) && p.num_ranges() == 1 &&
                  p[0].first == 'a' && p[0].second == 'b',
                  "(a-f) \\ (c-z) -> (a-b)");
        }
        // Negative: re.* of a range is NOT a char class
        {
            range_predicate p(M);
            expr_ref r1(u.re.mk_range(mk_singleton_str(u, 'a'), mk_singleton_str(u, 'z')), m);
            expr_ref star(u.re.mk_star(r1), m);
            check(!regex_to_range_predicate(u, star, p),
                  "re.* of range not translatable");
        }

        // ---- materialization round-trip ----

        // empty -> re.empty
        {
            range_predicate p = range_predicate::empty(M);
            expr_ref e = range_predicate_to_regex(u, p, str_sort);
            check(u.re.is_empty(e), "empty -> re.empty");
        }
        // top -> re.full_char
        {
            range_predicate p = range_predicate::top(M);
            expr_ref e = range_predicate_to_regex(u, p, str_sort);
            check(u.re.is_full_char(e), "top -> re.full_char");
        }
        // single range -> re.range
        {
            range_predicate p = range_predicate::range('a', 'z', M);
            expr_ref e = range_predicate_to_regex(u, p, str_sort);
            unsigned lo = 0, hi = 0;
            check(extract_range_chars(u, e, lo, hi) && lo == 'a' && hi == 'z',
                  "[a-z] -> re.range a z");
        }
        // singleton -> re.range c c
        {
            range_predicate p = range_predicate::singleton('A', M);
            expr_ref e = range_predicate_to_regex(u, p, str_sort);
            unsigned lo = 0, hi = 0;
            check(extract_range_chars(u, e, lo, hi) && lo == 'A' && hi == 'A',
                  "{A} -> re.range A A");
        }
        // 2 ranges -> re.union(range_0, range_1) in canonical order
        {
            range_predicate p = range_predicate::range('0', '9', M)
                              | range_predicate::range('a', 'z', M);
            expr_ref e = range_predicate_to_regex(u, p, str_sort);
            expr* a = nullptr; expr* b = nullptr;
            check(u.re.is_union(e, a, b), "2-range -> union");
            unsigned lo0 = 0, hi0 = 0, lo1 = 0, hi1 = 0;
            check(extract_range_chars(u, a, lo0, hi0) && lo0 == '0' && hi0 == '9',
                  "union arg0 = (0-9) (canonical: lower lo first)");
            check(extract_range_chars(u, b, lo1, hi1) && lo1 == 'a' && hi1 == 'z',
                  "union arg1 = (a-z)");
        }
        // 3 ranges -> right-associated union
        {
            range_predicate p = range_predicate::range(0, 5, M)
                              | range_predicate::range(10, 15, M)
                              | range_predicate::range(20, 25, M);
            expr_ref e = range_predicate_to_regex(u, p, str_sort);
            expr* a = nullptr; expr* rest = nullptr;
            check(u.re.is_union(e, a, rest), "3-range -> union(...)");
            unsigned lo = 0, hi = 0;
            check(extract_range_chars(u, a, lo, hi) && lo == 0 && hi == 5, "first arg = (0-5)");
            expr* b = nullptr; expr* c = nullptr;
            check(u.re.is_union(rest, b, c), "rest is union(...,...)");
            check(extract_range_chars(u, b, lo, hi) && lo == 10 && hi == 15, "second range");
            check(extract_range_chars(u, c, lo, hi) && lo == 20 && hi == 25, "third range");
        }
        // Round-trip identity for an arbitrary range-set
        {
            range_predicate p_in = range_predicate::range('a', 'c', M)
                                 | range_predicate::range('m', 'p', M)
                                 | range_predicate::range('x', 'z', M);
            expr_ref e = range_predicate_to_regex(u, p_in, str_sort);
            range_predicate p_out(M);
            check(regex_to_range_predicate(u, e, p_out), "round-trip translatable");
            check(p_in == p_out, "round-trip equal");
        }

        std::cerr << "regex_range_collapse tests passed\n";
    }
}

void tst_regex_range_collapse() {
    run();
}
