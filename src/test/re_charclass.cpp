/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    test/re_charclass.cpp

Abstract:

    Unit tests for the OP_RE_CHARCLASS AST node:
      * mk_charclass + is_charclass round-trip,
      * hash-cons identity (same predicate -> same app*),
      * canonical collapses (empty -> re.none, top -> re.allchar),
      * as_charclass for re.to_re of a single-char string / unit,
        re.range with concrete bounds, re.full_char, re.empty,
      * smart-constructor short-circuit for union / intersection / diff
        through seq_rewriter::mk_app_core,
      * parametric mk_func_decl validation (odd params, lo>hi, sort
        order, disjointness, non-adjacency),
      * SMT-LIB pretty-printer round-trip via the parametric
        `(_ re.charclass lo0 hi0 ...)` form.

Author:

    Margus Veanes (veanes) 2026

--*/

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/range_predicate.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/debug.h"
#include "util/z3_exception.h"
#include <iostream>
#include <sstream>

using seq::range_predicate;

namespace {

    static unsigned max_char(seq_util const& u) { return u.max_char(); }

    static range_predicate rp_range(unsigned lo, unsigned hi, unsigned mx) {
        return range_predicate::range(lo, hi, mx);
    }

    // Disjoint union of intervals; arguments must already be canonical.
    static range_predicate rp_intervals(std::initializer_list<std::pair<unsigned,unsigned>> ranges,
                                        unsigned mx) {
        range_predicate r = range_predicate::empty(mx);
        for (auto const& kv : ranges)
            r = r | range_predicate::range(kv.first, kv.second, mx);
        return r;
    }

    void test_round_trip() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);

        // multi-range charclass: [0-9] U [A-Z] U [a-z]
        range_predicate p = rp_intervals({{'0','9'},{'A','Z'},{'a','z'}}, mx);
        app_ref cc(u.re.mk_charclass(p, str_sort), m);

        ENSURE(u.re.is_charclass(cc));
        range_predicate q;
        ENSURE(u.re.is_charclass(cc, q));
        ENSURE(p == q);

        // single-range
        range_predicate p1 = rp_range('a','z', mx);
        app_ref cc1(u.re.mk_charclass(p1, str_sort), m);
        ENSURE(u.re.is_charclass(cc1));
        range_predicate q1;
        ENSURE(u.re.is_charclass(cc1, q1));
        ENSURE(p1 == q1);
    }

    void test_hash_cons_identity() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);

        range_predicate p = rp_intervals({{'a','f'},{'0','9'}}, mx);

        app_ref cc_a(u.re.mk_charclass(p, str_sort), m);
        app_ref cc_b(u.re.mk_charclass(p, str_sort), m);
        ENSURE(cc_a.get() == cc_b.get());
        ENSURE(cc_a->get_id() == cc_b->get_id());

        // A different predicate must hash-cons to a different node.
        range_predicate p2 = rp_intervals({{'a','f'},{'0','8'}}, mx);
        app_ref cc_c(u.re.mk_charclass(p2, str_sort), m);
        ENSURE(cc_a.get() != cc_c.get());
    }

    void test_empty_and_top_collapse() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);

        // empty -> re.none
        expr_ref empty_cc(u.re.mk_charclass(range_predicate::empty(mx), str_sort), m);
        ENSURE(u.re.is_empty(empty_cc));
        ENSURE(!u.re.is_charclass(empty_cc));

        // top -> re.allchar (re.full_char)
        expr_ref full_cc(u.re.mk_charclass(range_predicate::top(mx), str_sort), m);
        ENSURE(u.re.is_full_char(full_cc));
        ENSURE(!u.re.is_charclass(full_cc));
    }

    void test_as_charclass_positive() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);
        range_predicate p;

        // CHARCLASS itself
        app_ref cc(u.re.mk_charclass(rp_range('a','z',mx), str_sort), m);
        p = range_predicate::empty(mx);
        ENSURE(u.re.as_charclass(cc, p));
        ENSURE(p == rp_range('a','z',mx));

        // (re.range "a" "z")
        zstring sa("a"), sz("z");
        expr_ref a(u.str.mk_string(sa), m);
        expr_ref z(u.str.mk_string(sz), m);
        expr_ref range_az(u.re.mk_range(a, z), m);
        p = range_predicate::empty(mx);
        ENSURE(u.re.as_charclass(range_az, p));
        ENSURE(p == rp_range('a','z',mx));

        // (re.to_re "X") with a single-char string
        zstring sx("X");
        expr_ref to_re_x(u.re.mk_to_re(u.str.mk_string(sx)), m);
        p = range_predicate::empty(mx);
        ENSURE(u.re.as_charclass(to_re_x, p));
        ENSURE(p == rp_range('X','X',mx));

        // re.full_char
        expr_ref full(u.re.mk_full_char(u.re.mk_re(str_sort)), m);
        p = range_predicate::empty(mx);
        ENSURE(u.re.as_charclass(full, p));
        ENSURE(p == range_predicate::top(mx));

        // re.empty over (RegEx (Seq Char))
        expr_ref none(u.re.mk_empty(u.re.mk_re(str_sort)), m);
        p = range_predicate::top(mx);
        ENSURE(u.re.as_charclass(none, p));
        ENSURE(p.is_empty());
    }

    void test_as_charclass_negative() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* str_sort = u.str.mk_string_sort();
        range_predicate p;

        // (re.to_re "abc") is concat, not a single-char regex.
        zstring sabc("abc");
        expr_ref to_re_abc(u.re.mk_to_re(u.str.mk_string(sabc)), m);
        ENSURE(!u.re.as_charclass(to_re_abc, p));

        // (re.to_re "") is epsilon, not a charclass.
        zstring se("");
        expr_ref to_re_empty(u.re.mk_to_re(u.str.mk_string(se)), m);
        ENSURE(!u.re.as_charclass(to_re_empty, p));

        // (re.++ (re.range a z) (re.range a z)) - not a single charclass.
        zstring sa("a"), sz("z");
        expr_ref ar(u.re.mk_range(u.str.mk_string(sa), u.str.mk_string(sz)), m);
        expr_ref concat(u.re.mk_concat(ar, ar), m);
        ENSURE(!u.re.as_charclass(concat, p));
    }

    // Call seq_rewriter::mk_app_core via the func_decl built by re().mk_<op>.
    static expr_ref rewrite_binary(seq_rewriter& rw, app* template_app, expr* a, expr* b) {
        ast_manager& m = rw.m();
        expr_ref result(m);
        expr* args[] = {a, b};
        if (BR_FAILED == rw.mk_app_core(template_app->get_decl(), 2, args, result))
            result = m.mk_app(template_app->get_decl(), 2, args);
        return result;
    }

    void test_smart_ctor_union() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        seq_rewriter rw(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);

        // CHARCLASS | CHARCLASS -> merged CHARCLASS
        app_ref cc1(u.re.mk_charclass(rp_range('a','z',mx), str_sort), m);
        app_ref cc2(u.re.mk_charclass(rp_range('0','9',mx), str_sort), m);
        app_ref tmpl(u.re.mk_union(cc1, cc2), m);

        expr_ref out = rewrite_binary(rw, tmpl, cc1, cc2);
        range_predicate p;
        ENSURE(u.re.is_charclass(out, p));
        ENSURE(p == rp_intervals({{'0','9'},{'a','z'}}, mx));

        // CHARCLASS | range(concrete) -> CHARCLASS (uses as_charclass)
        zstring sA("A"), sZ("Z");
        expr_ref range_AZ(u.re.mk_range(u.str.mk_string(sA), u.str.mk_string(sZ)), m);
        app_ref tmpl2(u.re.mk_union(cc1, to_app(range_AZ)), m);
        expr_ref out2 = rewrite_binary(rw, tmpl2, cc1, range_AZ);
        ENSURE(u.re.is_charclass(out2, p));
        ENSURE(p == rp_intervals({{'A','Z'},{'a','z'}}, mx));

        // CHARCLASS | full_char -> full_char (after merge, top collapses)
        expr_ref full(u.re.mk_full_char(u.re.mk_re(str_sort)), m);
        app_ref tmpl3(u.re.mk_union(cc1, to_app(full)), m);
        expr_ref out3 = rewrite_binary(rw, tmpl3, cc1, full);
        ENSURE(u.re.is_full_char(out3));
    }

    void test_smart_ctor_inter() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        seq_rewriter rw(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);

        // [a-z] & [m-q] -> [m-q]
        app_ref cc1(u.re.mk_charclass(rp_range('a','z',mx), str_sort), m);
        app_ref cc2(u.re.mk_charclass(rp_range('m','q',mx), str_sort), m);
        app_ref tmpl(u.re.mk_inter(cc1, cc2), m);
        expr_ref out = rewrite_binary(rw, tmpl, cc1, cc2);
        range_predicate p;
        ENSURE(u.re.is_charclass(out, p));
        ENSURE(p == rp_range('m','q',mx));

        // [a-c] & [x-z] -> empty -> re.none
        app_ref cc3(u.re.mk_charclass(rp_range('a','c',mx), str_sort), m);
        app_ref cc4(u.re.mk_charclass(rp_range('x','z',mx), str_sort), m);
        app_ref tmpl2(u.re.mk_inter(cc3, cc4), m);
        expr_ref out2 = rewrite_binary(rw, tmpl2, cc3, cc4);
        ENSURE(u.re.is_empty(out2));
    }

    void test_smart_ctor_diff() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        seq_rewriter rw(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);

        // [a-z] - [m-q] -> [a-l] U [r-z]
        app_ref cc1(u.re.mk_charclass(rp_range('a','z',mx), str_sort), m);
        app_ref cc2(u.re.mk_charclass(rp_range('m','q',mx), str_sort), m);
        app_ref tmpl(u.re.mk_diff(cc1, cc2), m);
        expr_ref out = rewrite_binary(rw, tmpl, cc1, cc2);
        range_predicate p;
        ENSURE(u.re.is_charclass(out, p));
        ENSURE(p == rp_intervals({{'a','l'},{'r','z'}}, mx));
    }

    // Try to build OP_RE_CHARCLASS with bad parameters; the parametric
    // mk_func_decl should raise an exception.
    static bool mk_charclass_raises(ast_manager& m, seq_util& u,
                                    std::initializer_list<int> raw_params) {
        vector<parameter> params;
        for (int v : raw_params) params.push_back(parameter(v));
        sort* str_sort = u.str.mk_string_sort();
        sort* re_sort  = u.re.mk_re(str_sort);
        try {
            (void)m.mk_func_decl(u.get_family_id(), OP_RE_CHARCLASS,
                                 params.size(), params.data(),
                                 0u, (sort* const*)nullptr, re_sort);
        }
        catch (z3_exception &) { return true; }
        return false;
    }

    void test_validation() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);

        // odd number of parameters
        ENSURE(mk_charclass_raises(m, u, {5}));
        // lo > hi
        ENSURE(mk_charclass_raises(m, u, {10, 5}));
        // unsorted (97-122 then 48-57)
        ENSURE(mk_charclass_raises(m, u, {97, 122, 48, 57}));
        // overlapping
        ENSURE(mk_charclass_raises(m, u, {50, 100, 80, 120}));
        // adjacent: [48,57] and [58,65] should be merged
        ENSURE(mk_charclass_raises(m, u, {48, 57, 58, 65}));

        // Sane invocation must succeed.
        ENSURE(!mk_charclass_raises(m, u, {}));
        ENSURE(!mk_charclass_raises(m, u, {65, 90}));
        ENSURE(!mk_charclass_raises(m, u, {48, 57, 65, 90, 97, 122}));
    }

    // The SMT-LIB pretty-printer must emit the canonical
    // `(_ re.charclass lo0 hi0 ...)` form for any CHARCLASS node.
    void test_pp_round_trip() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* str_sort = u.str.mk_string_sort();
        unsigned mx = max_char(u);

        range_predicate p = rp_intervals({{'0','9'},{'A','Z'},{'a','z'}}, mx);
        expr_ref cc(u.re.mk_charclass(p, str_sort), m);

        std::ostringstream oss;
        oss << mk_pp(cc, m);
        std::string s = oss.str();
        // Expect: "(_ re.charclass 48 57 65 90 97 122)"
        ENSURE(s.find("re.charclass") != std::string::npos);
        ENSURE(s.find("48 57") != std::string::npos);
        ENSURE(s.find("65 90") != std::string::npos);
        ENSURE(s.find("97 122") != std::string::npos);
    }

}

void tst_re_charclass() {
    test_round_trip();
    test_hash_cons_identity();
    test_empty_and_top_collapse();
    test_as_charclass_positive();
    test_as_charclass_negative();
    test_smart_ctor_union();
    test_smart_ctor_inter();
    test_smart_ctor_diff();
    test_validation();
    test_pp_round_trip();
    std::cout << "re_charclass unit tests passed\n";
}
