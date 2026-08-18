/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_approx.cpp

Abstract:

    Unit tests for the regular over-approximation of word equations in
    ast/rewriter/seq_eq_approx.cpp.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_eq_approx.h"
#include "ast/rewriter/seq_regex_witness.h"
#include <iostream>
#include <sstream>

namespace {

struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class seq_eq_approx_test {
    ast_manager      m;
    plugin_registrar m_reg;
    seq_rewriter     m_rw;
    seq_eq_approx    m_eq;
    seq::regex_witness m_wit;
    seq_util         u;
    arith_util       m_arith;
    sort_ref         m_str;
    sort_ref         m_re;
    seq::transition_mode m_mode;
    unsigned         m_fail = 0;

    seq_util::rex& re() { return u.re; }

    // regexes
    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref cat(expr* a, expr* b) { return expr_ref(re().mk_concat(a, b), m); }
    expr_ref alt(expr* a, expr* b) { return expr_ref(re().mk_union(a, b), m); }
    expr_ref star(expr* a) { return expr_ref(re().mk_star(a), m); }
    expr_ref plus(expr* a) { return cat(a, star(a)); }
    expr_ref comp(expr* a) { return expr_ref(re().mk_complement(a), m); }
    expr_ref dot() { return expr_ref(re().mk_full_char(m_re), m); }
    expr_ref loop(expr* r, unsigned lo, unsigned hi) { return expr_ref(re().mk_loop(r, lo, hi), m); }

    // terms
    expr_ref var(char const* nm) { return expr_ref(m.mk_const(nm, m_str), m); }
    expr_ref sword(char const* s) { return expr_ref(u.str.mk_string(zstring(s)), m); }
    expr_ref sconcat(expr* a, expr* b) { return expr_ref(u.str.mk_concat(a, b), m); }
    expr_ref sconcat(expr* a, expr* b, expr* c) { return sconcat(a, sconcat(b, c)); }

    static char const* s(lbool l) {
        return l == l_true ? "consistent" : l == l_false ? "refuted" : "undef";
    }

    char const* mode_name() const {
        switch (m_mode) {
        case seq::transition_mode::brzozowski_tm: return "brz";
        case seq::transition_mode::light_antimirov_tm: return "light-ant";
        }
        UNREACHABLE();
        return "";
    }

    void report(char const* name, lbool got, lbool expected) {
        bool ok = got == expected;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << mode_name() << " " << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    void check(char const* name, expr* lhs, expr* rhs, lbool expected) {
        report(name, m_eq.check(lhs, rhs), expected);
    }

    // one equation checked with the given entries installed in h, which are dropped
    // again afterwards
    void check_with_regex(char const* name, expr* var, expr* r, expr* lhs, expr* rhs, lbool expected) {
        m_eq.set_regex(var, r);
        report(name, m_eq.check(lhs, rhs), expected);
        m_eq.unset_regex(var);
    }

    void check_with_regexes(char const* name, expr* v1, expr* r1, expr* v2, expr* r2,
                            expr* lhs, expr* rhs, lbool expected) {
        m_eq.set_regex(v1, r1);
        m_eq.set_regex(v2, r2);
        report(name, m_eq.check(lhs, rhs), expected);
        m_eq.reset_regexes();
    }

    // Membership of `w` in the image of `term`, decided by intersecting the image with
    // the singleton language of `w`.  This pins down the image itself, which the
    // equation checks only see through the verdict.
    void check_member(char const* name, expr* term, char const* w, lbool expected) {
        expr_ref img(m);
        if (!m_eq.abstract(term, img)) {
            ++m_fail;
            std::cout << "  FAIL " << mode_name() << " " << name << "  abstract failed\n";
            return;
        }
        report(name, m_wit.intersect_nonempty(img, word(w)), expected);
    }

    // terms that are neither a variable nor a constant: an application and a unit of a
    // non-value element, which are Sigma^* and Sigma respectively
    void check_opaque_terms() {
        sort* dom[1] = { m_str };
        func_decl_ref f(m.mk_func_decl(symbol("f"), 1, dom, m_str), m);
        expr_ref x = var("x");
        expr_ref fx(m.mk_app(f, x.get()), m);
        check("f(x) = abc", fx, sword("abc"), l_true);
        check("a.f(x) = b", sconcat(sword("a"), fx), sword("b"), l_false);
        check_member("f(x) accepts abc", fx, "abc", l_true);

        expr_ref i(m.mk_const("i", m_arith.mk_int()), m);
        expr_ref unit_i(u.str.mk_unit(i), m);
        expr_ref one(u.str.mk_unit(m_arith.mk_int(1)), m);
        check("[int] unit(i) = 1", unit_i, one, l_true);
        check("[int] unit(i).unit(i) = 1", sconcat(unit_i, unit_i), one, l_false);
    }

    // inputs the module cannot lift to a pair of regexes
    void check_unsupported() {
        expr_ref x = var("x");
        sort_ref si(u.str.mk_seq(m_arith.mk_int()), m);
        expr_ref other(re().mk_full_seq(re().mk_re(si)), m);
        m_eq.set_regex(x, other);                      // h at the wrong sequence sort
        report("h at the wrong sort", m_eq.check(x, sword("abc")), l_undef);
        m_eq.reset_regexes();

        expr_ref one(m_arith.mk_int(1), m), two(m_arith.mk_int(2), m);
        report("1 = 2 over Int", m_eq.check(one, two), l_undef);
        report("String = Seq Int", m_eq.check(x, m.mk_const("xi", si)), l_undef);

        report("check(x = abc)", m_eq.check(m.mk_eq(x, sword("abc"))), l_true);
        report("check(x.a = x.b)", m_eq.check(m.mk_eq(sconcat(x, sword("a")),
                                                      sconcat(x, sword("b")))), l_false);
        report("check(true)", m_eq.check(m.mk_true()), l_undef);
    }

    // the mapping is a plain map: overwriting, removing, clearing
    void check_mapping() {
        expr_ref x = var("x"), y = var("y");
        expr_ref aStar(star(word("a")), m), bStar(star(word("b")), m);
        m_eq.set_regex(x, aStar);
        m_eq.set_regex(x, bStar);                      // overwrites
        bool ok = m_eq.get_regex(x) == bStar.get() && m_eq.num_regexes() == 1 &&
                  m_eq.get_regex(y) == nullptr;
        report("h overwrite", ok ? l_true : l_false, l_true);
        report("x in b*: x = a", m_eq.check(x, sword("a")), l_false);
        m_eq.unset_regex(x);
        report("h unset", m_eq.num_regexes() == 0 ? l_true : l_false, l_true);
        report("x unmapped: x = a", m_eq.check(x, sword("a")), l_true);
        m_eq.set_regex(x, aStar);
        m_eq.reset_regexes();
        report("h reset", m_eq.num_regexes() == 0 ? l_true : l_false, l_true);
    }

    // the state bound is reported as a give-up, never as a refutation
    void check_state_bound() {
        unsigned const saved = m_eq.max_states();
        m_eq.set_max_states(1);
        report("abc = abd, max_states=1", m_eq.check(sword("abc"), sword("abd")), l_undef);
        m_eq.set_max_states(saved);
        report("abc = abd, bound restored", m_eq.check(sword("abc"), sword("abd")), l_false);
    }

    // elements that are not characters: the guards go through the candidate basis
    // instead of the range algebra
    void check_int_seq() {
        sort_ref si(u.str.mk_seq(m_arith.mk_int()), m);
        expr_ref x(m.mk_const("xi", si), m), y(m.mk_const("yi", si), m);
        expr_ref one(u.str.mk_unit(m_arith.mk_int(1)), m);
        expr_ref two(u.str.mk_unit(m_arith.mk_int(2)), m);

        report("[int] 1 = 2", m_eq.check(one, two), l_false);
        report("[int] 1.x = 2.y", m_eq.check(sconcat(one, x), sconcat(two, y)), l_false);
        report("[int] 1.x = y.2", m_eq.check(sconcat(one, x), sconcat(y, two)), l_true);
        report("[int] x.1 = y.2", m_eq.check(sconcat(x, one), sconcat(y, two)), l_false);
    }

public:

    seq_eq_approx_test(seq::transition_mode mode) :
        m_reg(m), m_rw(m), m_eq(m_rw, mode), m_wit(m_rw, mode), u(m), m_arith(m),
        m_str(u.str.mk_string_sort(), m), m_re(re().mk_re(m_str), m), m_mode(mode) {}

    void run() {
        expr_ref x = var("x"), y = var("y"), z = var("z");
        expr_ref a = word("a"), b = word("b"), ab = word("ab");

        std::cout << "=== seq_eq_approx: constants and free variables ===\n";
        check("abc = abc", sword("abc"), sword("abc"), l_true);
        check("abc = abd", sword("abc"), sword("abd"), l_false);
        check("abc = ab", sword("abc"), sword("ab"), l_false);
        check("x = abc", x, sword("abc"), l_true);
        check("a.x = b.y", sconcat(sword("a"), x), sconcat(sword("b"), y), l_false);
        check("x.a = y.b", sconcat(x, sword("a")), sconcat(y, sword("b")), l_false);
        check("x.a = y.a", sconcat(x, sword("a")), sconcat(y, sword("a")), l_true);
        check("a.x.b = a.y.b", sconcat(sword("a"), x, sword("b")),
              sconcat(sword("a"), y, sword("b")), l_true);
        check("a.x.b = a.y.c", sconcat(sword("a"), x, sword("b")),
              sconcat(sword("a"), y, sword("c")), l_false);
        // occurrences are abstracted apart, so a repeated variable carries no information
        check("x.x = a", sconcat(x, x), sword("a"), l_true);

        std::cout << "=== seq_eq_approx: over-approximating the variables ===\n";
        check_with_regex("x in a*: x = b", x, star(a), x, sword("b"), l_false);
        check_with_regex("x in a*: x = aaa", x, star(a), x, sword("aaa"), l_true);
        check_with_regex("x in (ab)*: x = abab", x, star(ab), x, sword("abab"), l_true);
        check_with_regex("x in (ab)*: x = aba", x, star(ab), x, sword("aba"), l_false);
        // two occurrences of Sigma^2 make the left side even
        check_with_regex("x in Sigma^2: x.x = abc", x, loop(dot(), 2, 2), sconcat(x, x),
                sword("abc"), l_false);
        check_with_regex("x in Sigma^2: x.x = abcd", x, loop(dot(), 2, 2), sconcat(x, x),
                sword("abcd"), l_true);
        check_with_regexes("x in a*, y in b*: x = y", x, star(a), y, star(b), x, y, l_true);
        check_with_regexes("x in a+, y in b*: x = y", x, plus(a), y, star(b), x, y, l_false);
        check_with_regexes("x in a+, y in b+: x.y = y.x", x, plus(a), y, plus(b),
                 sconcat(x, y), sconcat(y, x), l_false);
        check_with_regexes("x in a*, y in b*: x.y = y.x", x, star(a), y, star(b),
                 sconcat(x, y), sconcat(y, x), l_true);
        check_with_regexes("x in a*, y in a*: x.b.y = x.a.y", x, star(a), y, star(a),
                 sconcat(x, sword("b"), y), sconcat(x, sword("a"), y), l_false);
        // the same equation with an unmapped variable: Sigma^* absorbs the difference
        check_with_regex("x in a*: x.b.z = x.a.z", x, star(a),
                sconcat(x, sword("b"), z), sconcat(x, sword("a"), z), l_true);
        check_with_regex("x in ~(a*): x = aa", x, comp(star(a)), x, sword("aa"), l_false);
        check_with_regex("x in ~(a*): x = ab", x, comp(star(a)), x, sword("ab"), l_true);
        // h may describe a compound term, which is then not decomposed
        check_with_regex("x.y in a*: x.y = b", sconcat(x, y).get(), star(a),
                sconcat(x, y), sword("b"), l_false);

        std::cout << "=== seq_eq_approx: intersection emptiness ===\n";
        report("(a|b)* & ~(a*)", m_wit.intersect_nonempty(star(alt(a, b)), comp(star(a))), l_true);
        report("a* & ~(a*)", m_wit.intersect_nonempty(star(a), comp(star(a))), l_false);
        report("(aa)* & a(aa)*",
               m_wit.intersect_nonempty(star(cat(a, a)), cat(a, star(cat(a, a)))), l_false);

        std::cout << "=== seq_eq_approx: images ===\n";
        // the fold keeps the parts in order and drops nothing
        check_member("a.x.b accepts ab", sconcat(sword("a"), x, sword("b")), "ab", l_true);
        check_member("a.x.b accepts azzb", sconcat(sword("a"), x, sword("b")), "azzb", l_true);
        check_member("a.x.b rejects ba", sconcat(sword("a"), x, sword("b")), "ba", l_false);
        check_member("a.x.b rejects a", sconcat(sword("a"), x, sword("b")), "a", l_false);
        check_member("x.y.z accepts abc", sconcat(x, sconcat(y, z)), "abc", l_true);
        check_member("empty accepts eps", u.str.mk_empty(m_str), "", l_true);
        check_member("empty rejects a", u.str.mk_empty(m_str), "a", l_false);
        check("eps = eps", u.str.mk_empty(m_str), sword(""), l_true);
        check("eps = a", u.str.mk_empty(m_str), sword("a"), l_false);
        check("x = eps", x, u.str.mk_empty(m_str), l_true);
        check("eps.x = x.eps", sconcat(u.str.mk_empty(m_str), x),
              sconcat(x, u.str.mk_empty(m_str)), l_true);

        std::cout << "=== seq_eq_approx: opaque terms ===\n";
        check_opaque_terms();

        std::cout << "=== seq_eq_approx: the mapping ===\n";
        check_mapping();

        std::cout << "=== seq_eq_approx: unsupported input ===\n";
        check_unsupported();

        std::cout << "=== seq_eq_approx: state bound ===\n";
        check_state_bound();

        std::cout << "=== seq_eq_approx: non-character elements ===\n";
        check_int_seq();

        std::ostringstream buffer;                  // display must survive both states
        m_eq.display(buffer);
        m_eq.check(sconcat(x, sword("a")), sconcat(y, sword("b")));
        m_eq.display(buffer);
        report("display", buffer.str().empty() ? l_false : l_true, l_true);

        std::cout << "=== seq_eq_approx: " << (m_fail == 0 ? "ALL PASS" : "FAILURES") << " ("
                  << m_fail << " fail) ===\n";
        ENSURE(m_fail == 0);
    }
};

}

void tst_seq_eq_approx() {
    seq_eq_approx_test brz(seq::transition_mode::brzozowski_tm);
    brz.run();
    seq_eq_approx_test light_ant(seq::transition_mode::light_antimirov_tm);
    light_ant.run();
}
