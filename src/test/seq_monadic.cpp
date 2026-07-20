/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.cpp

Abstract:

    Unit tests for the continuation-regex split service in
    ast/rewriter/seq_monadic.{h,cpp}: seq::split_manager::intersect (element-sort
    agnostic intersection non-emptiness, decided by the derivative engine) and the
    seq::split midpoint iterator.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_monadic.h"
#include <iostream>
#include <climits>

namespace {

struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class seq_monadic_test {
    ast_manager        m;
    plugin_registrar   m_reg;
    seq_rewriter       m_rw;
    seq::split_manager m_sm;
    seq_util           u;
    sort_ref           m_str;   // String sort
    sort_ref           m_re;    // RegEx sort over m_str
    unsigned           m_fail = 0;

    seq_util::rex& re() { return u.re; }

    // regex builders
    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref cat(expr* a, expr* b) { return expr_ref(re().mk_concat(a, b), m); }
    expr_ref alt(expr* a, expr* b) { return expr_ref(re().mk_union(a, b), m); }
    expr_ref star(expr* a) { return expr_ref(re().mk_star(a), m); }
    expr_ref comp(expr* a) { return expr_ref(re().mk_complement(a), m); }
    expr_ref dotstar() { return expr_ref(re().mk_full_seq(m_re), m); }
    expr_ref none() { return expr_ref(re().mk_empty(m_re), m); }
    expr_ref rng(char lo, char hi) {
        char sl[2] = { lo, 0 }, sh[2] = { hi, 0 };
        return expr_ref(re().mk_range(u.str.mk_string(zstring(sl)), u.str.mk_string(zstring(sh))), m);
    }
    expr_ref loop(expr* r, unsigned lo, unsigned hi) { return expr_ref(re().mk_loop(r, lo, hi), m); }
    expr_ref plus(expr* a) { return cat(a, star(a)); }
    expr_ref inter2(expr* a, expr* b) { return expr_ref(re().mk_inter(a, b), m); }
    expr_ref eps() { return expr_ref(re().mk_epsilon(m_str), m); }

    static char const* s(lbool l) { return l == l_true ? "sat" : l == l_false ? "unsat" : "undef"; }

    // intersection non-emptiness of the given membership regexes, words of length in [lo,hi]
    lbool inter(std::initializer_list<expr*> rs, unsigned lo, unsigned hi) {
        vector<seq::cont_regex> crs;
        for (expr* r : rs) crs.push_back(m_sm.embed(r));
        expr_ref_vector wit(m);
        return m_sm.intersect(crs, lo, hi, wit);
    }

    // intersection non-emptiness of a single reach continuation regex <R, N>
    lbool reach(expr* R, expr* N, unsigned lo, unsigned hi) {
        vector<seq::cont_regex> crs;
        crs.push_back(seq::cont_regex(expr_ref(R, m), expr_ref(N, m)));
        expr_ref_vector wit(m);
        return m_sm.intersect(crs, lo, hi, wit);
    }

    void check(char const* name, lbool got, lbool expected) {
        bool ok = (got == expected);
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    // Enumerate the midpoints of sigma(r); report count and whether the shared
    // midpoint of each split pair agrees (left.second == right.first).
    unsigned split_count(expr* r, bool& failed, bool& consistent) {
        seq::split sp = m_sm.mk_split(r);
        seq::split_iterator it = sp.begin();
        failed = it.failed();
        consistent = true;
        unsigned count = 0;
        for (; it != sp.end(); ++it) {
            seq::split_pair pr = *it;
            if (pr.first.second.get() != pr.second.first.get())
                consistent = false;
            ++count;
        }
        return count;
    }

public:
    seq_monadic_test() : m_reg(m), m_rw(m), m_sm(m_rw), u(m), m_str(m), m_re(m) {
        m_str = u.str.mk_string_sort();
        m_re  = re().mk_re(m_str);
    }

    void run() {
        expr_ref a  = word("a");
        expr_ref b  = word("b");
        expr_ref ab = cat(a, b);
        expr_ref sig = dotstar();                                   // Sigma*
        expr_ref saas = cat(sig, cat(cat(a, a), sig));              // Sigma* a a Sigma*
        expr_ref sbbs = cat(sig, cat(cat(b, b), sig));              // Sigma* b b Sigma*
        expr_ref digitp = cat(rng('0', '9'), star(rng('0', '9')));  // [0-9]+

        std::cout << "=== split_manager::intersect (membership) ===\n";

        check("Sigma*                    ", inter({ sig }, 0, UINT_MAX), l_true);
        check("empty regex               ", inter({ none() }, 0, UINT_MAX), l_false);
        check("~Sigma*                   ", inter({ comp(sig) }, 0, UINT_MAX), l_false);
        // a* & b* = { epsilon }
        check("a* & b*  (any length)     ", inter({ star(a), star(b) }, 0, UINT_MAX), l_true);
        check("a* & b*  (>= 1 char)      ", inter({ star(a), star(b) }, 1, UINT_MAX), l_false);
        // Sigma*aaSigma* & Sigma*bbSigma*  has a common word (e.g. aabb)
        check("SaaS & SbbS               ", inter({ saas, sbbs }, 0, UINT_MAX), l_true);
        // (a|b)*  intersect ~(SaaS) intersect ~(SbbS) is non-empty (alternating words)
        check("(a|b)* & ~SaaS & ~SbbS    ",
              inter({ star(alt(a, b)), comp(saas), comp(sbbs) }, 0, UINT_MAX), l_true);
        // nested complement (L3-03) non-empty
        check("L3-03 nested complement   ",
              inter({ comp(cat(star(a), comp(cat(star(b), comp(star(ab)))))) }, 0, UINT_MAX), l_true);

        // concrete words
        check("abc & abc                 ", inter({ word("abc"), word("abc") }, 0, UINT_MAX), l_true);
        check("abc & abd                 ", inter({ word("abc"), word("abd") }, 0, UINT_MAX), l_false);
        check("abc & S*cS*               ", inter({ word("abc"), cat(sig, cat(word("c"), sig)) }, 0, UINT_MAX), l_true);
        check("abc & S*zS*               ", inter({ word("abc"), cat(sig, cat(word("z"), sig)) }, 0, UINT_MAX), l_false);
        // epsilon vs star / plus
        check("eps & a*                  ", inter({ eps(), star(a) }, 0, UINT_MAX), l_true);
        check("eps & a+                  ", inter({ eps(), plus(a) }, 0, UINT_MAX), l_false);
        check("a+ & a*                   ", inter({ plus(a), star(a) }, 0, UINT_MAX), l_true);
        // unions
        check("(a|b) & (b|c)             ", inter({ alt(a, b), alt(b, word("c")) }, 0, UINT_MAX), l_true);
        check("(a|b) & (c|d)             ", inter({ alt(a, b), alt(word("c"), word("d")) }, 0, UINT_MAX), l_false);
        // complement fundamentals
        check("~empty (= S*)             ", inter({ comp(none()) }, 0, UINT_MAX), l_true);
        check("~(a*)                     ", inter({ comp(star(a)) }, 0, UINT_MAX), l_true);
        check("(a|b)* & ~((a|b)*)        ", inter({ star(alt(a, b)), comp(star(alt(a, b))) }, 0, UINT_MAX), l_false);
        check("a* & ~(a*)                ", inter({ star(a), comp(star(a)) }, 0, UINT_MAX), l_false);
        check("~(a*) | a*  (= S*)        ", inter({ alt(comp(star(a)), star(a)) }, 0, UINT_MAX), l_true);
        // three-way intersections
        check("a* & (a|b)* & S*aS*       ", inter({ star(a), star(alt(a, b)), cat(sig, cat(a, sig)) }, 0, UINT_MAX), l_true);
        check("a* & b* & S*aS*           ", inter({ star(a), star(b), cat(sig, cat(a, sig)) }, 0, UINT_MAX), l_false);

        std::cout << "=== split_manager::intersect (length bounds) ===\n";
        check("[0-9]+  length 0..0       ", inter({ digitp }, 0, 0), l_false);
        check("[0-9]+  length 1..1       ", inter({ digitp }, 1, 1), l_true);
        check("a*      length 2..2       ", inter({ star(a) }, 2, 2), l_true);
        check("a* & b* length 3..3       ", inter({ star(a), star(b) }, 3, 3), l_false);
        check("[0-9]{2} & [0-9]+  len 2  ", inter({ loop(rng('0','9'), 2, 2), digitp }, 2, 2), l_true);
        check("[0-9]{2}           len 3  ", inter({ loop(rng('0','9'), 2, 2) }, 3, 3), l_false);
        check("(a|b)              len 1  ", inter({ alt(a, b) }, 1, 1), l_true);
        check("(a|b)              len 2  ", inter({ alt(a, b) }, 2, 2), l_false);
        check("abc                len 3  ", inter({ word("abc") }, 3, 3), l_true);
        check("abc                len 2  ", inter({ word("abc") }, 2, 2), l_false);
        check("a*                 len 0  ", inter({ star(a) }, 0, 0), l_true);
        // parity / counting via periodic stars
        check("(aa)*              len 2  ", inter({ star(cat(a, a)) }, 2, 2), l_true);
        check("(aa)*              len 3  ", inter({ star(cat(a, a)) }, 3, 3), l_false);
        check("(aa)*              len 4  ", inter({ star(cat(a, a)) }, 4, 4), l_true);
        check("(aa)* & (aaa)*     len 6  ", inter({ star(cat(a, a)), star(cat(a, cat(a, a))) }, 6, 6), l_true);
        check("(aa)* & (aaa)*     len 3  ", inter({ star(cat(a, a)), star(cat(a, cat(a, a))) }, 3, 3), l_false);
        // length must both admit an 'a' and stay empty-word: contradiction at len 0
        check("a* & S*aS*         len 0  ", inter({ star(a), cat(sig, cat(a, sig)) }, 0, 0), l_false);
        check("[0-9]{2,4}         len 3  ", inter({ loop(rng('0','9'), 2, 4) }, 3, 3), l_true);
        check("[0-9]{2,4}         len 5  ", inter({ loop(rng('0','9'), 2, 4) }, 5, 5), l_false);
        check("[0-9]{2,4}         len 1  ", inter({ loop(rng('0','9'), 2, 4) }, 1, 1), l_false);

        std::cout << "=== split_manager::intersect (reach, general N) ===\n";
        {
            expr_ref aSig = cat(a, sig);                               // a . Sigma*
            // <Sigma*, Sigma*>: delta_epsilon(Sigma*) == Sigma* already at depth 0
            check("<S*,S*>              len0 ", reach(sig, sig, 0, UINT_MAX), l_true);
            // <Sigma*, empty>: Sigma* never derives to the empty regex
            check("<S*,empty>                ", reach(sig, none(), 0, UINT_MAX), l_false);
            // <a.Sigma*, Sigma*>: reached exactly after consuming one element
            check("<a.S*,S*>            len1 ", reach(aSig, sig, 1, 1), l_true);
            check("<a.S*,S*>            len0 ", reach(aSig, sig, 0, 0), l_false);
            // <S*,S*> via a self-loop: still on target after one step
            check("<S*,S*>              len1 ", reach(sig, sig, 1, 1), l_true);
            // <a*,a*>: a* is its own 'a'-derivative (fixpoint state)
            check("<a*,a*>              len0 ", reach(star(a), star(a), 0, 0), l_true);
            check("<a*,a*>              len1 ", reach(star(a), star(a), 1, 1), l_true);
            // <empty,empty>: the empty word already sits on the target
            check("<empty,empty>        len0 ", reach(none(), none(), 0, 0), l_true);
            // <a.S*, S*>: after the first 'a' the state is the S* fixpoint, so it
            // stays on target for every further element (reachable at len2 too)
            check("<a.S*,S*>            len2 ", reach(aSig, sig, 2, 2), l_true);
        }

        std::cout << "=== split_manager::test_intersect ===\n";
        {
            vector<seq::cont_regex> good, bad;
            good.push_back(m_sm.embed(sig));
            bad.push_back(m_sm.embed(none()));
            check("test_intersect Sigma*     ", m_sm.test_intersect(good) ? l_true : l_false, l_true);
            check("test_intersect empty      ", m_sm.test_intersect(bad) ? l_true : l_false, l_false);

            // one-sided: a+ and b+ are disjoint but neither is *syntactically*
            // empty, so the cheap check does NOT detect it (allowed false positive)
            vector<seq::cont_regex> disjoint;
            disjoint.push_back(m_sm.embed(plus(a)));
            disjoint.push_back(m_sm.embed(plus(b)));
            check("test_intersect a+,b+      ", m_sm.test_intersect(disjoint) ? l_true : l_false, l_true);

            // concat(empty, a) normalizes to the empty regex → detected
            vector<seq::cont_regex> normempty;
            normempty.push_back(m_sm.embed(cat(none(), a)));
            check("test_intersect empty-concat", m_sm.test_intersect(normempty) ? l_true : l_false, l_false);
        }

        std::cout << "=== split midpoint iterator ===\n";
        {
            seq::split sp = m_sm.mk_split(star(alt(a, b)));
            seq::split_iterator it = sp.begin();
            bool failed = it.failed();
            unsigned count = 0;
            for (; it != sp.end(); ++it) {
                seq::split_pair pr = *it;
                // left = <R, mid>, right = <mid, null>: the shared midpoint agrees
                if (pr.first.second.get() != pr.second.first.get()) ++m_fail;
                ++count;
            }
            check("(a|b)* split not failed   ", failed ? l_true : l_false, l_false);
            check("(a|b)* has >=1 midpoint   ", count > 0 ? l_true : l_false, l_true);
        }
        {
            bool failed, consistent;
            unsigned c;
            // empty regex: no live states, so no midpoints (and not a failure)
            c = split_count(none(), failed, consistent);
            check("split(empty) not failed   ", failed ? l_true : l_false, l_false);
            check("split(empty) 0 midpoints  ", c == 0 ? l_true : l_false, l_true);
            // finite word: at least one live midpoint, all pairs consistent
            c = split_count(word("a"), failed, consistent);
            check("split(a) not failed       ", failed ? l_true : l_false, l_false);
            check("split(a) >=1 midpoint     ", c >= 1 ? l_true : l_false, l_true);
            check("split(a) consistent       ", consistent ? l_true : l_false, l_true);
            // epsilon: the (single, nullable) start state is a live midpoint
            c = split_count(eps(), failed, consistent);
            check("split(eps) not failed     ", failed ? l_true : l_false, l_false);
            check("split(eps) >=1 midpoint   ", c >= 1 ? l_true : l_false, l_true);
            // ground finite word a.b.c (concat form): several live midpoints
            c = split_count(cat(a, cat(b, word("c"))), failed, consistent);
            check("split(a.b.c) not failed   ", failed ? l_true : l_false, l_false);
            check("split(a.b.c) >=1 midpoint ", c >= 1 ? l_true : l_false, l_true);
            check("split(a.b.c) consistent   ", consistent ? l_true : l_false, l_true);
        }

        std::cout << "=== seq_monadic: " << (m_fail == 0 ? "ALL PASS" : "FAILURES") << " ("
                  << m_fail << " fail) ===\n";
        ENSURE(m_fail == 0);
    }
};

}

void tst_seq_monadic() {
    seq_monadic_test t;
    t.run();
}
