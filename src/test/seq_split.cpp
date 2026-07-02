/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_split.cpp

Abstract:

    Unit tests for the regex split engine (the split function sigma) in
    ast/rewriter/seq_split.cpp.  The engine is exposed through split_set: a
    lazily-iterated split-set constructed from a regex, a size threshold, and an
    optional lookahead oracle.

Author:

    Clemens Eisenhofer 2026-6-22

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_split.h"
#include "ast/rewriter/th_rewriter.h"
#include <set>
#include <utility>


struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class seq_split_test {
    ast_manager      m;
    plugin_registrar m_reg;
    seq_rewriter     m_rw;
    seq_util         u;
    sort_ref         m_str;   // the sequence (String) sort
    sort_ref         m_re;    // the RegEx sort over m_str
    expr_ref_vector  m_pin;   // keeps collected/expected AST nodes alive so that
                              // pointer identity (hash-consing) is stable across
                              // the lifetime of a single check.

    seq_util::rex& re() { return u.re; }

    // pin an expr so its address stays valid for later hash-cons lookups, and
    // return the raw pointer used as a set key.
    expr* pin(expr* e) { m_pin.push_back(e); return e; }

    expr_ref eps()        { return expr_ref(re().mk_epsilon(m_str), m); }   // mk_epsilon takes the seq sort
    expr_ref dot()        { return expr_ref(re().mk_full_char(m_re), m); }  // mk_full_char takes the RegEx sort
    expr_ref dotstar()    { return expr_ref(re().mk_full_seq(m_re), m); }   // .*
    expr_ref empty_re()   { return expr_ref(re().mk_empty(m_re), m); }      // the bottom regex
    expr_ref rcat(expr* a, expr* b) { return m_rw.mk_re_append(a, b); }  // the engine's raw regex concat
    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref rng(char lo, char hi) {
        return expr_ref(re().mk_range(m_re, static_cast<unsigned>(lo), static_cast<unsigned>(hi)), m);
    }

    typedef std::set<std::pair<expr*, expr*>> pair_set;

    // Drain sigma(r) into a set of <D, N> pairs.  Returns true when the engine
    // ran to a clean exhaustion, false when it gave up (threshold overrun or an
    // unsupported regex).  Collected nodes are pinned so that the raw pointers
    // used as set keys stay valid after the split_set is destroyed.
    bool collect(expr* r, pair_set& out, unsigned threshold = UINT_MAX,
                 split_oracle const& oracle = split_oracle()) {
        split_set s(m_rw, r, threshold, oracle);
        split_set::iterator it = s.begin(), end = s.end();
        for (; it != end; ++it) {
            auto const [d, n] = *it;
            out.insert({ pin(d), pin(n) });
        }
        return !it.failed();
    }

    // Cardinality of sigma(r); requires a clean exhaustion.
    unsigned count(expr* r) {
        pair_set s;
        ENSURE(collect(r, s));
        return (unsigned)s.size();
    }

public:
    seq_split_test() : m_reg(m), m_rw(m), u(m), m_str(m), m_re(m), m_pin(m) {
        m_str = u.str.mk_string_sort();
        m_re  = re().mk_re(m_str);
    }

    void test_epsilon() {
        // sigma(eps) = { <eps, eps> }
        pair_set s;
        ENSURE(collect(eps(), s));
        ENSURE(s == pair_set({ { eps().get(), eps().get() } }));
    }

    void test_char() {
        // sigma(.) = { <eps, .>, <., eps> }
        expr_ref a = dot();
        pair_set s;
        ENSURE(collect(a, s));
        pair_set expected({ { eps().get(), a.get() }, { a.get(), eps().get() } });
        ENSURE(s == expected);
    }

    void test_word() {
        // sigma("ab") = { <"", "ab">, <"a","b">, <"ab",""> }
        pair_set s;
        ENSURE(collect(word("ab"), s));
        pair_set expected({
            { word("").get(),   word("ab").get() },
            { word("a").get(),  word("b").get()  },
            { word("ab").get(), word("").get()   },
        });
        ENSURE(s == expected);
    }

    void test_empty_word() {
        // sigma(to_re("")) = { <"", ""> }  (a single, trivial split)
        pair_set s;
        ENSURE(collect(word(""), s));
        ENSURE(s == pair_set({ { word("").get(), word("").get() } }));
    }

    void test_union() {
        // sigma(a | b) = sigma(a) cup sigma(b)
        expr_ref a = rng('a', 'a'), b = rng('b', 'b');
        expr_ref u_re(re().mk_union(a, b), m);
        pair_set s;
        ENSURE(collect(u_re, s));
        pair_set expected({
            { eps().get(), a.get() }, { a.get(), eps().get() },
            { eps().get(), b.get() }, { b.get(), eps().get() },
        });
        ENSURE(s == expected);
    }

    void test_full_seq() {
        // sigma(.*) = { <.*, .*> }
        expr_ref ds = dotstar();
        pair_set s;
        ENSURE(collect(ds, s));
        ENSURE(s == pair_set({ { ds.get(), ds.get() } }));
    }

    void test_bottom() {
        // sigma(empty) = {}
        pair_set s;
        ENSURE(collect(empty_re(), s));
        ENSURE(s.empty());
    }

    void test_star_content() {
        // sigma(a*) = { <eps,eps>, <a*.eps, a.a*>, <a*.a, eps.a*> }
        expr_ref a = rng('a', 'a');
        expr_ref as(re().mk_star(a), m);
        pair_set s;
        ENSURE(collect(as, s));
        pair_set expected({
            { eps().get(), eps().get() },
            { rcat(as, eps()).get(), rcat(a, as).get() },
            { rcat(as, a).get(),     rcat(eps(), as).get() },
        });
        ENSURE(s == expected);
    }

    void test_plus_content() {
        // sigma(a+) = a*.sigma(a).a*  (the star rule without <eps,eps>)
        expr_ref a = rng('a', 'a');
        expr_ref as(re().mk_star(a), m);
        expr_ref ap(re().mk_plus(a), m);
        pair_set s;
        ENSURE(collect(ap, s));
        pair_set expected({
            { rcat(as, eps()).get(), rcat(a, as).get() },
            { rcat(as, a).get(),     rcat(eps(), as).get() },
        });
        ENSURE(s == expected);
    }

    void test_concat_content() {
        // sigma(a.b): the engine drops the epsilon-suffix split from the left
        // side (it is language-equivalent to a right-side split), giving
        //   { <eps, a.b>, <a.eps, b>, <a.b, eps> }
        expr_ref a = rng('a', 'a'), b = rng('b', 'b');
        expr_ref ab(re().mk_concat(a, b), m);
        pair_set s;
        ENSURE(collect(ab, s));
        pair_set expected({
            { eps().get(),          rcat(a, b).get() },   // <eps, a.b>
            { rcat(a, eps()).get(), b.get()          },   // <a.eps, b>
            { rcat(a, b).get(),     eps().get()      },   // <a.b, eps>
        });
        ENSURE(s == expected);
    }

    void test_nary_union() {
        // sigma(a|b|c) has 2 splits per char-class
        expr_ref a = rng('a', 'a'), b = rng('b', 'b'), c = rng('c', 'c');
        expr_ref u3(re().mk_union(a, re().mk_union(b, c)), m);
        ENSURE(count(u3) == 6);
    }

    void test_nary_concat() {
        // sigma(a.b.c)
        expr_ref a = rng('a', 'a'), b = rng('b', 'b'), c = rng('c', 'c');
        expr_ref c3(re().mk_concat(a, re().mk_concat(b, c)), m);
        ENSURE(count(c3) >= 4);
    }

    void test_intersection() {
        // The engine handles intersection via the split algebra (De Morgan-free
        // product).  It must run to completion and produce a non-empty set.
        expr_ref inter(re().mk_inter(re().mk_star(rng('a', 'a')),
                                     re().mk_star(rng('b', 'b'))), m);
        pair_set s;
        ENSURE(collect(inter, s));
        ENSURE(!s.empty());
    }

    void test_complement() {
        // strong-mode De Morgan complement
        expr_ref compl_(re().mk_complement(re().mk_star(rng('a', 'a'))), m);
        pair_set s;
        ENSURE(collect(compl_, s));
        ENSURE(!s.empty());
    }

    void test_diff() {
        // sigma(a* \ b*) via intersection with the complement
        expr_ref diff(re().mk_diff(re().mk_star(rng('a', 'a')),
                                   re().mk_star(rng('b', 'b'))), m);
        pair_set s;
        ENSURE(collect(diff, s));
        ENSURE(!s.empty());
    }

    void test_nested_complement() {
        // sigma(~~(a*)) must still terminate cleanly
        expr_ref cc(re().mk_complement(re().mk_complement(re().mk_star(rng('a', 'a')))), m);
        pair_set s;
        ENSURE(collect(cc, s));
    }

    void test_determinism() {
        // Two independent runs over the same regex yield the identical set.
        expr_ref r(re().mk_concat(rng('a', 'a'), re().mk_star(rng('b', 'b'))), m);
        pair_set s1, s2;
        ENSURE(collect(r, s1));
        ENSURE(collect(r, s2));
        ENSURE(s1 == s2);
    }

    void test_threshold_boundary() {
        expr_ref as(re().mk_star(rng('a', 'a')), m);   // exactly 3 splits
        unsigned k = count(as);
        ENSURE(k == 3);

        pair_set ok;
        ENSURE(collect(as, ok, k));                    // at threshold: fine

        pair_set bad;
        ENSURE(!collect(as, bad, k - 1));              // one below threshold: give up
    }

    void test_threshold_giveup() {
        // a* has 3 splits; capping at 1 forces a give-up.
        expr_ref as(re().mk_star(rng('a', 'a')), m);
        pair_set s;
        ENSURE(!collect(as, s, /*threshold*/ 1));
    }

    void test_early_stop() {
        // Pull exactly one split on demand, then walk away.  Stopping early is
        // not a give-up, even when the full set is larger.
        expr_ref as(re().mk_star(rng('a', 'a')), m);   // 3 splits
        split_set s(m_rw, as, UINT_MAX, {});
        split_set::iterator it = s.begin(), end = s.end();
        unsigned seen = 0;
        if (it != end) {
            (void)*it;
            ++seen;
        }
        ENSURE(seen == 1);
        ENSURE(!it.failed());   // early stop is not a failure
    }

    void test_early_stop_after_two() {
        // Pull two splits on demand, then stop.
        expr_ref as(re().mk_star(rng('a', 'a')), m);   // 3 splits
        split_set s(m_rw, as, UINT_MAX, {});
        split_set::iterator it = s.begin(), end = s.end();
        unsigned seen = 0;
        while (seen < 2 && it != end) {
            (void)*it;
            ++it;
            ++seen;
        }
        ENSURE(seen == 2);
        ENSURE(!it.failed());
    }

    void test_iterator_exhaustion() {
        // Pull every split on demand; failed() must stay false on a clean
        // exhaustion, and end() must remain end() once drained.
        expr_ref as(re().mk_star(rng('a', 'a')), m);   // 3 splits
        split_set s(m_rw, as, UINT_MAX, {});
        split_set::iterator it = s.begin(), end = s.end();
        unsigned seen = 0;
        for (; it != end; ++it) {
            (void)*it;
            ++seen;
        }
        ENSURE(seen == 3);
        ENSURE(!it.failed());
        // idempotent past the end
        ENSURE(it == end);
        ENSURE(!it.failed());
    }

    void test_iterator_giveup() {
        // A threshold overrun aborts: the iterator reaches end() with failed().
        expr_ref as(re().mk_star(rng('a', 'a')), m);   // 3 splits, cap at 1
        split_set s(m_rw, as, 1, {});
        split_set::iterator it = s.begin(), end = s.end();
        unsigned seen = 0;
        for (; it != end; ++it) {
            (void)*it;
            ++seen;
        }
        ENSURE(it.failed());   // aborted, not a clean exhaustion
        ENSURE(seen <= 1);     // produced at most the capped number
    }

    void test_oracle_prunes() {
        // sigma(.) without an oracle = { <eps,.>, <.,eps> }; an oracle that keeps
        // only splits whose suffix is epsilon must drop one of the two.
        expr_ref a = dot();
        expr_ref e = eps();
        split_oracle keep_eps_suffix = [&](expr*, expr* n) { return n == e.get(); };

        pair_set s;
        ENSURE(collect(a, s, UINT_MAX, keep_eps_suffix));
        ENSURE(s == pair_set({ { a.get(), e.get() } }));
    }

    void test_trivial_oracle() {
        // An oracle that keeps everything leaves sigma unchanged.
        expr_ref r(re().mk_star(rng('a', 'a')), m);
        split_oracle keep_all = [](expr*, expr*) { return true; };
        pair_set s_no, s_yes;
        ENSURE(collect(r, s_no));
        ENSURE(collect(r, s_yes, UINT_MAX, keep_all));
        ENSURE(s_no == s_yes);
    }

    void run() {
        test_epsilon();
        test_char();
        test_word();
        test_empty_word();
        test_union();
        test_full_seq();
        test_bottom();
        test_star_content();
        test_plus_content();
        test_concat_content();
        test_nary_union();
        test_nary_concat();
        test_intersection();
        test_complement();
        test_diff();
        test_nested_complement();
        test_determinism();
        test_threshold_boundary();
        test_threshold_giveup();
        test_early_stop();
        test_early_stop_after_two();
        test_iterator_exhaustion();
        test_iterator_giveup();
        test_oracle_prunes();
        test_trivial_oracle();
    }
};

void tst_seq_split() {
    seq_split_test t;
    t.run();
}
