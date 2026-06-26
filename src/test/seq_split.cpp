/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_split.cpp

Abstract:

    Unit tests for the regex split engine (the split function sigma) in ast/rewriter/seq_split.cpp.

Author:

    Clemens Eisenhofer 2026-6-22

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_split.h"
#include <set>
#include <utility>


struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class seq_split_test {
    ast_manager     m;
    plugin_registrar m_reg;
    seq_rewriter    m_rw;
    seq_split       m_split;
    seq_util        u;
    sort_ref        m_str;   // the sequence (String) sort
    sort_ref        m_re;    // the RegEx sort over m_str

    seq_util::rex& re() { return u.re; }

    expr_ref eps()        { return expr_ref(re().mk_epsilon(m_str), m); }   // mk_epsilon takes the seq sort
    expr_ref dot()        { return expr_ref(re().mk_full_char(m_re), m); }  // mk_full_char takes the RegEx sort
    expr_ref dotstar()    { return expr_ref(re().mk_full_seq(m_re), m); }   // .*
    expr_ref empty_re()   { return expr_ref(re().mk_empty(m_re), m); }      // the bottom regex
    expr_ref rappend(expr* a, expr* b) { return m_rw.mk_re_append(a, b); }  // the engine's regex concat
    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref rng(char lo, char hi) {
        return expr_ref(re().mk_range(u.str.mk_string(zstring(std::string(1, lo).c_str())),
                                      u.str.mk_string(zstring(std::string(1, hi).c_str()))), m);
    }

    typedef std::set<std::pair<expr*, expr*>> pair_set;

    pair_set as_set(split_set const& s) {
        pair_set out;
        for (auto const& p : s)
            out.insert({ p.m_d.get(), p.m_n.get() });
        return out;
    }

    bool eager(expr* r, split_set& out, unsigned threshold = UINT_MAX,
               split_mode mode = split_mode::strong, split_oracle const& oracle = {}) {
        return m_split.compute(r, out, threshold, mode, oracle);
    }

    bool lazy(expr* r, split_set& out, unsigned threshold = UINT_MAX,
              split_mode mode = split_mode::strong, split_oracle const& oracle = {}) {
        expr_ref node = m_split.make(r);
        ENSURE(node);
        return m_split.enumerate(node, mode, threshold, oracle,
                                 [&](expr* d, expr* n) { out.push_back(split_pair(d, n, m)); return true; });
    }

    // assert that the eager and lazy engines agree on sigma(r) as a *set* of
    // splits, and report the common cardinality.
    unsigned check_agree(expr* r) {
        split_set se, sl;
        bool oke = eager(r, se);
        bool okl = lazy(r, sl);
        ENSURE(oke == okl);
        if (!oke)
            return 0;
        ENSURE(as_set(se) == as_set(sl));
        return (unsigned)as_set(se).size();
    }

public:
    seq_split_test() : m_reg(m), m_rw(m), m_split(m_rw), u(m), m_str(m), m_re(m) {
        m_str = u.str.mk_string_sort();
        m_re  = re().mk_re(m_str);
    }

    void test_eager_epsilon() {
        split_set s;
        ENSURE(eager(eps(), s));
        ENSURE(as_set(s) == pair_set({ { eps().get(), eps().get() } }));
    }

    void test_eager_char() {
        // sigma(.) = { <eps, .>, <., eps> }
        expr_ref a = dot();
        split_set s;
        ENSURE(eager(a, s));
        pair_set expected({ { eps().get(), a.get() }, { a.get(), eps().get() } });
        ENSURE(as_set(s) == expected);
    }

    void test_eager_word() {
        // sigma("ab") = { <"", "ab">, <"a","b">, <"ab",""> }
        split_set s;
        ENSURE(eager(word("ab"), s));
        pair_set expected({
            { word("").get(),  word("ab").get() },
            { word("a").get(), word("b").get()  },
            { word("ab").get(), word("").get()  },
        });
        ENSURE(as_set(s) == expected);
    }

    void test_eager_union() {
        // sigma(a | b) = sigma(a) cup sigma(b)
        expr_ref a = rng('a', 'a'), b = rng('b', 'b');
        expr_ref u_re(re().mk_union(a, b), m);
        split_set s;
        ENSURE(eager(u_re, s));
        pair_set expected({
            { eps().get(), a.get() }, { a.get(), eps().get() },
            { eps().get(), b.get() }, { b.get(), eps().get() },
        });
        ENSURE(as_set(s) == expected);
    }

    void test_agree_all() {
        expr_ref a = rng('a', 'a'), b = rng('b', 'b');
        expr_ref star(re().mk_star(a), m);
        expr_ref plus(re().mk_plus(a), m);
        expr_ref concat(re().mk_concat(a, b), m);
        expr_ref uni(re().mk_union(a, b), m);
        expr_ref inter(re().mk_inter(re().mk_star(a), re().mk_star(b)), m);
        expr_ref compl_(re().mk_complement(re().mk_star(a)), m);
        expr_ref diff(re().mk_diff(re().mk_star(a), re().mk_star(b)), m);

        ENSURE(check_agree(eps())  == 1);
        ENSURE(check_agree(a)      == 2);
        ENSURE(check_agree(word("ab")) == 3);
        ENSURE(check_agree(uni)    == 4);
        ENSURE(check_agree(star)   == 3);   // { <eps,eps>, <a*, a.a*>, <a*.a, a*> }
        (void)check_agree(plus);
        (void)check_agree(concat);
        (void)check_agree(inter);            // strong-mode intersection
        (void)check_agree(compl_);           // strong-mode De Morgan complement
        (void)check_agree(diff);
    }

    void test_lazy_early_stop() {
        // a* has 3 splits; stop after the first one.  (Note .* is the full_seq
        // special case with a single split, so use a proper char-class body.)
        expr_ref star(re().mk_star(rng('a', 'a')), m);
        expr_ref node = m_split.make(star);
        ENSURE(node);
        unsigned seen = 0;
        bool ok = m_split.enumerate(node, split_mode::strong, UINT_MAX, {},
                                    [&](expr*, expr*) { ++seen; return false; /* stop now */ });
        ENSURE(ok);              // early stop is reported as success
        ENSURE(seen == 1);       // and nothing was produced past the stop
    }

    void test_threshold_giveup() {
        expr_ref star(re().mk_star(rng('a', 'a')), m);   // 3 splits
        split_set s;
        ENSURE(!lazy(star, s, /*threshold*/ 1));
        // the eager wrapper honours the same cap
        split_set s2;
        ENSURE(!eager(star, s2, /*threshold*/ 1));
    }

    void test_weak_vs_strong() {
        expr_ref inter(re().mk_inter(re().mk_star(rng('a', 'a')), re().mk_star(rng('b', 'b'))), m);
        expr_ref compl_(re().mk_complement(re().mk_star(dot())), m);

        split_set s;
        ENSURE(!eager(inter, s, UINT_MAX, split_mode::weak));
        s.reset();
        ENSURE(!lazy(inter, s, UINT_MAX, split_mode::weak));
        s.reset();
        ENSURE(!eager(compl_, s, UINT_MAX, split_mode::weak));
        s.reset();
        ENSURE(!lazy(compl_, s, UINT_MAX, split_mode::weak));

        // strong mode succeeds for both
        s.reset();
        ENSURE(eager(inter, s, UINT_MAX, split_mode::strong));
        s.reset();
        ENSURE(eager(compl_, s, UINT_MAX, split_mode::strong));
    }

    void test_make_non_regex() {
        expr_ref not_a_regex(u.str.mk_string(zstring("a")), m);   // String, not RegEx
        expr_ref node = m_split.make(not_a_regex);
        ENSURE(!node);
    }

    void test_oracle_prunes() {
        // sigma(.) without an oracle = { <eps,.>, <.,eps> }; an oracle that keeps
        // only splits whose suffix is epsilon must drop one of the two.
        expr_ref a = dot();
        expr_ref e = eps();
        split_oracle keep_eps_suffix = [&](expr*, expr* n) { return n == e.get(); };

        split_set se, sl;
        ENSURE(eager(a, se, UINT_MAX, split_mode::strong, keep_eps_suffix));
        ENSURE(lazy(a, sl, UINT_MAX, split_mode::strong, keep_eps_suffix));
        pair_set expected({ { a.get(), e.get() } });
        ENSURE(as_set(se) == expected);
        ENSURE(as_set(sl) == expected);
    }

    void test_eager_full_seq() {
        // sigma(.*) = { <.*, .*> }
        expr_ref ds = dotstar();
        split_set s;
        ENSURE(eager(ds, s));
        ENSURE(as_set(s) == pair_set({ { ds.get(), ds.get() } }));
    }

    void test_eager_bottom() {
        // sigma(empty) = {}
        split_set s;
        ENSURE(eager(empty_re(), s));
        ENSURE(s.empty());

        split_set sl;
        ENSURE(lazy(empty_re(), sl));
        ENSURE(sl.empty());
    }

    void test_eager_empty_word() {
        // sigma(to_re("")) = { <"", ""> }  (a single, trivial split)
        split_set s;
        ENSURE(eager(word(""), s));
        ENSURE(as_set(s) == pair_set({ { word("").get(), word("").get() } }));
    }

    void test_eager_star_content() {
        // sigma(a*) = { <eps,eps>, <a*.eps, a.a*>, <a*.a, eps.a*> }
        expr_ref a = rng('a', 'a');
        expr_ref as(re().mk_star(a), m);
        split_set s;
        ENSURE(eager(as, s));
        pair_set expected({
            { eps().get(), eps().get() },
            { rappend(as, eps()).get(), rappend(a, as).get() },
            { rappend(as, a).get(),     rappend(eps(), as).get() },
        });
        ENSURE(as_set(s) == expected);
    }

    void test_eager_plus_content() {
        // sigma(a+) = a*.sigma(a).a*  (the star rule without <eps,eps>)
        expr_ref a = rng('a', 'a');
        expr_ref as(re().mk_star(a), m);
        expr_ref ap(re().mk_plus(a), m);
        split_set s;
        ENSURE(eager(ap, s));
        pair_set expected({
            { rappend(as, eps()).get(), rappend(a, as).get() },
            { rappend(as, a).get(),     rappend(eps(), as).get() },
        });
        ENSURE(as_set(s) == expected);
    }

    void test_eager_concat_content() {
        // sigma(a.b) = sigma(a).b cup a.sigma(b)
        expr_ref a = rng('a', 'a'), b = rng('b', 'b');
        expr_ref ab(re().mk_concat(a, b), m);
        split_set s;
        ENSURE(eager(ab, s));
        pair_set expected({
            { eps().get(),           rappend(a, b).get()   },   // <eps, a.b>
            { a.get(),               rappend(eps(), b).get() }, // <a, eps.b>
            { rappend(a, eps()).get(), b.get()             },   // <a.eps, b>
            { rappend(a, b).get(),   eps().get()           },   // <a.b, eps>
        });
        ENSURE(as_set(s) == expected);
    }

    void test_nary_union() {
        // sigma(a|b|c) has 2 splits per char-class
        expr_ref a = rng('a', 'a'), b = rng('b', 'b'), c = rng('c', 'c');
        expr_ref u3(re().mk_union(a, re().mk_union(b, c)), m);
        ENSURE(check_agree(u3) == 6);
    }

    void test_nary_concat() {
        // sigma(a.b.c)
        expr_ref a = rng('a', 'a'), b = rng('b', 'b'), c = rng('c', 'c');
        expr_ref c3(re().mk_concat(a, re().mk_concat(b, c)), m);
        ENSURE(check_agree(c3) >= 4);
    }

    void test_nested_complement() {
        // sigma(~~(a*))
        expr_ref cc(re().mk_complement(re().mk_complement(re().mk_star(rng('a', 'a')))), m);
        (void)check_agree(cc);
    }

    void test_determinism() {
        expr_ref r(re().mk_concat(rng('a', 'a'), re().mk_star(rng('b', 'b'))), m);
        split_set s1, s2;
        ENSURE(lazy(r, s1));
        ENSURE(lazy(r, s2));
        ENSURE(as_set(s1) == as_set(s2));
    }

    void test_threshold_boundary() {
        expr_ref as(re().mk_star(rng('a', 'a')), m);   // exactly 3 splits
        split_set s;
        ENSURE(eager(as, s));
        unsigned k = (unsigned)as_set(s).size();
        ENSURE(k == 3);

        split_set ok_e, ok_l, bad_e, bad_l;
        ENSURE(eager(as, ok_e, k));
        ENSURE(lazy(as, ok_l, k));
        ENSURE(!eager(as, bad_e, k - 1));   // one below threshold; give up
        ENSURE(!lazy(as, bad_l, k - 1));
    }

    void test_early_stop_after_two() {
        expr_ref as(re().mk_star(rng('a', 'a')), m);   // 3 splits
        expr_ref node = m_split.make(as);
        ENSURE(node);
        unsigned seen = 0;
        bool ok = m_split.enumerate(node, split_mode::strong, UINT_MAX, {},
                                    [&](expr*, expr*) { ++seen; return seen < 2; });
        ENSURE(ok);
        ENSURE(seen == 2);
    }

    void test_simplify() {
        expr_ref regs[] = {
            expr_ref(re().mk_star(rng('a', 'a')), m),
            expr_ref(re().mk_complement(re().mk_star(rng('a', 'a'))), m),
            expr_ref(re().mk_concat(rng('a', 'a'), rng('b', 'b')), m),
        };
        for (auto& r : regs) {
            split_set s;
            ENSURE(eager(r, s));
            unsigned before = (unsigned)s.size();
            m_split.simplify(s);
            ENSURE(s.size() <= before);
            ENSURE(!s.empty());
            // idempotent
            split_set s2(s);
            m_split.simplify(s2);
            ENSURE(as_set(s) == as_set(s2));
        }
    }

    void test_trivial_oracle() {
        expr_ref r(re().mk_star(rng('a', 'a')), m);
        split_oracle keep_all = [](expr*, expr*) { return true; };
        split_set s_no, s_yes;
        ENSURE(eager(r, s_no));
        ENSURE(eager(r, s_yes, UINT_MAX, split_mode::strong, keep_all));
        ENSURE(as_set(s_no) == as_set(s_yes));
    }

    void run() {
        test_eager_epsilon();
        test_eager_char();
        test_eager_word();
        test_eager_union();
        test_agree_all();
        test_lazy_early_stop();
        test_threshold_giveup();
        test_weak_vs_strong();
        test_make_non_regex();
        test_oracle_prunes();
        test_eager_full_seq();
        test_eager_bottom();
        test_eager_empty_word();
        test_eager_star_content();
        test_eager_plus_content();
        test_eager_concat_content();
        test_nary_union();
        test_nary_concat();
        test_nested_complement();
        test_determinism();
        test_threshold_boundary();
        test_early_stop_after_two();
        test_simplify();
        test_trivial_oracle();
    }
};

void tst_seq_split() {
    seq_split_test t;
    t.run();
}
