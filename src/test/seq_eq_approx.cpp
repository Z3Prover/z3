/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_approx.cpp

Abstract:

    Unit tests for the intersection of concatenations of views and the word-equation
    check in ast/rewriter/seq_eq_approx.cpp.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_eq_approx.h"
#include "ast/rewriter/seq_view.h"
#include "ast/rewriter/seq_regex_witness.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include <iostream>
#include <sstream>
#include <random>

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
    unsigned         m_fail = 0;
    expr_ref_vector  m_keep;        // the random regexes a case is built from

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

    void report(char const* name, lbool got, lbool expected) {
        bool ok = got == expected;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    void check(char const* name, expr* lhs, expr* rhs, lbool expected) {
        report(name, m_eq.check(lhs, rhs), expected);
    }

    // one equation checked with the given views installed, which are dropped afterwards
    void check_with_regex(char const* name, expr* var, expr* r, expr* lhs, expr* rhs, lbool expected) {
        m_eq.add_view(var, seq::view::membership(r));
        report(name, m_eq.check(lhs, rhs), expected);
        m_eq.unset_views(var);
    }

    void check_with_regexes(char const* name, expr* v1, expr* r1, expr* v2, expr* r2,
                            expr* lhs, expr* rhs, lbool expected) {
        m_eq.add_view(v1, seq::view::membership(r1));
        m_eq.add_view(v2, seq::view::membership(r2));
        report(name, m_eq.check(lhs, rhs), expected);
        m_eq.reset_views();
    }

    // Membership of `w` in the segments of `term`, decided by intersecting them with the
    // single segment of `w`.  This pins down the segments themselves, which the equation
    // checks only see through the verdict.
    void check_member(char const* name, expr* term, char const* w, lbool expected) {
        seq_eq_approx::segments segs, wsegs;
        m_eq.to_segments(term, segs);
        expr_ref w_re = word(w);           // a view holds a raw pointer: keep it alive
        seq::view_vector v;
        v.push_back(seq::view::membership(w_re));
        wsegs.push_back(v);
        report(name, m_eq.intersect_nonempty(segs, wsegs), expected);
    }

    // The target a character leads to in the derivative automaton of `r`: the cofactor
    // branch whose guard admits `c`.  A reach view has to be stated over the very terms
    // the transition relation produces, so a test cannot spell its target out by hand.
    expr* derivative_target(expr* r, unsigned c) {
        sort* elem_sort = nullptr;
        VERIFY(u.is_seq(m_str, elem_sort));
        expr_ref v0(m.mk_var(0, elem_sort), m);
        th_rewriter rw(m);
        for (auto const& [g, t] : m_rw.get_derive().get_cached_cofactors(
                 seq::transition_mode::light_antimirov_tm, r)) {
            expr_safe_replace rep(m);
            rep.insert(v0, u.str.mk_char(c));
            expr_ref inst(m), simp(m);
            rep(g, inst);
            rw(inst, simp);
            if (m.is_true(simp) && !re().is_empty(t))
                return t;
        }
        return nullptr;
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

    // inputs the module cannot read as segments
    void check_unsupported() {
        expr_ref x = var("x");
        report("check(x = abc)", m_eq.check(m.mk_eq(x, sword("abc"))), l_true);
        report("check(x.a = x.b)", m_eq.check(m.mk_eq(sconcat(x, sword("a")),
                                                      sconcat(x, sword("b")))), l_false);
        report("check(true)", m_eq.check(m.mk_true()), l_undef);
    }

    // the views map: conjoining, replacing, removing, clearing
    void check_mapping() {
        expr_ref x = var("x"), y = var("y");
        expr_ref aStar(star(word("a")), m), bStar(star(word("b")), m);
        seq::view_vector vs;
        vs.push_back(seq::view::membership(bStar));
        m_eq.add_view(x, seq::view::membership(aStar));
        m_eq.set_views(x, vs);                                    // replaces what x carries
        bool ok = m_eq.get_views(x) && m_eq.get_views(x)->size() == 1 &&
                  (*m_eq.get_views(x))[0].m_state == bStar.get() && m_eq.num_terms() == 1 &&
                  m_eq.get_views(y) == nullptr;
        report("views replace", ok ? l_true : l_false, l_true);
        report("x in b*: x = a", m_eq.check(x, sword("a")), l_false);
        m_eq.unset_views(x);
        report("views unset", m_eq.num_terms() == 0 ? l_true : l_false, l_true);
        report("x unconstrained: x = a", m_eq.check(x, sword("a")), l_true);
        m_eq.add_view(x, seq::view::membership(aStar));
        m_eq.reset_views();
        report("views reset", m_eq.num_terms() == 0 ? l_true : l_false, l_true);
    }

    // the state bound is reported as a give-up, never as a refutation
    void check_state_bound() {
        unsigned const saved = m_eq.max_states();
        m_eq.set_max_states(1);
        report("abc = abd, max_states=1", m_eq.check(sword("abc"), sword("abd")), l_undef);
        m_eq.set_max_states(saved);
        report("abc = abd, bound restored", m_eq.check(sword("abc"), sword("abd")), l_false);
    }

    // reach views: the runs between two states, which no regex denotes
    void check_reach_views() {
        expr_ref x = var("x"), y = var("y");
        expr_ref ab = word("ab");
        expr* after_a = derivative_target(ab, 'a');            // "ab" after reading 'a'
        if (!after_a) {
            ++m_fail;
            std::cout << "  FAIL reach views: no derivative target\n";
            return;
        }
        // x drives "ab" from its start to the state after 'a', i.e. x is exactly "a"
        m_eq.add_view(x, seq::view::reach(ab, after_a));
        report("x reaches ab-after-a: x = a", m_eq.check(x, sword("a")), l_true);
        report("x reaches ab-after-a: x = b", m_eq.check(x, sword("b")), l_false);
        report("x reaches ab-after-a: x = ab", m_eq.check(x, sword("ab")), l_false);
        report("x reaches ab-after-a: x = eps", m_eq.check(x, sword("")), l_false);
        report("x reaches ab-after-a: x.b = ab", m_eq.check(sconcat(x, sword("b")),
                                                            sword("ab")), l_true);
        report("x reaches ab-after-a: x.b = aa", m_eq.check(sconcat(x, sword("b")),
                                                            sword("aa")), l_false);
        m_eq.reset_views();

        // a* loops onto itself, so the empty word already reaches the target
        expr_ref aStar = star(word("a"));
        expr* a_after_a = derivative_target(aStar, 'a');
        m_eq.add_view(x, seq::view::reach(aStar, a_after_a));
        report("x reaches a*-after-a: x = aaa", m_eq.check(x, sword("aaa")), l_true);
        report("x reaches a*-after-a: x = eps", m_eq.check(x, sword("")), l_true);
        report("x reaches a*-after-a: x = b", m_eq.check(x, sword("b")), l_false);
        m_eq.reset_views();

        // a reach and a membership view on the same term are intersected
        m_eq.add_view(x, seq::view::reach(ab, after_a));
        m_eq.add_view(x, seq::view::membership(star(word("b"))));
        report("x reaches ab-after-a and in b*: x = a", m_eq.check(x, sword("a")), l_false);
        m_eq.reset_views();

        // reach views on both sides of the equation
        m_eq.add_view(x, seq::view::reach(ab, after_a));
        m_eq.add_view(y, seq::view::reach(ab, after_a));
        report("x = y, both reach ab-after-a", m_eq.check(x, y), l_true);
        report("x.b = y.c, both reach", m_eq.check(sconcat(x, sword("b")),
                                                   sconcat(y, sword("c"))), l_false);
        m_eq.reset_views();
    }

    // ---- randomized cross-checks --------------------------------------------------
    // The engine decides a product of cursors; these decide the same question by two
    // independent routes, so a bug in the product shows up as a disagreement.

    std::mt19937 m_rng{20260818};

    unsigned pick(unsigned n) { return m_rng() % n; }

    // a small regex over {a,b}, kept alive for the duration of the case
    expr* random_regex(unsigned depth) {
        expr_ref r(m);
        if (depth == 0) {
            switch (pick(5)) {
            case 0: r = word("a"); break;
            case 1: r = word("b"); break;
            case 2: r = word("ab"); break;
            case 3: r = dot(); break;
            default: r = word(""); break;
            }
        }
        else {
            expr* p = random_regex(depth - 1);
            expr* q = random_regex(depth - 1);
            switch (pick(6)) {
            case 0: r = cat(p, q); break;
            case 1: r = alt(p, q); break;
            case 2: r = star(p); break;
            case 3: r = loop(p, 1, 2); break;
            case 4: r = comp(p); break;
            default: r = cat(p, star(q)); break;
            }
        }
        m_keep.push_back(r);
        return r.get();
    }

    // the states a character leads to, i.e. the transition relation the engine steps in
    void step_targets(expr* state, unsigned c, ptr_vector<expr>& out) {
        sort* elem_sort = nullptr;
        VERIFY(u.is_seq(m_str, elem_sort));
        expr_ref v0(m.mk_var(0, elem_sort), m);
        th_rewriter rw(m);
        for (auto const& [g, t] : m_rw.get_derive().get_cached_cofactors(
                 seq::transition_mode::light_antimirov_tm, state)) {
            if (re().is_empty(t))
                continue;
            expr_safe_replace rep(m);
            rep.insert(v0, u.str.mk_char(c));
            expr_ref inst(m), simp(m);
            rep(g, inst);
            rw(inst, simp);
            if (m.is_true(simp) && !out.contains(t))
                out.push_back(t);
        }
    }

    // does `w` satisfy every view of one segment?  Simulated one character at a time,
    // over the set of states each view can be in.
    bool oracle_segment(seq::view_vector const& views, zstring const& w) {
        for (auto const& v : views) {
            ptr_vector<expr> states, next;
            states.push_back(v.m_state);
            for (unsigned i = 0; i < w.length(); ++i) {
                next.reset();
                for (expr* s : states)
                    step_targets(s, w[i], next);
                states = next;
            }
            bool ok = false;
            for (expr* s : states) {
                if (v.m_target)
                    ok |= s == v.m_target;
                else
                    ok |= m.is_true(m_rw.is_nullable(s));
            }
            if (!ok)
                return false;
        }
        return true;
    }

    // does `w` split across the segments so that every one of them is satisfied?
    bool oracle_word(seq_eq_approx::segments const& segs, unsigned i, zstring const& w,
                     unsigned pos) {
        if (i == segs.size())
            return pos == w.length();
        for (unsigned end = pos; end <= w.length(); ++end) {
            if (oracle_segment(segs[i], w.extract(pos, end - pos)) &&
                oracle_word(segs, i + 1, w, end))
                return true;
        }
        return false;
    }

    // the shortest word both sides accept, up to `max_len`; empty result = none found
    bool oracle_common_word(seq_eq_approx::segments const& l, seq_eq_approx::segments const& r,
                            unsigned max_len, zstring& witness) {
        for (unsigned len = 0; len <= max_len; ++len) {
            for (unsigned bits = 0; bits < (1u << len); ++bits) {
                zstring w;
                for (unsigned i = 0; i < len; ++i)
                    w = w + zstring(((bits >> i) & 1) ? 'b' : 'a');
                if (oracle_word(l, 0, w, 0) && oracle_word(r, 0, w, 0)) {
                    witness = w;
                    return true;
                }
            }
        }
        return false;
    }

    // one side: 1..3 segments, each 1..2 views over random regexes
    void random_side(seq_eq_approx::segments& out, bool with_reach) {
        unsigned n = 1 + pick(2);
        for (unsigned i = 0; i < n; ++i) {
            seq::view_vector views;
            unsigned k = 1 + pick(2);
            for (unsigned j = 0; j < k; ++j) {
                expr* r = random_regex(pick(2));
                ptr_vector<expr> targets;
                if (with_reach && pick(2) == 0) {
                    step_targets(r, pick(2) ? 'b' : 'a', targets);
                    if (!targets.empty()) {
                        views.push_back(seq::view::reach(r, targets[0]));
                        continue;
                    }
                }
                views.push_back(seq::view::membership(r));
            }
            out.push_back(views);
        }
    }

    // Views accepting exactly `part`: a membership view over the constant, or a reach
    // view driven along it, so the segment is satisfiable by construction.
    void views_for(zstring const& part, seq::view_vector& out) {
        expr_ref w(re().mk_to_re(u.str.mk_string(part)), m);
        m_keep.push_back(w);
        if (pick(2)) {
            expr* r = random_regex(pick(2));
            ptr_vector<expr> states, next;
            states.push_back(r);
            for (unsigned i = 0; i < part.length() && !states.empty(); ++i) {
                next.reset();
                for (expr* s : states)
                    step_targets(s, part[i], next);
                states = next;
            }
            if (!states.empty()) {
                out.push_back(seq::view::reach(r, states[0]));
                return;
            }
        }
        out.push_back(seq::view::membership(w));
    }

    // A side that accepts `w`: split it and constrain each part by views that hold of it.
    void side_for(zstring const& w, seq_eq_approx::segments& out) {
        unsigned pos = 0;
        while (true) {
            unsigned len = w.length() - pos == 0 ? 0 : pick(w.length() - pos + 1);
            seq::view_vector views;
            views_for(w.extract(pos, len), views);
            out.push_back(views);
            pos += len;
            if (pos == w.length())
                return;
        }
    }

    // Instances that share a word by construction: refuting one of these is a bug, and
    // this is what covers the refutation direction for reach views.
    void check_cross_positive(unsigned cases) {
        unsigned refuted = 0, decided = 0;
        for (unsigned c = 0; c < cases; ++c) {
            m_keep.reset();
            unsigned len = pick(6);
            zstring w;
            for (unsigned i = 0; i < len; ++i)
                w = w + zstring(pick(2) ? 'b' : 'a');
            seq_eq_approx::segments l, r;
            side_for(w, l);
            side_for(w, r);
            lbool got = m_eq.intersect_nonempty(l, r);
            if (got == l_undef)
                continue;
            ++decided;
            if (got == l_false) {
                ++refuted;
                std::cout << "  refuted an instance built around \"" << w.encode()
                          << "\"\n";
            }
        }
        if (refuted) ++m_fail;
        std::cout << (refuted ? "  FAIL " : "  OK   ")
                  << "cross-check on instances with a common word by construction: "
                  << decided << " decided, " << refuted << " refuted\n";
    }

    // membership-only cases: the same question stated as regexes and decided by the
    // independent search in seq::regex_witness
    void check_cross_regex(unsigned cases) {
        unsigned mismatch = 0, decided = 0;
        for (unsigned c = 0; c < cases; ++c) {
            m_keep.reset();
            seq_eq_approx::segments l, r;
            random_side(l, false);
            random_side(r, false);
            expr_ref lr(re().mk_epsilon(m_str), m), rr(re().mk_epsilon(m_str), m);
            for (auto const& seg : l)
                lr = cat(lr, seg[0].m_state);
            for (auto const& seg : r)
                rr = cat(rr, seg[0].m_state);
            for (unsigned i = 0; i < l.size(); ++i)
                if (l[i].size() > 1) { l[i].shrink(1); }
            for (unsigned i = 0; i < r.size(); ++i)
                if (r[i].size() > 1) { r[i].shrink(1); }
            lbool got = m_eq.intersect_nonempty(l, r);
            lbool expected = m_wit.intersect_nonempty(lr, rr);
            if (got == l_undef || expected == l_undef)
                continue;
            ++decided;
            if (got != expected) {
                ++mismatch;
                std::cout << "  cross-regex mismatch: engine=" << s(got)
                          << " regex_witness=" << s(expected) << " on " << mk_pp(lr, m)
                          << " vs " << mk_pp(rr, m) << "\n";
            }
        }
        if (mismatch) ++m_fail;
        std::cout << (mismatch ? "  FAIL " : "  OK   ") << "cross-check vs regex_witness: "
                  << decided << " decided, " << mismatch << " mismatches\n";
    }

    // cases with reach views: an explicit word-level simulation decides the same thing.
    // A refutation must survive it, and a word it finds must be reported as consistent.
    void check_cross_oracle(unsigned cases, unsigned max_len) {
        unsigned bad_refutation = 0, missed_word = 0, confirmed = 0;
        for (unsigned c = 0; c < cases; ++c) {
            m_keep.reset();
            seq_eq_approx::segments l, r;
            random_side(l, true);
            random_side(r, true);
            lbool got = m_eq.intersect_nonempty(l, r);
            if (got == l_undef)
                continue;
            zstring w;
            bool common = oracle_common_word(l, r, max_len, w);
            if (common) {
                ++confirmed;
                if (got != l_true) {
                    ++missed_word;
                    std::cout << "  oracle found \"" << w.encode()
                              << "\" but the engine said " << s(got) << "\n";
                }
            }
            else if (got == l_false)
                ++bad_refutation;      // no short word either: consistent with the engine
        }
        bool ok = missed_word == 0;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << "cross-check vs word oracle: "
                  << confirmed << " words confirmed, " << bad_refutation
                  << " refutations with no short word, " << missed_word << " missed\n";
    }

public:

    seq_eq_approx_test() :
        m_reg(m), m_rw(m), m_eq(m_rw), m_wit(m_rw), u(m), m_arith(m),
        m_str(u.str.mk_string_sort(), m), m_re(re().mk_re(m_str), m), m_keep(m) {}

    void run() {
        std::cout << std::unitbuf;             // keep the log usable if a case crashes
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
        // segments are constrained apart, so a repeated variable carries no information
        check("x.x = a", sconcat(x, x), sword("a"), l_true);

        std::cout << "=== seq_eq_approx: constraining the variables ===\n";
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
        // the same equation with an unconstrained variable: Sigma^* absorbs the difference
        check_with_regex("x in a*: x.b.z = x.a.z", x, star(a),
                         sconcat(x, sword("b"), z), sconcat(x, sword("a"), z), l_true);
        check_with_regex("x in ~(a*): x = aa", x, comp(star(a)), x, sword("aa"), l_false);
        check_with_regex("x in ~(a*): x = ab", x, comp(star(a)), x, sword("ab"), l_true);
        // several views on one term are conjunctive
        {
            m_eq.add_view(x, seq::view::membership(star(alt(a, b))));
            m_eq.add_view(x, seq::view::membership(star(a)));
            report("x in (a|b)* and in a*: x = b", m_eq.check(x, sword("b")), l_false);
            report("x in (a|b)* and in a*: x = aa", m_eq.check(x, sword("aa")), l_true);
            m_eq.reset_views();
        }

        std::cout << "=== seq_eq_approx: reach views ===\n";
        check_reach_views();

        std::cout << "=== seq_eq_approx: segments ===\n";
        // the segments keep their order and drop nothing
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

        std::cout << "=== seq_eq_approx: the views map ===\n";
        check_mapping();

        std::cout << "=== seq_eq_approx: unsupported input ===\n";
        check_unsupported();

        std::cout << "=== seq_eq_approx: state bound ===\n";
        check_state_bound();

        std::cout << "=== seq_eq_approx: used terms ===\n";
        {
            m_eq.add_view(x, seq::view::membership(star(a)));
            m_eq.add_view(y, seq::view::membership(star(b)));
            report("used: x in a*: x = c", m_eq.check(x, sword("c")), l_false);
            bool ok = m_eq.used().size() == 1 && m_eq.used()[0] == x.get();
            report("used reports x alone", ok ? l_true : l_false, l_true);
            report("used: x.x = b", m_eq.check(sconcat(x, x), sword("b")), l_false);
            ok = m_eq.used().size() == 1;                 // one entry per term, not per use
            report("used counts a term once", ok ? l_true : l_false, l_true);
            m_eq.reset_views();
        }

        std::cout << "=== seq_eq_approx: randomized cross-checks ===\n";
        check_cross_regex(400);
        check_cross_oracle(600, 8);
        check_cross_positive(600);

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
    seq_eq_approx_test test;
    test.run();
}
