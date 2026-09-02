/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ssnf.cpp

Abstract:

    Unit tests for seq_ssnf (ast/rewriter/seq_ssnf.cpp): the shapes the strong
    star normal form is supposed to collapse, and a randomized cross-check that
    the rewrite preserves the language (the symmetric difference of r and
    ssnf(r) is empty).

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_regex_witness.h"
#include "ast/rewriter/seq_ssnf.h"
#include "ast/rewriter/th_rewriter.h"
#include "util/util.h"
#include <iostream>
#include <random>

namespace {

struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class ssnf_test {
    ast_manager        m;
    plugin_registrar   m_reg;
    seq_util           u;
    seq_rewriter       m_rw;
    th_rewriter        m_thrw;
    seq::regex_witness m_wit;
    seq_ssnf           m_ssnf;
    sort_ref           m_str;
    sort_ref           m_re;
    unsigned           m_fail = 0;
    unsigned           m_changed = 0;
    unsigned           m_undef = 0;

    seq_util::rex& re() { return u.re; }

    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref cat(expr* a, expr* b) { return expr_ref(re().mk_concat(a, b), m); }
    expr_ref alt(expr* a, expr* b) { return expr_ref(re().mk_union(a, b), m); }
    expr_ref star(expr* a) { return expr_ref(re().mk_star(a), m); }
    expr_ref plus(expr* a) { return expr_ref(re().mk_plus(a), m); }
    expr_ref opt(expr* a) { return expr_ref(re().mk_opt(a), m); }
    expr_ref loop(expr* a, unsigned lo, unsigned hi) { return expr_ref(re().mk_loop(a, lo, hi), m); }
    expr_ref inter(expr* a, expr* b) { return expr_ref(re().mk_inter(a, b), m); }
    expr_ref comp(expr* a) { return expr_ref(re().mk_complement(a), m); }
    expr_ref eps() { return expr_ref(re().mk_epsilon(m_str), m); }
    expr_ref none() { return expr_ref(re().mk_empty(m_re), m); }
    expr_ref dotstar() { return expr_ref(re().mk_full_seq(m_re), m); }

    // ssnf, canonicalized the way theory_nseq::preprocess_regex does
    expr_ref ssnf(expr* r) {
        expr_ref res(m_ssnf(r), m);
        m_thrw(res);
        return res;
    }

    expr_ref norm(expr* r) {
        expr_ref res(r, m);
        m_thrw(res);
        return res;
    }

    // Structural check: ssnf(r) and the expected term agree after canonicalization.
    void check_shape(char const* name, expr* r, expr* expected) {
        const expr_ref got = ssnf(r);
        const expr_ref want = norm(expected);
        const bool ok = got.get() == want.get();
        std::cout << (ok ? "PASS " : "FAIL ") << name << ": " << mk_pp(got, m);
        if (!ok) {
            std::cout << "  expected " << mk_pp(want, m);
            ++m_fail;
        }
        std::cout << "\n";
    }

    // Language check: L(r) = L(ssnf(r)).
    void check_equiv(expr* r) {
        const expr_ref s = ssnf(r);
        if (s.get() == norm(r).get())
            return;
        ++m_changed;
        const expr_ref d(m_rw.mk_symmetric_diff(r, s), m);
        // l_undef means the witness search gave up, which is not a failure
        const lbool ne = m_wit.nonempty(d);
        if (ne == l_undef)
            ++m_undef;
        if (ne == l_true) {
            std::cout << "FAIL not equivalent: " << mk_pp(r, m) << " -> " << mk_pp(s, m) << "\n";
            ++m_fail;
        }
    }

    // random regex generation for the equivalence cross-check
    expr_ref mk_random(std::mt19937& rng, unsigned depth) {
        std::uniform_int_distribution<unsigned> leaf(0, 4);
        std::uniform_int_distribution<unsigned> node(0, 8);
        std::uniform_int_distribution<unsigned> chr(0, 2);
        if (depth == 0) {
            switch (leaf(rng)) {
            case 0: return eps();
            case 1: return none();
            case 2: return dotstar();
            default: {
                char cs[2] = { (char)('a' + chr(rng)), 0 };
                return word(cs);
            }
            }
        }
        const expr_ref a = mk_random(rng, depth - 1);
        switch (node(rng)) {
        case 0: return star(a);
        case 1: return plus(a);
        case 2: return opt(a);
        case 3: return loop(a, 0, 2);
        case 4: return loop(a, 1, 3);
        case 5: return comp(a);
        case 6: return inter(a, mk_random(rng, depth - 1));
        case 7: return alt(a, mk_random(rng, depth - 1));
        default: return cat(a, mk_random(rng, depth - 1));
        }
    }

public:
    ssnf_test() :
        m_reg(m), u(m), m_rw(m), m_thrw(m),
        m_wit(m_rw), m_ssnf(u),
        m_str(u.str.mk_string_sort(), m),
        m_re(re().mk_re(m_str), m) {}

    void run() {
        const expr_ref a = word("a"), b = word("b"), c = word("c");

        std::cout << "=== ssnf: star bodies ===\n";
        check_shape("(a?b?)*", star(cat(opt(a), opt(b))), star(alt(a, b)));
        check_shape("(a*b*)*", star(cat(star(a), star(b))), star(alt(a, b)));
        check_shape("(a?|b*)*", star(alt(opt(a), star(b))), star(alt(a, b)));
        check_shape("((a|b)?)*", star(opt(alt(a, b))), star(alt(a, b)));
        check_shape("(a{0,2})*", star(loop(a, 0, 2)), star(a));
        check_shape("((a?)+)*", star(plus(opt(a))), star(a));
        check_shape("((a?b?)*c?)*", star(cat(star(cat(opt(a), opt(b))), opt(c))),
                    star(alt(alt(a, b), c)));
        // a non-nullable body is left alone
        check_shape("(ab)*", star(cat(a, b)), star(cat(a, b)));
        check_shape("(a*b)*", star(cat(star(a), b)), star(cat(star(a), b)));

        std::cout << "=== ssnf: the strong rule (nullable under ?) ===\n";
        check_shape("(a*b*)?", opt(cat(star(a), star(b))), cat(star(a), star(b)));
        // a? b is not nullable, so the option stays
        check_shape("(a?b)?", opt(cat(opt(a), b)), opt(cat(opt(a), b)));

        std::cout << "=== ssnf: sharing ===\n";
        {
            const expr_ref r = cat(a, star(b));
            const expr_ref s(m_ssnf(r), m);
            const bool ok = s.get() == r.get();
            std::cout << (ok ? "PASS " : "FAIL ") << "unchanged terms keep their identity\n";
            if (!ok)
                ++m_fail;
        }

        std::cout << "=== ssnf: language preservation (random) ===\n";
        {
            std::mt19937 rng(42);
            for (unsigned i = 0; i < 400; ++i)
                check_equiv(mk_random(rng, 3));
            std::cout << (m_changed > 0 ? "PASS " : "FAIL ") << m_changed
                      << " of 400 random regexes were rewritten, " << m_undef
                      << " equivalence checks gave up\n";
            if (m_changed == 0)
                ++m_fail;
        }

        std::cout << "=== ssnf: " << (m_fail == 0 ? "ALL PASS" : "FAILURES") << " ("
                  << m_fail << " fail) ===\n";
        ENSURE(m_fail == 0);
    }
};

}

void tst_seq_ssnf() {
    ssnf_test t;
    t.run();
}
