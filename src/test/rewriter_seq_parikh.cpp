// Tests for the Parikh abstraction over word equations, seq_parikh.
//
// Each case builds the constraint system for one equation and decides it on its own,
// without asserting the equation itself.  So the verdict is about the observers, not about
// the equation: `refuted` means they contradict each other, `allowed` means they do not -
// the equation may still be unsatisfiable.
//
// In the specifications below 'a'..'e' are constant characters and 'x', 'y', 'z' are
// variables.
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/seq_parikh.h"
#include "smt/smt_kernel.h"
#include "params/smt_params.h"
#include "util/rlimit.h"
#include "util/util.h"
#include <iostream>
#include <string>

namespace {

    enum class verdict { refuted, allowed, skipped };

    std::ostream& operator<<(std::ostream& out, verdict v) {
        switch (v) {
        case verdict::refuted: return out << "refuted";
        case verdict::allowed: return out << "allowed";
        default: return out << "skipped";
        }
    }

    struct fixture {
        ast_manager m;
        seq_util    u;
        sort_ref    str_sort;

        fixture(): u((reg_decl_plugins(m), m)), str_sort(u.str.mk_string_sort(), m) {}

        void side(std::string const& s, expr_ref_vector& out) {
            for (char c : s) {
                if (c >= 'x')
                    out.push_back(m.mk_const(symbol(c), str_sort));
                else
                    out.push_back(u.str.mk_unit(u.mk_char(c)));
            }
        }
    };

    unsigned g_checks = 0;
    unsigned g_failures = 0;
    unsigned g_bounded = 0;

    // decide the observation system of l = r for the grid bounded by (k, n)
    verdict observe(std::string const& l, std::string const& r, unsigned k, unsigned n) {
        fixture f;
        expr_ref_vector ls(f.m), rs(f.m), defs(f.m), eqs(f.m);
        f.side(l, ls);
        f.side(r, rs);

        seq::parikh::config cfg;
        cfg.m_k = k;
        cfg.m_n = n;
        seq::parikh parikh(f.m, cfg);
        if (!parikh(ls, rs, defs, eqs))
            return verdict::skipped;

        smt_params fp;
        // A single hard system must not stall the suite.  Running out of resources reads as
        // `allowed`, which is the safe direction: the test only complains about refutations.
        // A larger grid is strictly stronger, so any drop in the refutation count between
        // grids is this bound and nothing else - g_bounded says how often it was hit.
        scoped_rlimit rl(f.m.limit(), 2000000);
        smt::kernel solver(f.m, fp);
        for (expr* e : defs) {
            solver.assert_expr(e);
        }
        for (expr* e : eqs) {
            solver.assert_expr(e);
        }
        lbool res = solver.check();
        if (res == l_undef)
            ++g_bounded;
        return res == l_false ? verdict::refuted : verdict::allowed;
    }

    void check(std::string const& l, std::string const& r, unsigned k, unsigned n, verdict expected) {
        verdict actual = observe(l, r, k, n);
        ++g_checks;
        if (actual == expected)
            return;
        ++g_failures;
        std::cout << "seq_parikh: " << l << " = " << r << " at (" << k << "," << n
                  << ") expected " << expected << " got " << actual << std::endl;
    }

    std::string subst(std::string const& s, std::string const& x, std::string const& y) {
        std::string out;
        for (char c : s) {
            if (c == 'x')
                out += x;
            else if (c == 'y')
                out += y;
            else
                out += c;
        }
        return out;
    }

    // does some assignment of words up to max_len solve l = r?
    bool has_solution(std::string const& l, std::string const& r, unsigned max_len) {
        vector<std::string> words;
        words.push_back(std::string());
        for (unsigned i = 0; i < words.size() && words[i].size() < max_len; ++i) {
            words.push_back(words[i] + "a");
            words.push_back(words[i] + "b");
        }
        for (auto const& x : words) {
            for (auto const& y : words) {
                if (subst(l, x, y) == subst(r, x, y))
                    return true;
            }
        }
        return false;
    }

    // The abstraction is only allowed to refute.  Generate random equations, search for a
    // solution by hand, and insist that a refuted equation really has none.
    void test_random(unsigned num_equations, unsigned k, unsigned n) {
        random_gen rnd(17);
        char const* alphabet = "abxy";
        unsigned refuted = 0, skipped = 0;
        g_bounded = 0;
        for (unsigned i = 0; i < num_equations; ++i) {
            std::string l, r;
            for (unsigned j = 2 + rnd(5); j-- > 0; ) {
                l += alphabet[rnd(4)];
            }
            for (unsigned j = 2 + rnd(5); j-- > 0; ) {
                r += alphabet[rnd(4)];
            }
            verdict v = observe(l, r, k, n);
            if (v == verdict::skipped)
                ++skipped;
            if (v != verdict::refuted)
                continue;
            ++refuted;
            if (!has_solution(l, r, 6))
                continue;
            ++g_failures;
            std::cout << "seq_parikh: (" << k << "," << n << ") refuted the satisfiable equation "
                      << l << " = " << r << std::endl;
        }
        std::cout << "seq_parikh: (" << k << "," << n << ") " << num_equations
                  << " random equations, " << refuted << " refuted, " << skipped
                  << " out of scope, " << g_bounded << " over the resource bound" << std::endl;
    }

    // theory_seq feeds many equations to one seq_parikh instance and asserts every
    // definition it gets back.  The counters are shared, so definitions coming from
    // equations over different alphabets have to stay consistent with each other.
    void test_shared_alphabet() {
        char const* equations[][2] = {
            { "xa", "ax" }, { "xb", "bx" }, { "xc", "cx" },
            { "xx", "abab" }, { "bx", "xb" }, { "xcx", "cc" },
            { "xaby", "abxy" }, { "yx", "xy" }, { "xdx", "dd" }
        };
        fixture f;
        seq::parikh::config cfg;
        seq::parikh parikh(f.m, cfg);
        expr_ref_vector defs(f.m), eqs(f.m);
        for (auto const& e : equations) {
            expr_ref_vector ls(f.m), rs(f.m);
            f.side(e[0], ls);
            f.side(e[1], rs);
            parikh(ls, rs, defs, eqs);
        }
        // x = "" solves every one of them, so the definitions alone must be satisfiable
        smt_params fp;
        smt::kernel solver(f.m, fp);
        for (expr* d : defs) {
            solver.assert_expr(d);
        }
        lbool r = solver.check();
        if (r != l_true) {
            std::cout << "seq_parikh: shared definitions are inconsistent, got " << r << std::endl;
            ENSURE(false);
        }
        std::cout << "seq_parikh: shared alphabet ok, " << defs.size()
                  << " definitions over " << (sizeof(equations) / sizeof(*equations))
                  << " equations" << std::endl;
    }
}

void tst_rewriter_seq_parikh() {
    // 3|x| = 2 + |x| is solvable, but counting the characters gives 2|x|_a = 1
    check("xxx", "abx", 1, 1, verdict::refuted);

    // Parikh is satisfied, the pairs are not: x has one a and one b, but no arrangement
    // gives both sides the same pairs
    check("xx", "axb", 1, 1, verdict::allowed);
    check("xx", "axb", 2, 1, verdict::refuted);

    // yy = abba, the standard witness that adjacent pairs see more than single characters
    check("yy", "abba", 1, 1, verdict::allowed);
    check("yy", "abba", 2, 1, verdict::refuted);

    // the same equation with a common prefix left in place.  The residue observer refutes it
    // on its own: the a's on the right sit at two even positions and one odd one, which the
    // two copies of y cannot reproduce
    check("ayy", "aabba", 1, 1, verdict::allowed);
    check("ayy", "aabba", 1, 2, verdict::refuted);
    check("ayy", "aabba", 2, 1, verdict::refuted);
    check("ayy", "aabba", 2, 2, verdict::refuted);

    // the abstraction is blind to order.  a x x y = x b x x is unsatisfiable but has almost
    // solutions for every observer, so the abstraction must not refute it
    check("axxy", "xbxx", 1, 1, verdict::allowed);
    check("axxy", "xbxx", 2, 1, verdict::allowed);
    check("axxy", "xbxx", 2, 2, verdict::allowed);

    // satisfiable equations must stay satisfiable under every observer
    check("xax", "axa", 2, 2, verdict::allowed);
    check("xay", "xya", 2, 2, verdict::allowed);
    check("axb", "axb", 2, 2, verdict::allowed);
    check("xaay", "xaay", 2, 2, verdict::allowed);
    check("ax", "xa", 2, 2, verdict::allowed);
    check("xxa", "axx", 2, 2, verdict::allowed);
    check("abxy", "abxy", 2, 2, verdict::allowed);
    check("xyab", "xyab", 2, 2, verdict::allowed);
    // empty blocks: x = "" and y = "ab" solves it, so no observer may refute it
    check("xyx", "ab", 2, 2, verdict::allowed);
    check("xaybz", "aybz", 2, 2, verdict::allowed);

    // an equation without constants collapses to the length equation and is skipped
    check("xy", "yx", 2, 2, verdict::skipped);

    // the abstraction can be turned off
    check("yy", "abba", 0, 1, verdict::skipped);

    // Including the catch-all class, the default bound admits p = 5 (25 pairs)
    // and rejects p = 6 (36 pairs).
    check("abcd", "abcd", 2, 1, verdict::allowed);
    check("abcde", "abcde", 2, 1, verdict::skipped);

    // Regression for the rotation being shared across observers.  The clock is an argument
    // of the rotation, so clocks of different moduli that happen to agree used to make
    // congruence identify rotations that mean different things.  n >= 3 puts two observers
    // in the same system, which is what it takes to see this.
    for (unsigned n = 1; n <= 6; ++n) {
        check("ayyx", "aba", 1, n, verdict::allowed);   // y empty, x = "ba"
        check("aba", "ax", 1, n, verdict::allowed);     // x = "ba"
        check("xax", "axa", 2, n, verdict::allowed);    // x in a*
    }

    test_shared_alphabet();
    for (unsigned n = 1; n <= 4; ++n) {
        test_random(80, 1, n);
    }
    for (unsigned n = 1; n <= 3; ++n) {
        test_random(25, 2, n);
    }
    std::cout << "seq_parikh: " << g_checks << " directed cases, " << g_failures << " failures" << std::endl;
    ENSURE(g_failures == 0);
}
