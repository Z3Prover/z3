/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    test/seq_profile_abs.cpp

Abstract:

    Unit tests for seq::profile_abs, the per-letter Parikh abstraction
    refined by length.

    The abstraction has two directions, and the tests check both against a
    brute-force oracle rather than against hand-computed masks alone:

      * profiles(R) OVER-approximates: w in L(R) implies profile(w) is in
        the mask.  Verified by enumerating every word up to a small length
        over a small alphabet and matching it against R with an independent
        reference matcher.

      * forced(R) UNDER-approximates: if profile p is in forced(R) then
        EVERY word with profile p lies in L(R).  Verified by searching the
        same word set for a counterexample.

    Both properties are what the consumer relies on for refutation, so a
    regression in either direction is a soundness bug, not a precision loss.

Author:

    Margus Veanes (veanes) 2026

--*/
#include "ast/rewriter/seq_profile_abs.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_pp.h"
#include "util/util.h"

#include <iostream>
#include <set>
#include <string>
#include <vector>

namespace {

    using seq::profile_abs;

    static unsigned const LCAP = 2;

    static void check(bool ok, char const* what) {
        if (!ok) {
            std::cerr << "seq_profile_abs FAILED: " << what << "\n";
            ENSURE(false);
        }
    }

    static inline unsigned pbit(unsigned c, unsigned l) { return 1u << (c * 3 + l); }

    // ---- reference matcher -------------------------------------------
    //
    // match_set(r, w, i) = { j : w[i..j) in L(r) }.  Computing the set of
    // end positions rather than a yes/no answer makes concat, star and
    // intersection straightforward and keeps complement exact.

    class matcher {
        seq_util& u;
        std::string const& w;

    public:
        matcher(seq_util& u, std::string const& w) : u(u), w(w) {}

        std::set<unsigned> ends(expr* r, unsigned i) {
            std::set<unsigned> res;
            unsigned const n = (unsigned)w.size();
            expr *a = nullptr, *b = nullptr, *s = nullptr;
            unsigned lo = 0, hi = 0;
            zstring str;

            if (u.re.is_empty(r))
                return res;
            if (u.re.is_full_seq(r)) {
                for (unsigned j = i; j <= n; ++j)
                    res.insert(j);
                return res;
            }
            if (u.re.is_full_char(r)) {
                if (i < n)
                    res.insert(i + 1);
                return res;
            }
            if (u.re.is_to_re(r, s) && u.str.is_string(s, str)) {
                unsigned const L = str.length();
                if (i + L <= n) {
                    bool ok = true;
                    for (unsigned k = 0; k < L && ok; ++k)
                        ok = (unsigned)(unsigned char)w[i + k] == str[k];
                    if (ok)
                        res.insert(i + L);
                }
                return res;
            }
            if (u.re.is_range(r, lo, hi)) {
                if (i < n) {
                    unsigned c = (unsigned)(unsigned char)w[i];
                    if (lo <= c && c <= hi)
                        res.insert(i + 1);
                }
                return res;
            }
            if (u.re.is_concat(r, a, b)) {
                for (unsigned mid : ends(a, i))
                    for (unsigned j : ends(b, mid))
                        res.insert(j);
                return res;
            }
            if (u.re.is_union(r, a, b)) {
                for (unsigned j : ends(a, i)) res.insert(j);
                for (unsigned j : ends(b, i)) res.insert(j);
                return res;
            }
            if (u.re.is_intersection(r, a, b)) {
                std::set<unsigned> ra = ends(a, i), rb = ends(b, i);
                for (unsigned j : ra)
                    if (rb.count(j))
                        res.insert(j);
                return res;
            }
            if (u.re.is_diff(r, a, b)) {
                std::set<unsigned> rb = ends(b, i);
                for (unsigned j : ends(a, i))
                    if (!rb.count(j))
                        res.insert(j);
                return res;
            }
            if (u.re.is_complement(r, a)) {
                // w[i..j) not in L(a), for every j
                std::set<unsigned> ra = ends(a, i);
                for (unsigned j = i; j <= n; ++j)
                    if (!ra.count(j))
                        res.insert(j);
                return res;
            }
            if (u.re.is_star(r, a)) {
                res.insert(i);
                bool grew = true;
                while (grew) {
                    grew = false;
                    std::vector<unsigned> cur(res.begin(), res.end());
                    for (unsigned p : cur)
                        for (unsigned j : ends(a, p))
                            if (j > p && res.insert(j).second)
                                grew = true;
                }
                return res;
            }
            if (u.re.is_plus(r, a)) {
                for (unsigned mid : ends(a, i)) {
                    expr_ref st(u.re.mk_star(a), u.get_manager());
                    for (unsigned j : ends(st, mid))
                        res.insert(j);
                }
                return res;
            }
            if (u.re.is_opt(r, a)) {
                res.insert(i);
                for (unsigned j : ends(a, i)) res.insert(j);
                return res;
            }
            std::cerr << "seq_profile_abs: reference matcher has no case for "
                      << mk_pp(r, u.get_manager()) << "\n";
            ENSURE(false);
            return res;
        }

        bool matches(expr* r) {
            return ends(r, 0).count((unsigned)w.size()) > 0;
        }
    };

    // Every word of length <= max_len over `alphabet`.
    static void all_words(std::string const& alphabet, unsigned max_len,
                          std::vector<std::string>& out) {
        out.push_back("");
        size_t start = 0;
        for (unsigned len = 1; len <= max_len; ++len) {
            size_t end = out.size();
            for (size_t k = start; k < end; ++k)
                for (char c : alphabet)
                    out.push_back(out[k] + c);
            start = end;
        }
    }

    static unsigned word_profile(std::string const& w, unsigned sigma, unsigned mod) {
        unsigned cnt = 0;
        for (char c : w)
            if ((unsigned)(unsigned char)c == sigma)
                ++cnt;
        return pbit(cnt % mod, std::min((unsigned)w.size(), LCAP));
    }

    static expr_ref chr(seq_util& u, char c) {
        return expr_ref(u.re.mk_to_re(u.str.mk_string(zstring((unsigned)(unsigned char)c))),
                        u.get_manager());
    }

    static void run() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        profile_abs abs(m);

        sort* str_sort = u.str.mk_string_sort();
        sort* re_sort = u.re.mk_re(str_sort);

        expr_ref a(chr(u, 'a')), b(chr(u, 'b'));
        expr_ref dot(u.re.mk_full_char(re_sort), m);
        expr_ref all(u.re.mk_full_seq(re_sort), m);

        // The battery deliberately includes the extended idioms that the
        // length refinement exists for.
        expr_ref_vector battery(m);
        battery.push_back(a);                                          // "a"
        battery.push_back(u.re.mk_concat(a, a));                       // "aa"
        battery.push_back(u.re.mk_union(a, b));                        // a | b
        battery.push_back(u.re.mk_star(a));                            // a*
        battery.push_back(u.re.mk_plus(a));                            // a+
        battery.push_back(u.re.mk_opt(a));                             // a?
        battery.push_back(u.re.mk_star(u.re.mk_concat(a, a)));         // (aa)*
        battery.push_back(u.re.mk_union(u.re.mk_star(u.re.mk_concat(a, a)),
                                        u.re.mk_star(u.re.mk_concat(a, u.re.mk_concat(a, a)))));
        battery.push_back(u.re.mk_inter(dot, u.re.mk_complement(a)));  // . & ~a
        battery.push_back(u.re.mk_complement(a));                      // ~a
        battery.push_back(u.re.mk_complement(u.re.mk_star(a)));        // ~(a*)
        battery.push_back(u.re.mk_diff(dot, a));                       // . \ a
        battery.push_back(u.re.mk_concat(u.re.mk_star(a), b));         // a* b
        battery.push_back(u.re.mk_inter(u.re.mk_star(a), u.re.mk_complement(u.re.mk_concat(a, a))));
        battery.push_back(dot);
        battery.push_back(all);
        battery.push_back(u.re.mk_empty(re_sort));

        std::vector<std::string> words;
        all_words("abc", 4, words);

        unsigned checked = 0;
        for (unsigned mod = 2; mod <= 4; ++mod) {
            for (char sig : std::string("ab")) {
                unsigned sigma = (unsigned)(unsigned char)sig;
                for (expr* r : battery) {
                    abs.begin_pass(mod, sigma);
                    unsigned const prof = abs.profiles(r);
                    unsigned const forc = abs.forced(r);

                    for (std::string const& w : words) {
                        matcher mt(u, w);
                        bool const in = mt.matches(r);
                        unsigned const p = word_profile(w, sigma, mod);

                        // over-approximation: membership implies the bit is set
                        if (in && !(prof & p)) {
                            std::cerr << "profiles() unsound for "
                                      << mk_pp(r, m) << " on \"" << w << "\""
                                      << " (mod " << mod << ", sigma " << sig << ")\n";
                            check(false, "profiles over-approximation");
                        }
                        // under-approximation: a forced bit admits no non-member
                        if (!in && (forc & p)) {
                            std::cerr << "forced() unsound for "
                                      << mk_pp(r, m) << " on \"" << w << "\""
                                      << " (mod " << mod << ", sigma " << sig << ")\n";
                            check(false, "forced under-approximation");
                        }
                        ++checked;
                    }
                }
            }
        }

        // Note: forced() is NOT contained in profiles().  A profile that no
        // word realizes -- e.g. length 1 with two occurrences of sigma -- is
        // vacuously forced, since every word realizing it (there are none)
        // lies in L(R), yet it is absent from profiles(R).  The two masks are
        // deliberately independent approximations.

        // ---- concrete residue expectations ----

        // "aa" counting 'a' mod 2 -> only residue 0
        {
            unsigned res = abs.regex_residues(u.re.mk_concat(a, a), 2, 'a');
            check(res == 0x1, "residues of \"aa\" mod 2 = {0}");
        }
        // "a" counting 'a' mod 2 -> only residue 1
        {
            unsigned res = abs.regex_residues(a, 2, 'a');
            check(res == 0x2, "residues of \"a\" mod 2 = {1}");
        }
        // (aa)* counting 'a' mod 2 -> only residue 0
        {
            unsigned res = abs.regex_residues(u.re.mk_star(u.re.mk_concat(a, a)), 2, 'a');
            check(res == 0x1, "residues of (aa)* mod 2 = {0}");
        }
        // . & ~a is exactly one non-'a' character: residue 0, and it must
        // NOT degrade to "all residues" -- this is the case the length
        // refinement exists for.
        {
            expr_ref e(u.re.mk_inter(dot, u.re.mk_complement(a)), m);
            unsigned res = abs.regex_residues(e, 3, 'a');
            check(res == 0x1, "residues of (. & ~a) mod 3 = {0}");
        }
        // re.all carries no information.
        {
            unsigned res = abs.regex_residues(all, 3, 'a');
            check(res == 0x7, "residues of re.all mod 3 = all");
        }
        // out-of-range modulus is rejected
        {
            check(abs.regex_residues(a, 1, 'a') == UINT_MAX, "modulus 1 rejected");
            check(abs.regex_residues(a, profile_abs::max_modulus + 1, 'a') == UINT_MAX,
                  "modulus above max rejected");
        }

        std::cerr << "seq_profile_abs tests passed (" << checked
                  << " word/regex soundness checks)\n";
    }
}

void tst_seq_profile_abs() {
    run();
}
