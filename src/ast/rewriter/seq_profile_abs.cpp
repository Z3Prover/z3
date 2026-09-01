/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_profile_abs.cpp

Abstract:

    Per-letter Parikh abstraction refined by length.  See seq_profile_abs.h.

--*/
#include "ast/rewriter/seq_profile_abs.h"
#include "util/zstring.h"

namespace seq {
    static const unsigned LCAP = 2;

    static inline unsigned pbit(unsigned c, unsigned l) { return 1u << (c * 3 + l); }

    void profile_abs::begin_pass(unsigned modulus, unsigned sigma) {
        SASSERT(2 <= modulus && modulus <= max_modulus);
        m_pk_mod = modulus;
        m_pk_sigma = sigma;
        m_pk_top = 0;
        for (unsigned c = 0; c < modulus; ++c)
            for (unsigned l = 0; l <= LCAP; ++l)
                m_pk_top |= pbit(c, l);
        m_pk_budget = 1 << 14;
        m_pk_prof.reset();
        m_pk_forced.reset();
    }

    unsigned profile_abs::prof_cat(unsigned a1, unsigned a2) const {
        if (a1 == 0 || a2 == 0)
            return 0;
        unsigned r = 0;
        for (unsigned c1 = 0; c1 < m_pk_mod; ++c1)
            for (unsigned l1 = 0; l1 <= LCAP; ++l1) {
                if (!(a1 & pbit(c1, l1)))
                    continue;
                for (unsigned c2 = 0; c2 < m_pk_mod; ++c2)
                    for (unsigned l2 = 0; l2 <= LCAP; ++l2)
                        if (a2 & pbit(c2, l2))
                            r |= pbit((c1 + c2) % m_pk_mod, std::min(l1 + l2, LCAP));
            }
        return r;
    }

    // Binary exponentiation: the profile masks form a monoid under prof_cat
    // with unit {(0,0)}, so A^n is exact and costs O(log n) products.
    unsigned profile_abs::prof_pow(unsigned a1, unsigned n) const {
        unsigned r = pbit(0, 0), base = a1;
        while (n > 0) {
            if (n & 1)
                r = prof_cat(r, base);
            n >>= 1;
            if (n > 0)
                base = prof_cat(base, base);
        }
        return r;
    }

    unsigned profile_abs::prof_star(unsigned a1) const {
        unsigned r = pbit(0, 0);
        while (true) {
            const unsigned next = r | prof_cat(r, a1);
            if (next == r)
                return r;
            r = next;
        }
    }

    unsigned profile_abs::prof_loop(unsigned a1, unsigned lo, unsigned hi) const {
        if (lo > hi)
            return 0;
        const unsigned base = prof_pow(a1, lo);
        // A^lo..A^hi is contained in A^lo · A*, which is cheap and sound; take it
        // whenever enumerating the exponents one by one would be the costlier of
        // the two.  The lattice has only 3·m elements, so nothing is lost.
        if (hi - lo > 3 * m_pk_mod)
            return prof_cat(base, prof_star(a1));
        unsigned r = 0, cur = base;
        for (unsigned i = lo; i <= hi; ++i) {
            r |= cur;
            cur = prof_cat(cur, a1);
        }
        return r;
    }

    unsigned profile_abs::prof_chars(bool has_sigma, bool has_other) const {
        unsigned r = 0;
        if (has_sigma)
            r |= pbit(1 % m_pk_mod, 1);
        if (has_other)
            r |= pbit(0, 1);
        return r;
    }

    unsigned profile_abs::forced(expr* re) {
        unsigned r = 0;
        if (m_pk_forced.find(re, r))
            return r;
        if (m_pk_budget == 0)
            return 0;               // sound: claim nothing is forced
        --m_pk_budget;

        expr* x = nullptr;
        zstring s;
        unsigned lo = 0, hi = 0;
        if (seq.re.is_full_seq(re))
            r = m_pk_top;
        else if (seq.re.is_full_char(re)) {
            // every one-character word belongs to allchar
            for (unsigned c = 0; c < m_pk_mod; ++c)
                r |= pbit(c, 1);
        }
        else if (seq.re.is_to_re(re, x) && seq.str.is_string(x, s)) {
            if (s.length() == 0)
                r = pbit(0, 0);                       // eps is the only word of profile (0,0)
            else if (s.length() == 1 && s[0] == m_pk_sigma)
                r = pbit(1 % m_pk_mod, 1);            // sigma is the only word of profile (1,1)
        }
        else if (seq.re.is_range(re, lo, hi)) {
            if (lo <= m_pk_sigma && m_pk_sigma <= hi)
                r = pbit(1 % m_pk_mod, 1);
        }
        else if (seq.re.is_union(re)) {
            for (expr* arg : *to_app(re))
                r |= forced(arg);
        }
        else if (seq.re.is_intersection(re)) {
            r = m_pk_top;
            for (expr* arg : *to_app(re))
                r &= forced(arg);
        }
        else if (seq.re.is_complement(re, x))
            r = m_pk_top & ~profiles(x);
        else if (seq.re.is_star(re, x) || seq.re.is_opt(re, x))
            r = forced(x) | pbit(0, 0);
        m_pk_forced.insert(re, r);
        return r;
    }

    unsigned profile_abs::profiles(expr* re) {
        unsigned r = 0;
        if (m_pk_prof.find(re, r))
            return r;
        if (m_pk_budget == 0)
            return m_pk_top;        // sound: claim every profile is possible
        --m_pk_budget;

        expr* x = nullptr;
        expr* y = nullptr;
        zstring s;
        unsigned lo = 0, hi = 0;
        if (seq.re.is_empty(re))
            r = 0;
        else if (seq.re.is_full_seq(re))
            r = m_pk_top;
        else if (seq.re.is_full_char(re))
            r = prof_chars(true, true);
        else if (seq.re.is_to_re(re, x)) {
            if (seq.str.is_string(x, s)) {
                unsigned cnt = 0;
                for (unsigned i = 0; i < s.length(); ++i)
                    if (s[i] == m_pk_sigma)
                        ++cnt;
                r = pbit(cnt % m_pk_mod, std::min(s.length(), LCAP));
            }
            else
                r = m_pk_top;
        }
        else if (seq.re.is_concat(re)) {
            r = pbit(0, 0);
            for (expr* arg : *to_app(re)) {
                r = prof_cat(r, profiles(arg));
                if (r == 0)
                    break;
            }
        }
        else if (seq.re.is_union(re)) {
            for (expr* arg : *to_app(re))
                r |= profiles(arg);
        }
        else if (seq.re.is_intersection(re)) {
            r = m_pk_top;
            for (expr* arg : *to_app(re))
                r &= profiles(arg);
        }
        else if (seq.re.is_star(re, x))
            r = prof_star(profiles(x));
        else if (seq.re.is_plus(re, x)) {
            const unsigned p = profiles(x);
            r = prof_cat(p, prof_star(p));
        }
        else if (seq.re.is_opt(re, x))
            r = profiles(x) | pbit(0, 0);
        else if (seq.re.is_complement(re, x))
            r = m_pk_top & ~forced(x);
        else if (seq.re.is_diff(re, x, y))
            r = profiles(x) & (m_pk_top & ~forced(y));
        else if (seq.re.is_range(re, lo, hi)) {
            if (lo > hi)
                r = 0;              // SMT-LIB: an inverted range is the empty language
            else {
                const bool has_sigma = lo <= m_pk_sigma && m_pk_sigma <= hi;
                r = prof_chars(has_sigma, hi > lo || !has_sigma);
            }
        }
        else if (seq.re.is_loop(re, x, lo, hi))
            r = prof_loop(profiles(x), lo, hi);
        else if (seq.re.is_loop(re, x, lo)) {
            const unsigned p = profiles(x);
            r = prof_cat(prof_pow(p, lo), prof_star(p));
        }
        else
            r = m_pk_top;           // of_pred, reverse, derivative, ...
        m_pk_prof.insert(re, r);
        return r;
    }

    unsigned profile_abs::regex_residues(expr* re, unsigned modulus, unsigned sigma) {
        if (modulus < 2 || modulus > max_modulus)
            return UINT_MAX;
        begin_pass(modulus, sigma);
        const unsigned mask = profiles(re);
        unsigned res = 0;
        for (unsigned c = 0; c < modulus; ++c)
            for (unsigned l = 0; l <= LCAP; ++l)
                if (mask & pbit(c, l)) {
                    res |= 1u << c;
                    break;
                }
        return res;
    }

    // -----------------------------------------------------------------------
    // Congruence refutation
} // namespace seq
