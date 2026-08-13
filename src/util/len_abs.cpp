/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    len_abs.cpp

Abstract:

    Ultimately periodic abstraction of a set of word lengths.

--*/

#include "util/len_abs.h"
#include <algorithm>
#include <numeric>
#include <ostream>

/* All residues modulo q. */
static uint64_t full_mask(unsigned q) {
    return q >= len_abs::max_period ? ~0ull : ((1ull << q) - 1);
}

/*
  Least common multiple of two effective periods, treating 0 as "adaptable" (identity).
  Returns 0 when the result would exceed max_period, signalling that the caller must degrade.
  std::lcm is not usable here: it has undefined behaviour precisely on the overflow this
  needs to detect.
*/
static unsigned bounded_lcm(unsigned a, unsigned b) {
    if (a == 0) return b;
    if (b == 0) return a;
    uint64_t l = (uint64_t)(a / std::gcd(a, b)) * b;
    return l > len_abs::max_period ? 0 : (unsigned)l;
}

/*
  A common modulus for combining two values: the lcm when it stays within max_period,
  otherwise the gcd.  Both are sound, since residues_mod over-approximates for either.
*/
static unsigned common_period(unsigned a, unsigned b) {
    unsigned q = bounded_lcm(a, b);
    if (q == 0) q = std::gcd(a, b);
    return q == 0 ? 1 : q;
}

len_abs len_abs::progression(unsigned d, unsigned stride) {
    if (stride == 0)
        return exact(d);
    if (stride > max_period)
        return len_abs(d, UINT_MAX);
    return len_abs(d, UINT_MAX, stride, 1ull << (d % stride));
}

bool len_abs::is_empty() const {
    if (m_lo > m_hi || m_residues == 0)
        return true;
    if (m_period <= 1)
        return false;
    // A window spanning at least one full period necessarily meets some residue.
    if (m_hi == UINT_MAX || m_hi - m_lo >= m_period - 1)
        return false;
    for (unsigned n = m_lo; n <= m_hi; ++n)
        if (m_residues & (1ull << (n % m_period)))
            return false;
    return true;
}

unsigned len_abs::num_residues() const {
    if (is_empty())
        return 0;
    return get_num_1bits(m_residues & full_mask(m_period));
}

uint64_t len_abs::residues_mod(unsigned q) const {
    if (q == 0 || is_empty())
        return 0;
    if (q >= max_period)
        return full_mask(q);
    uint64_t res = 0;
    // Exact when the length range is short and finite; this also covers the singleton case.
    if (m_hi != UINT_MAX && m_hi - m_lo < max_period) {
        for (unsigned n = m_lo; n <= m_hi; ++n)
            if (m_residues & (1ull << (n % m_period)))
                res |= 1ull << (n % q);
        return res;
    }
    if (q <= m_period && m_period % q == 0) {
        for (unsigned r = 0; r < m_period; ++r)
            if (m_residues & (1ull << r))
                res |= 1ull << (r % q);
        return res;
    }
    if (q > m_period && q % m_period == 0) {
        for (unsigned r = 0; r < m_period; ++r)
            if (m_residues & (1ull << r))
                for (unsigned t = r; t < q; t += m_period)
                    res |= 1ull << t;
        return res;
    }
    return full_mask(q);
}

unsigned len_abs::gcd() const {
    if (is_empty())
        return 0;
    unsigned g = 0;
    // Scanning two full periods past the minimum suffices to expose the gcd of the set.
    unsigned span = (m_period > (UINT_MAX - m_lo) / 2) ? UINT_MAX : m_lo + 2 * m_period;
    unsigned hi = std::min(m_hi, span);
    for (unsigned n = m_lo; n <= hi; ++n) {
        if (m_residues & (1ull << (n % m_period)))
            g = std::gcd(g, n);
        if (g == 1)
            return 1;
    }
    if (m_hi == UINT_MAX)
        g = std::gcd(g, m_period);
    return g;
}

len_abs len_abs::concat(len_abs const& other) const {
    len_abs r(add_truncate(m_lo, other.m_lo), add_truncate(m_hi, other.m_hi));
    // Lengths add, so residues add modulo the gcd of the two periods.
    unsigned g = std::gcd(eff_period(), other.eff_period());
    if (g > 1) {
        uint64_t a = residues_mod(g), b = other.residues_mod(g), res = 0;
        for (unsigned i = 0; i < g; ++i) {
            if (!(a & (1ull << i)))
                continue;
            for (unsigned j = 0; j < g; ++j)
                if (b & (1ull << j))
                    res |= 1ull << ((i + j) % g);
        }
        r.m_period = g;
        r.m_residues = res;
    }
    return r;
}

len_abs len_abs::unite(len_abs const& other) const {
    len_abs r(std::min(m_lo, other.m_lo), std::max(m_hi, other.m_hi));
    unsigned q = common_period(eff_period(), other.eff_period());
    if (q > 1) {
        r.m_period = q;
        r.m_residues = residues_mod(q) | other.residues_mod(q);
    }
    return r;
}

len_abs len_abs::meet(len_abs const& other) const {
    len_abs r(std::max(m_lo, other.m_lo), std::min(m_hi, other.m_hi));
    unsigned q = common_period(eff_period(), other.eff_period());
    if (q > 1) {
        r.m_period = q;
        r.m_residues = residues_mod(q) & other.residues_mod(q);
    }
    return r;
}

len_abs len_abs::star() const {
    len_abs r(0, m_hi == 0 ? 0 : UINT_MAX);
    // Every word of r* is a concatenation of words of r, so its length is a multiple of gcd.
    unsigned g = gcd();
    if (g > 1 && g <= max_period) {
        r.m_period = g;
        r.m_residues = 1;
    }
    return r;
}

len_abs len_abs::plus() const {
    len_abs r(m_lo, m_hi == 0 ? 0 : UINT_MAX);
    unsigned g = gcd();
    if (g > 1 && g <= max_period) {
        r.m_period = g;
        r.m_residues = 1;
    }
    return r;
}

len_abs len_abs::opt() const {
    // Lambda(r?) = Lambda(r) union {0}
    return len_abs(0, m_hi, m_period, m_residues | 1ull);
}

len_abs len_abs::loop(unsigned lower, unsigned upper) const {
    len_abs r(mul_truncate(m_lo, lower), mul_truncate(m_hi, upper));
    if (upper == UINT_MAX || upper > max_period) {
        // Unbounded (or very wide) repetition: every element is a multiple of the gcd.
        unsigned g = gcd();
        if (g > 1 && g <= max_period) {
            r.m_period = g;
            r.m_residues = 1;
        }
    }
    else {
        // Bounded repetition: union of the k-fold sumsets of the residues, lower <= k <= upper.
        // A fixed-length operand has period 1 but a non-trivial gcd, and that gcd is the
        // modulus to use; without it (aaaa){1,3} would keep only the bounds [4,12] and
        // lose that every length is a multiple of 4.
        unsigned q = m_period > 1 ? m_period : gcd();
        if (q > 1 && q <= max_period) {
            uint64_t base = residues_mod(q), acc = 0, cur = 1ull /* k = 0 */;
            for (unsigned k = 0; k <= upper; ++k) {
                if (k >= lower)
                    acc |= cur;
                uint64_t next = 0;
                for (unsigned i = 0; i < q; ++i) {
                    if (!(cur & (1ull << i)))
                        continue;
                    for (unsigned j = 0; j < q; ++j)
                        if (base & (1ull << j))
                            next |= 1ull << ((i + j) % q);
                }
                cur = next;
            }
            r.m_period = q;
            r.m_residues = acc;
        }
    }
    return r;
}

std::ostream& len_abs::display(std::ostream& out) const {
    if (m_period <= 1)
        return out;
    out << ", lengths=";
    bool first = true;
    for (unsigned r = 0; r < m_period; ++r)
        if (m_residues & (1ull << r)) {
            out << (first ? "" : "|") << r;
            first = false;
        }
    if (first)
        out << "{}";
    return out << " mod " << m_period;
}

bool len_abs::residue_reachable(unsigned period, uint64_t residues, unsigned cst, unsigned g) {
    if (period == 0)
        return true;
    unsigned c = cst % period;
    // Lengths cst + g*k, k >= 0, cover exactly the residues congruent to cst modulo
    // gcd(g, period); with g = 0 the only reachable length residue is cst itself.
    unsigned d = g == 0 ? period : std::gcd(g, period);
    for (unsigned i = 0; i < period; ++i) {
        if (0 == (residues & (1ull << i)))
            continue;
        if (g == 0) {
            if (i == c)
                return true;
        }
        else if ((i + period - c) % d == 0)
            return true;
    }
    return false;
}