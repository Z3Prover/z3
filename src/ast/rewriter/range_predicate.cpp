/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    range_predicate.cpp

Abstract:

    Implementation of the specialized range-algebra used by symbolic
    derivative computation and regex rewriting. See range_predicate.h
    for the algebraic specification.

    All Boolean operations are implemented as single linear sweeps over
    the canonical sorted range vectors and produce canonical output
    (sorted, disjoint, non-adjacent).

Authors:

    Margus Veanes (veanes) 2026

--*/

#include "ast/rewriter/range_predicate.h"
#include "util/debug.h"
#include <algorithm>
#include <ostream>

namespace seq {

    // -----------------------------------------------------------------------
    // Factories
    // -----------------------------------------------------------------------

    range_predicate range_predicate::empty(unsigned max_char) {
        return range_predicate(max_char);
    }

    range_predicate range_predicate::top(unsigned max_char) {
        range_predicate r(max_char);
        r.m_ranges.push_back({0u, max_char});
        SASSERT(r.well_formed());
        return r;
    }

    range_predicate range_predicate::singleton(unsigned c, unsigned max_char) {
        SASSERT(c <= max_char);
        range_predicate r(max_char);
        r.m_ranges.push_back({c, c});
        SASSERT(r.well_formed());
        return r;
    }

    range_predicate range_predicate::range(unsigned lo, unsigned hi, unsigned max_char) {
        range_predicate r(max_char);
        if (lo <= hi && lo <= max_char) {
            unsigned clipped_hi = hi <= max_char ? hi : max_char;
            r.m_ranges.push_back({lo, clipped_hi});
        }
        SASSERT(r.well_formed());
        return r;
    }

    // -----------------------------------------------------------------------
    // Invariants and observers
    // -----------------------------------------------------------------------

    bool range_predicate::well_formed() const {
        for (unsigned i = 0; i < m_ranges.size(); ++i) {
            auto [lo, hi] = m_ranges[i];
            if (lo > hi) return false;
            if (hi > m_max_char) return false;
            if (i > 0) {
                unsigned prev_hi = m_ranges[i - 1].second;
                // Non-adjacent and sorted: prev_hi + 1 < lo, with care
                // around prev_hi == UINT_MAX which we never expect because
                // hi <= m_max_char.
                if (prev_hi + 1 >= lo) return false;
            }
        }
        return true;
    }

    bool range_predicate::contains(unsigned c) const {
        // Binary search on first element of pairs.
        unsigned lo = 0, hi = m_ranges.size();
        while (lo < hi) {
            unsigned mid = lo + (hi - lo) / 2;
            auto [a, b] = m_ranges[mid];
            if (c < a) hi = mid;
            else if (c > b) lo = mid + 1;
            else return true;
        }
        return false;
    }

    uint64_t range_predicate::cardinality() const {
        uint64_t n = 0;
        for (auto [lo, hi] : m_ranges)
            n += static_cast<uint64_t>(hi) - static_cast<uint64_t>(lo) + 1u;
        return n;
    }

    // -----------------------------------------------------------------------
    // Equality, ordering, hashing
    // -----------------------------------------------------------------------

    bool range_predicate::equals(range_predicate const& o) const {
        if (m_max_char != o.m_max_char) return false;
        if (m_ranges.size() != o.m_ranges.size()) return false;
        for (unsigned i = 0; i < m_ranges.size(); ++i)
            if (m_ranges[i] != o.m_ranges[i]) return false;
        return true;
    }

    bool range_predicate::operator<(range_predicate const& o) const {
        if (m_max_char != o.m_max_char)
            return m_max_char < o.m_max_char;
        unsigned n = std::min(m_ranges.size(), o.m_ranges.size());
        for (unsigned i = 0; i < n; ++i) {
            auto a = m_ranges[i];
            auto b = o.m_ranges[i];
            if (a.first  != b.first)  return a.first  < b.first;
            if (a.second != b.second) return a.second < b.second;
        }
        return m_ranges.size() < o.m_ranges.size();
    }

    unsigned range_predicate::hash() const {
        // FNV-1a 32-bit over (max_char, then each (lo, hi)).
        uint32_t h = 2166136261u;
        auto step = [&](uint32_t x) {
            h ^= x;
            h *= 16777619u;
        };
        step(m_max_char);
        for (auto [lo, hi] : m_ranges) {
            step(lo);
            step(hi);
        }
        return h;
    }

    // -----------------------------------------------------------------------
    // Boolean operations
    // -----------------------------------------------------------------------

    namespace {
        // Append (lo, hi) to result, merging with the previous range if
        // adjacent or overlapping. Maintains canonical form.
        inline void append_merged(svector<std::pair<unsigned, unsigned>>& result,
                                  unsigned lo, unsigned hi) {
            SASSERT(lo <= hi);
            if (!result.empty() && result.back().second + 1 >= lo) {
                if (result.back().second < hi)
                    result.back().second = hi;
            } else {
                result.push_back({lo, hi});
            }
        }
    }

    range_predicate range_predicate::operator|(range_predicate const& o) const {
        SASSERT(m_max_char == o.m_max_char);
        range_predicate r(m_max_char);
        unsigned i = 0, j = 0;
        const unsigned n = m_ranges.size();
        const unsigned m = o.m_ranges.size();
        while (i < n && j < m) {
            auto a = m_ranges[i];
            auto b = o.m_ranges[j];
            if (a.first <= b.first) {
                append_merged(r.m_ranges, a.first, a.second);
                ++i;
            } else {
                append_merged(r.m_ranges, b.first, b.second);
                ++j;
            }
        }
        while (i < n) {
            auto a = m_ranges[i++];
            append_merged(r.m_ranges, a.first, a.second);
        }
        while (j < m) {
            auto b = o.m_ranges[j++];
            append_merged(r.m_ranges, b.first, b.second);
        }
        SASSERT(r.well_formed());
        return r;
    }

    range_predicate range_predicate::operator&(range_predicate const& o) const {
        SASSERT(m_max_char == o.m_max_char);
        range_predicate r(m_max_char);
        unsigned i = 0, j = 0;
        const unsigned n = m_ranges.size();
        const unsigned m = o.m_ranges.size();
        while (i < n && j < m) {
            auto [a_lo, a_hi] = m_ranges[i];
            auto [b_lo, b_hi] = o.m_ranges[j];
            unsigned lo = std::max(a_lo, b_lo);
            unsigned hi = std::min(a_hi, b_hi);
            if (lo <= hi)
                r.m_ranges.push_back({lo, hi});
            // Advance the range that ends first.
            if (a_hi < b_hi) ++i;
            else if (b_hi < a_hi) ++j;
            else { ++i; ++j; }
        }
        SASSERT(r.well_formed());
        return r;
    }

    range_predicate range_predicate::operator~() const {
        range_predicate r(m_max_char);
        unsigned cursor = 0;
        for (auto [lo, hi] : m_ranges) {
            if (cursor < lo)
                r.m_ranges.push_back({cursor, lo - 1});
            // Step past hi without overflow: hi <= m_max_char and we
            // only step when more characters remain.
            if (hi >= m_max_char) {
                cursor = m_max_char + 1; // sentinel: no more characters
                break;
            }
            cursor = hi + 1;
        }
        if (cursor <= m_max_char)
            r.m_ranges.push_back({cursor, m_max_char});
        SASSERT(r.well_formed());
        return r;
    }

    range_predicate range_predicate::operator-(range_predicate const& o) const {
        SASSERT(m_max_char == o.m_max_char);
        // A - B by linear sweep: for each range of A, subtract overlapping
        // ranges of B. Both inputs are sorted so we advance j monotonically.
        range_predicate r(m_max_char);
        unsigned j = 0;
        const unsigned m = o.m_ranges.size();
        for (auto [a_lo, a_hi] : m_ranges) {
            unsigned cursor = a_lo;
            while (j < m && o.m_ranges[j].second < cursor)
                ++j;
            unsigned k = j;
            while (k < m && o.m_ranges[k].first <= a_hi) {
                auto [b_lo, b_hi] = o.m_ranges[k];
                if (cursor < b_lo)
                    r.m_ranges.push_back({cursor, std::min(a_hi, b_lo - 1)});
                if (b_hi >= a_hi) {
                    cursor = a_hi + 1;
                    break;
                }
                cursor = b_hi + 1;
                ++k;
            }
            if (cursor <= a_hi)
                r.m_ranges.push_back({cursor, a_hi});
        }
        SASSERT(r.well_formed());
        return r;
    }

    range_predicate range_predicate::operator^(range_predicate const& o) const {
        SASSERT(m_max_char == o.m_max_char);
        // (A | B) - (A & B), but implemented directly with one linear sweep
        // over the union of breakpoints.
        return (*this | o) - (*this & o);
    }

    // -----------------------------------------------------------------------
    // Display
    // -----------------------------------------------------------------------

    std::ostream& range_predicate::display(std::ostream& out) const {
        if (m_ranges.empty()) {
            return out << "[]";
        }
        out << "[";
        bool first = true;
        for (auto [lo, hi] : m_ranges) {
            if (!first) out << ",";
            first = false;
            if (lo == hi)
                out << lo;
            else
                out << lo << "-" << hi;
        }
        return out << "]";
    }

}
