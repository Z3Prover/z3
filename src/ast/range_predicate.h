/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    range_predicate.h

Abstract:

    Specialized range-algebra over an unsigned character domain [0, max_char].

    A range_predicate represents a subset of the character domain as a
    sorted sequence of non-overlapping, non-adjacent, non-empty ranges:

        [(lo_0, hi_0), (lo_1, hi_1), ...] with hi_i + 1 < lo_{i+1}.

    The representation is canonical, so two range_predicates over the same
    domain are extensionally equivalent iff their internal vectors are
    elementwise equal.

    All Boolean operations (union, intersection, complement, difference)
    are linear in the total number of ranges and produce the canonical
    representation.

    Intended use:
      * path conditions for symbolic derivative computation,
      * OneStep predicates capturing length-1 acceptance,
      * smart-constructor side conditions for regex rewrites such as
        R & psi  -->  toregex(OneStep(R) & psi).

    The type is a pure value: no ast_manager allocation occurs in its
    construction or its Boolean operations. Conversion to and from
    expr* is the responsibility of a separate translator (see callers
    in seq_derive / seq_rewriter).

Authors:

    Margus Veanes (veanes) 2026

--*/
#pragma once

#include "util/vector.h"
#include <iosfwd>
#include <utility>

namespace seq {

    class range_predicate {
        using range_t  = std::pair<unsigned, unsigned>;
        using ranges_t = svector<range_t>;

        // Sorted by first; ranges are disjoint and non-adjacent;
        // every range satisfies lo <= hi <= m_max_char.
        ranges_t m_ranges;
        unsigned m_max_char { 0 };

        // Invariant check used in debug builds.
        bool well_formed() const;

    public:
        range_predicate() = default;
        explicit range_predicate(unsigned max_char) : m_max_char(max_char) {}

        // ---------------- Factory functions ----------------

        static range_predicate empty(unsigned max_char);
        static range_predicate top(unsigned max_char);
        static range_predicate singleton(unsigned c, unsigned max_char);
        static range_predicate range(unsigned lo, unsigned hi, unsigned max_char);

        // ---------------- Observers ----------------

        unsigned max_char()        const { return m_max_char; }
        unsigned num_ranges()      const { return m_ranges.size(); }
        range_t  operator[](unsigned i) const { return m_ranges[i]; }
        ranges_t const& ranges()   const { return m_ranges; }

        bool is_empty() const { return m_ranges.empty(); }
        bool is_top()   const {
            return m_ranges.size() == 1
                && m_ranges[0].first == 0
                && m_ranges[0].second == m_max_char;
        }
        bool is_singleton(unsigned& c) const {
            if (m_ranges.size() != 1) return false;
            if (m_ranges[0].first != m_ranges[0].second) return false;
            c = m_ranges[0].first;
            return true;
        }
        bool contains(unsigned c) const;

        // Number of characters in the predicate (well-defined for any domain).
        uint64_t cardinality() const;

        // ---------------- Equality, ordering, hashing ----------------

        bool equals(range_predicate const& o) const;
        bool operator==(range_predicate const& o) const { return equals(o); }
        bool operator!=(range_predicate const& o) const { return !equals(o); }

        // Total order: lexicographic on the canonical range sequence,
        // with shorter sequences ordered before longer prefixes.
        // Predicates over different domains compare by max_char first.
        bool operator<(range_predicate const& o) const;
        bool less_than(range_predicate const& o) const { return *this < o; }

        unsigned hash() const;

        // ---------------- Boolean operations ----------------

        range_predicate operator|(range_predicate const& o) const;   // union
        range_predicate operator&(range_predicate const& o) const;   // intersection
        range_predicate operator-(range_predicate const& o) const;   // difference
        range_predicate operator^(range_predicate const& o) const;   // symmetric diff
        range_predicate operator~() const;                            // complement

        // ---------------- Display ----------------

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, range_predicate const& p) {
        return p.display(out);
    }

}
