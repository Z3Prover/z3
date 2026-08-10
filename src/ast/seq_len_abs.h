/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_len_abs.h

Abstract:

    Ultimately periodic abstraction of a set of word lengths.

    A regular language L has a semilinear length set Lambda(L) = { |w| : w in L }.
    This module keeps a sound over-approximation of Lambda as the value

        { n : lo <= n <= hi, (n mod period) in residues }

    with period in [1, max_period] and bit i of residues (i < period) recording that
    length residue i is possible.  The trivial value lo = 0, hi = UINT_MAX, period = 1,
    residues = 1 constrains nothing and is the default.

    Only the containment Lambda subseteq value is required, so every operation may
    safely weaken its result: a rule can cost precision, never soundness.  Complement
    therefore degrades to top.

    The abstraction refutes what plain length bounds cannot.  (a^4)* and (b^6)* both
    have bounds [0, oo), yet |z| in 4N together with |w| in 6N and |z| + 1 = |w| is
    refuted by 6n - 4m = 1, which linear arithmetic closes with its gcd test once the
    residues are visible to it.  Likewise (ab)* and a(ba)* have period 2 with residues
    {0} and {1}, so their intersection is empty.

    Keeping a residue *set* rather than a single arithmetic progression d + g*N is what
    makes the abstraction closed under union: for (aa)* | (aaa)* a single progression
    degrades to gcd(2, 3) = 1 and says nothing, while this representation records
    period 6 with residues {0, 2, 3, 4} and still refutes lengths 1 and 5 mod 6.

    The value is producer-agnostic.  It can be computed syntactically by structural
    recursion over a regex (see seq_decl_plugin's rex::info), or semantically from a
    derivative automaton via a BFS potential function -- see progression().  Two sound
    abstractions of the same Lambda may always be combined with meet().

--*/
#pragma once

#include "util/util.h"
#include <cstdint>
#include <climits>
#include <iosfwd>

namespace seq {

    class len_abs {
        unsigned m_lo { 0 };
        unsigned m_hi { UINT_MAX };
        unsigned m_period { 1 };
        uint64_t m_residues { 1 };

    public:
        /*
          Residues are held in a 64 bit mask, so the period cannot exceed 64.
          Operations that would need a larger modulus degrade instead.
        */
        static constexpr unsigned max_period = 64;

        len_abs() = default;

        len_abs(unsigned lo, unsigned hi) : m_lo(lo), m_hi(hi) {}

        len_abs(unsigned lo, unsigned hi, unsigned period, uint64_t residues) :
            m_lo(lo), m_hi(hi), m_period(period), m_residues(residues) {}

        /* The empty set of lengths. */
        static len_abs empty() { return len_abs(1, 0); }

        /* Exactly the length n. */
        static len_abs exact(unsigned n) { return len_abs(n, n); }

        /*
          The single arithmetic progression d + stride*N, the abstraction produced by a
          BFS potential function over an automaton: d is the distance to the state and
          stride the gcd of the edge slacks.  stride == 0 means the length is exactly d.
        */
        static len_abs progression(unsigned d, unsigned stride);

        unsigned lo() const { return m_lo; }
        unsigned hi() const { return m_hi; }
        unsigned period() const { return m_period; }
        uint64_t residues() const { return m_residues; }

        void set_bounds(unsigned lo, unsigned hi) { m_lo = lo; m_hi = hi; }

        /* True when the abstraction is trivial, i.e. records no periodicity. */
        bool is_trivial() const { return m_period <= 1; }

        /*
          True when the abstracted set is empty, which certifies that L is empty.
          Sound in one direction only: a false result proves nothing.
        */
        bool is_empty() const;

        /* Number of possible residues; 0 iff the abstracted set is empty. */
        unsigned num_residues() const;

        /*
          Over-approximates the residues modulo q, as a bitmask over [0, q).
          Handles both projection (q divides period) and lifting (period divides q),
          and enumerates exactly when the length range is short and finite.
        */
        uint64_t residues_mod(unsigned q) const;

        /*
          The gcd of the abstracted set; 0 when that set is empty or is exactly {0}.
          Used by star/plus/loop, since every sum of elements is a multiple of the gcd.
        */
        unsigned gcd() const;

        /*
          Period to use when combining with another value.  A set with at most one
          element is congruent to that element modulo *any* period, so it adapts to the
          other operand; 0 signals "adaptable" and composes correctly under gcd and lcm.
        */
        unsigned eff_period() const { return m_lo == m_hi ? 0 : m_period; }

        /* Lambda(r s) = Lambda(r) + Lambda(s), pointwise sums. */
        len_abs concat(len_abs const& other) const;

        /* Lambda(r | s) = Lambda(r) union Lambda(s). */
        len_abs unite(len_abs const& other) const;

        /*
          Any set contained in both operands, so this is sound for intersection and for
          combining two independently computed abstractions of the same language.
        */
        len_abs meet(len_abs const& other) const;

        len_abs star() const;
        len_abs plus() const;
        len_abs opt() const;
        len_abs loop(unsigned lower, unsigned upper) const;

        bool operator==(len_abs const& other) const {
            return m_lo == other.m_lo && m_hi == other.m_hi &&
                   m_period == other.m_period && m_residues == other.m_residues;
        }

        bool operator!=(len_abs const& other) const { return !(*this == other); }

        /* Appends ", lengths=r1|r2 mod p" when the abstraction is non-trivial. */
        std::ostream& display(std::ostream& out) const;
    };

}
