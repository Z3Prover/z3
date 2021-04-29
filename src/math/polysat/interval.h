/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat intervals

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/types.h"
#include "util/optional.h"

namespace polysat {

    enum class ikind_t { full, proper };

    struct bounds {
        pdd lo;  ///< lower bound, inclusive
        pdd hi;  ///< upper bound, exclusive
    };

    /**
     * An interval is either [lo; hi[ (excl. upper bound) or the full domain Z_{2^w}.
     * If lo > hi, the interval wraps around, i.e., represents the union of [lo; 2^w[ and [0; hi[.
     * Membership test t \in [lo; hi[ is equivalent to t - lo < hi - lo.
     */
    class interval {
        ikind_t m_kind;
        optional<bounds> m_bounds;

        interval(): m_kind(ikind_t::full) {}
        interval(pdd const& lo, pdd const& hi):
            m_kind(ikind_t::proper), m_bounds({lo, hi}) {}
    public:
        static interval empty(dd::pdd_manager& m) { return proper(m.zero(), m.zero()); }
        static interval full() { return {}; }
        static interval proper(pdd const& lo, pdd const& hi) { return {lo, hi}; }

        bool is_full() const { return m_kind == ikind_t::full; }
        bool is_proper() const { return m_kind == ikind_t::proper; }
        bool is_always_empty() const { return is_proper() && lo() == hi(); }
        pdd const& lo() const { SASSERT(is_proper()); return m_bounds->lo; }
        pdd const& hi() const { SASSERT(is_proper()); return m_bounds->hi; }
    };

}
