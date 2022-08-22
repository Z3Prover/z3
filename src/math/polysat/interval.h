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

    inline std::ostream& operator<<(std::ostream& os, interval const& i) {
        if (i.is_full())
            return os << "full";
        else
            return os << "[" << i.lo() << " ; " << i.hi() << "[";
    }

    class eval_interval {
        interval m_symbolic;
        rational m_concrete_lo;
        rational m_concrete_hi;

        eval_interval(interval&& i, rational const& lo_val, rational const& hi_val):
            m_symbolic(std::move(i)), m_concrete_lo(lo_val), m_concrete_hi(hi_val) {}
    public:
        static eval_interval empty(dd::pdd_manager &m) {
            return {interval::empty(m), rational::zero(), rational::zero()};
        }
        static eval_interval full() {
            return {interval::full(), rational::zero(), rational::zero()};
        }
        static eval_interval proper(pdd const &lo, rational const &lo_val, pdd const &hi, rational const &hi_val) {
            SASSERT(0 <= lo_val && lo_val <= lo.manager().max_value());
            SASSERT(0 <= hi_val && hi_val <= hi.manager().max_value());
            return {interval::proper(lo, hi), lo_val, hi_val};
        }

        bool is_full() const { return m_symbolic.is_full(); }
        bool is_proper() const { return m_symbolic.is_proper(); }
        bool is_always_empty() const { return m_symbolic.is_always_empty(); }
        bool is_currently_empty() const { return is_proper() && lo_val() == hi_val(); }
        interval const& symbolic() const { return m_symbolic; }
        pdd const& lo() const { return m_symbolic.lo(); }
        pdd const& hi() const { return m_symbolic.hi(); }
        rational const& lo_val() const { SASSERT(is_proper()); return m_concrete_lo; }
        rational const& hi_val() const { SASSERT(is_proper()); return m_concrete_hi; }
        rational current_len() const {
            SASSERT(is_proper());
            return mod(hi_val() - lo_val(), rational::power_of_two(lo().power_of_2()));
        }
        bool currently_contains(rational const& val) const {
            if (is_full())
                return true;
            else if (lo_val() <= hi_val())
                return lo_val() <= val && val < hi_val();
            else
                return val < hi_val() || val >= lo_val();
        }
        bool currently_contains(eval_interval const& other) const {
            if (is_full())
                return true;
            if (other.is_full())
                return false;
            // lo <= lo' <= hi' <= hi'
            if (lo_val() <= other.lo_val() && other.lo_val() <= other.hi_val() && other.hi_val() <= hi_val())
                return true;
            if (lo_val() <= hi_val())
                return false;
            // hi < lo <= lo' <= hi'
            if (lo_val() <= other.lo_val() && other.lo_val() <= other.hi_val())
                return true;
            // lo' <= hi' <= hi < lo 
            if (other.lo_val() <= other.hi_val() && other.hi_val() <= hi_val())
                return true;
            // hi' <= hi < lo <= lo'
            if (other.hi_val() <= hi_val() && lo_val() <= other.lo_val())
                return true;
            return false;
        }

        eval_interval intersect(eval_interval const& other) const {
            if (is_full()) return other;
            if (other.is_full()) return *this;

            pdd i_lo = lo();
            rational i_lo_val = lo_val();
            if (lo_val() < other.lo_val()) {
                i_lo = other.lo();
                i_lo_val = other.lo_val();
            }

            pdd i_hi = hi();
            rational i_hi_val = hi_val();
            if (hi_val() > other.hi_val()) {
                i_hi = other.hi();
                i_hi_val = other.hi_val();
            }

            return eval_interval::proper(i_lo, i_lo_val, i_hi, i_hi_val);
        }
    };

    inline std::ostream& operator<<(std::ostream& os, eval_interval const& i) {
        auto& m = i.hi().manager();
        if (i.is_full())
            return os << "full";
        else
            return os << i.symbolic() << " := [" << m.normalize(i.lo_val()) << ";" << m.normalize(i.hi_val()) << "[";
    }


}
