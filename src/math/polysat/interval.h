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
#include <optional>

namespace polysat {

    struct pdd_bounds {
        pdd lo;  ///< lower bound, inclusive
        pdd hi;  ///< upper bound, exclusive
    };

    /**
     * An interval is either [lo; hi[ (excl. upper bound) or the full domain Z_{2^w}.
     * If lo > hi, the interval wraps around, i.e., represents the union of [lo; 2^w[ and [0; hi[.
     * Membership test t \in [lo; hi[ is equivalent to t - lo < hi - lo.
     */
    class interval {
        std::optional<pdd_bounds> m_bounds = std::nullopt;

        interval() = default;
        interval(pdd const& lo, pdd const& hi): m_bounds({lo, hi}) {}
    public:
        static interval empty(dd::pdd_manager& m) { return proper(m.zero(), m.zero()); }
        static interval full() { return {}; }
        static interval proper(pdd const& lo, pdd const& hi) { return {lo, hi}; }

        interval(interval const&) = default;
        interval(interval&&) = default;
        interval& operator=(interval const& other) {
            m_bounds = std::nullopt;  // clear pdds first to allow changing pdd_manager (probably should change the PDD assignment operator; but for now I want to be able to detect manager confusions)
            m_bounds = other.m_bounds;
            return *this;
        }
        interval& operator=(interval&& other) {
            m_bounds = std::nullopt;  // clear pdds first to allow changing pdd_manager
            m_bounds = std::move(other.m_bounds);
            return *this;
        }
        ~interval() = default;

        bool is_full() const { return !m_bounds; }
        bool is_proper() const { return !!m_bounds; }
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

    // distance from a to b, wrapping around at mod_value.
    // basically mod(b - a, mod_value), but distance(0, mod_value, mod_value) = mod_value.
    rational distance(rational const& a, rational const& b, rational const& mod_value) {
        SASSERT(mod_value.is_power_of_two());
        SASSERT(0 <= a && a < mod_value);
        SASSERT(0 <= b && b <= mod_value);
        rational x = b - a;
        if (x.is_neg())
            x += mod_value;
        return x;
    }

    class r_interval {
        rational m_lo;
        rational m_hi;

        r_interval(rational lo, rational hi)
            : m_lo(std::move(lo)), m_hi(std::move(hi))
        {}

    public:

        static r_interval empty() {
            return {rational::zero(), rational::zero()};
        }

        static r_interval full() {
            return {rational(-1), rational::zero()};
        }

        static r_interval proper(rational lo, rational hi) {
            SASSERT(0 <= lo);
            SASSERT(0 <= hi);
            return {std::move(lo), std::move(hi)};
        }

        bool is_full() const { return m_lo.is_neg(); }
        bool is_proper() const { return !is_full(); }
        bool is_empty() const { return is_proper() && lo() == hi(); }
        rational const& lo() const { SASSERT(is_proper()); return m_lo; }
        rational const& hi() const { SASSERT(is_proper()); return m_hi; }

        // this one also supports representing full intervals as [lo;mod_value[
        static rational len(rational const& lo, rational const& hi, rational const& mod_value) {
            SASSERT(mod_value.is_power_of_two());
            SASSERT(0 <= lo && lo < mod_value);
            SASSERT(0 <= hi && hi <= mod_value);
            SASSERT(hi != mod_value || lo == 0);  // hi == mod_value only allowed when lo == 0
            rational len = hi - lo;
            if (len.is_neg())
                len += mod_value;
            return len;
        }

        rational len(rational const& mod_value) const {
            SASSERT(is_proper());
            return len(lo(), hi(), mod_value);
        }

        // deals only with proper intervals
        // but works with full intervals represented as [0;mod_value[  -- maybe we should just change representation of full intervals to this always
        static bool contains(rational const& lo, rational const& hi, rational const& val) {
            if (lo <= hi)
                return lo <= val && val < hi;
            else
                return val < hi || val >= lo;
        }

        bool contains(rational const& val) const {
            if (is_full())
                return true;
            else
                return contains(lo(), hi(), val);
        }

    };

    class eval_interval {
        interval m_symbolic;
        rational m_concrete_lo;
        rational m_concrete_hi;

        eval_interval(interval&& i, rational const& lo_val, rational const& hi_val):
            m_symbolic(std::move(i)), m_concrete_lo(lo_val), m_concrete_hi(hi_val) {}
    public:
        static eval_interval empty(dd::pdd_manager& m) {
            return {interval::empty(m), rational::zero(), rational::zero()};
        }

        static eval_interval full() {
            return {interval::full(), rational::zero(), rational::zero()};
        }

        static eval_interval proper(pdd const& lo, rational const& lo_val, pdd const& hi, rational const& hi_val) {
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
            return mod(hi_val() - lo_val(), lo().manager().two_to_N());
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

    };  // class eval_interval

    inline std::ostream& operator<<(std::ostream& os, eval_interval const& i) {
        if (i.is_full())
            return os << "full";
        else {
            auto& m = i.hi().manager();
            return os << i.symbolic() << " := [" << m.normalize(i.lo_val()) << ";" << m.normalize(i.hi_val()) << "[";
        }
    }

}
