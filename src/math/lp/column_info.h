/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
#include "util/vector.h"
#include <unordered_map>
#include <string>
#include <algorithm>
#include "math/lp/lp_settings.h"
namespace lp {
inline bool is_valid(unsigned j) { return static_cast<int>(j) >= 0;}

template <typename T>
class column_info {
    std::string m_name;
    bool        m_lower_bound_is_set;
    bool        m_lower_bound_is_strict;
    bool        m_upper_bound_is_set;
    bool        m_upper_bound_is_strict;
    T           m_lower_bound;
    T           m_upper_bound;
    T           m_fixed_value;
    bool        m_is_fixed;
    T           m_cost;
    unsigned    m_column_index;
public:
    bool operator==(const column_info & c) const {
        return m_name == c.m_name &&
            m_lower_bound_is_set == c.m_lower_bound_is_set &&
            m_lower_bound_is_strict == c.m_lower_bound_is_strict &&
            m_upper_bound_is_set == c.m_upper_bound_is_set&&
            m_upper_bound_is_strict == c.m_upper_bound_is_strict&&
            (!m_lower_bound_is_set || m_lower_bound == c.m_low_bound) &&
            (!m_upper_bound_is_set || m_upper_bound == c.m_upper_bound) &&
            m_cost == c.m_cost &&
            m_is_fixed == c.m_is_fixed &&
            (!m_is_fixed || m_fixed_value == c.m_fixed_value) &&
            m_column_index == c.m_column_index;
    }
    bool operator!=(const column_info & c) const { return !((*this) == c); }
    void set_column_index(unsigned j) {
        m_column_index = j;
    }
    // the default constructor
    column_info():
        m_lower_bound_is_set(false),
        m_lower_bound_is_strict(false),
        m_upper_bound_is_set (false),
        m_upper_bound_is_strict (false),
        m_is_fixed(false),
        m_cost(numeric_traits<T>::zero()),
        m_column_index(static_cast<unsigned>(-1))
    {}
    
    column_info(const column_info & ci) {
        m_name = ci.m_name;
        m_lower_bound_is_set = ci.m_lower_bound_is_set;
        m_lower_bound_is_strict = ci.m_lower_bound_is_strict;
        m_upper_bound_is_set = ci.m_upper_bound_is_set;
        m_upper_bound_is_strict = ci.m_upper_bound_is_strict;
        m_lower_bound = ci.m_lower_bound;
        m_upper_bound = ci.m_upper_bound;
        m_cost = ci.m_cost;
        m_fixed_value = ci.m_fixed_value;
        m_is_fixed = ci.m_is_fixed;
        m_column_index = ci.m_column_index;
    }

    unsigned get_column_index() const {
        return m_column_index;
    }

    column_type get_column_type() const {
        return m_is_fixed? column_type::fixed : (m_lower_bound_is_set? (m_upper_bound_is_set? column_type::boxed : column_type::lower_bound) : (m_upper_bound_is_set? column_type::upper_bound: column_type::free_column));
    }

    column_type get_column_type_no_flipping() const {
        if (m_is_fixed) {
            return column_type::fixed;
        }

        if (m_lower_bound_is_set) {
            return m_upper_bound_is_set? column_type::boxed: column_type::lower_bound;
        }
        // we are flipping the bounds!
        return m_upper_bound_is_set? column_type::upper_bound
            : column_type::free_column;
    }

    T get_lower_bound() const {
        lp_assert(m_lower_bound_is_set);
        return m_lower_bound;
    }
    T get_upper_bound() const {
        lp_assert(m_upper_bound_is_set);
        return m_upper_bound;
    }

    bool lower_bound_is_set() const {
        return m_lower_bound_is_set;
    }

    bool upper_bound_is_set() const {
        return m_upper_bound_is_set;
    }

    T get_shift() {
        if (is_fixed()) {
            return m_fixed_value;
        }
        if (is_flipped()){
            return m_upper_bound;
        }
        return m_lower_bound_is_set? m_lower_bound : numeric_traits<T>::zero();
    }

    bool is_flipped() {
        return m_upper_bound_is_set && !m_lower_bound_is_set;
    }

    bool adjusted_lower_bound_is_set() {
        return !is_flipped()? lower_bound_is_set(): upper_bound_is_set();
    }

    bool adjusted_upper_bound_is_set() {
        return !is_flipped()? upper_bound_is_set(): lower_bound_is_set();
    }

    T  get_adjusted_upper_bound() {
        return get_upper_bound() - get_lower_bound();
    }

    bool is_fixed() const {
        return m_is_fixed;
    }

    bool is_free() {
        return !m_lower_bound_is_set && !m_upper_bound_is_set;
    }

    void set_fixed_value(T v) {
        m_is_fixed = true;
        m_fixed_value = v;
    }

    T get_fixed_value() const {
        lp_assert(m_is_fixed);
        return m_fixed_value;
    }

    T get_cost() const {
        return m_cost;
    }

    void set_cost(T const & cost) {
        m_cost = cost;
    }

    void set_name(std::string const & s) {
        m_name = s;
    }

    std::string get_name() const {
        return m_name;
    }

    void set_lower_bound(T const & l) {
        m_lower_bound = l;
        m_lower_bound_is_set = true;
    }

    void set_upper_bound(T const & l) {
        m_upper_bound = l;
        m_upper_bound_is_set = true;
    }

    void unset_lower_bound() {
        m_lower_bound_is_set = false;
    }

    void unset_upper_bound() {
        m_upper_bound_is_set = false;
    }

    void unset_fixed() {
        m_is_fixed = false;
    }

    bool lower_bound_holds(T v) {
        return !lower_bound_is_set() || v >= m_lower_bound -T(0.0000001);
    }

    bool upper_bound_holds(T v) {
        return !upper_bound_is_set() || v <= m_upper_bound + T(0.000001);
    }

    bool bounds_hold(T v) {
        return lower_bound_holds(v) && upper_bound_holds(v);
    }

    bool adjusted_bounds_hold(T v) {
        return adjusted_lower_bound_holds(v) && adjusted_upper_bound_holds(v);
    }

    bool adjusted_lower_bound_holds(T v) {
        return !adjusted_lower_bound_is_set() || v >= -T(0.0000001);
    }

    bool adjusted_upper_bound_holds(T v) {
        return !adjusted_upper_bound_is_set() || v <= get_adjusted_upper_bound() + T(0.000001);
    }
    bool is_infeasible() {
        if ((!upper_bound_is_set()) || (!lower_bound_is_set()))
            return false;
        // ok, both bounds are set
        bool at_least_one_is_strict = upper_bound_is_strict() || lower_bound_is_strict();
        if (!at_least_one_is_strict)
            return get_upper_bound() < get_lower_bound();
        // at least on bound is strict
        return get_upper_bound() <= get_lower_bound(); // the equality is impossible
    }
    bool lower_bound_is_strict() const {
        return m_lower_bound_is_strict;
    }

    void set_lower_bound_strict(bool val) {
        m_lower_bound_is_strict = val;
    }

    bool upper_bound_is_strict() const {
        return m_upper_bound_is_strict;
    }

    void set_upper_bound_strict(bool val) {
        m_upper_bound_is_strict = val;
    }
};
}
