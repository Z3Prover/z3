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

namespace lp {
template <typename T>
class indexed_value {
public:
    T m_value;
    // the idea is that m_index for a row element gives its column, and for a column element its row
    unsigned m_index;
    // m_other point is the offset of the corresponding element in its vector : for a row element it point to the column element offset,
    // for a column element it points to the row element offset
    unsigned m_other;
    indexed_value() {}
    indexed_value(T v, unsigned i) : m_value(v), m_index(i) {}
    indexed_value(T v, unsigned i, unsigned other) :
        m_value(v), m_index(i), m_other(other) {
    }

    indexed_value(const indexed_value & iv) {
        m_value = iv.m_value;
        m_index = iv.m_index;
        m_other = iv.m_other;
    }

    indexed_value & operator=(const indexed_value & right_side) {
        m_value = right_side.m_value;
        m_index = right_side.m_index;
        m_other = right_side.m_other;
        return *this;
    }

    const T & value() const {
        return m_value;
    }

    void set_value(T val) {
        m_value = val;
    }
};
#ifdef Z3DEBUG
template <typename X>
bool check_vector_for_small_values(indexed_vector<X> & w, lp_settings & settings) {
    for (unsigned i : w.m_index) {
        const X & v = w[i];
        if ((!is_zero(v)) && settings.abs_val_is_smaller_than_drop_tolerance(v))
            return false;
    }
    return true;
}
#endif
}
