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
#include <string>
#include <algorithm>
#include <utility>
#include "math/lp/column_info.h"
#include "math/lp/lp_types.h"

namespace lp {


inline bool kind_is_strict(lconstraint_kind kind) { return kind == LT || kind == GT;}

inline std::ostream& operator<<(std::ostream& out, lconstraint_kind k) {
    switch (k) {
    case LE: return out << "<=";
    case LT: return out << "<";
    case GE: return out << ">=";
    case GT: return out << ">";
    case EQ: return out << "=";
    case NE: return out << "!=";
    }
    return out << "??";
}

inline bool compare(const std::pair<mpq, var_index> & a, const std::pair<mpq, var_index> & b) {
    return a.second < b.second;
}

class ul_pair {
    constraint_index m_lower_bound_witness;
    constraint_index m_upper_bound_witness;
    bool             m_associated_with_row;  
public:
    constraint_index& lower_bound_witness() {return m_lower_bound_witness;}
    constraint_index lower_bound_witness() const {return m_lower_bound_witness;}
    constraint_index& upper_bound_witness() { return m_upper_bound_witness;}
    constraint_index upper_bound_witness() const {return m_upper_bound_witness;}
    bool operator!=(const ul_pair & p) const {
        return !(*this == p);
    }

    bool operator==(const ul_pair & p) const {
        return m_lower_bound_witness == p.m_lower_bound_witness
            && m_upper_bound_witness == p.m_upper_bound_witness &&
            m_associated_with_row == p.m_associated_with_row;
    }
    // empty constructor
    ul_pair() :
        m_lower_bound_witness(UINT_MAX),
        m_upper_bound_witness(UINT_MAX),
        m_associated_with_row(false) {}

    ul_pair(bool associated_with_row) :
        m_lower_bound_witness(UINT_MAX),
        m_upper_bound_witness(UINT_MAX),
        m_associated_with_row(associated_with_row) {}

    bool associated_with_row() const { return m_associated_with_row; }
};

}
