/*++
Copyright (c) 2017 Microsoft Corporation

Abstract:

    justifications for upper or lower bounds

Author:

    Lev Nachmanson (levnach)

--*/

#pragma once
#include "util/vector.h"
#include "util/dependency.h"
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

class column {
    u_dependency* m_lower_bound_witness = nullptr;
    u_dependency* m_upper_bound_witness = nullptr;
    bool          m_associated_with_row = false;  
    lpvar         m_j; //the column index
    lar_term*     m_term = nullptr;
public:
    lar_term*  term() const { return m_term; }
    lar_term*& term() { return m_term; } // for setting m_term
    lpvar      j() const { return m_j; } //the column index

    u_dependency*& lower_bound_witness() { return m_lower_bound_witness; }
    u_dependency* lower_bound_witness() const { return m_lower_bound_witness; }
    u_dependency*& upper_bound_witness() { return m_upper_bound_witness; }
    u_dependency* upper_bound_witness() const { return m_upper_bound_witness; }

    // equality is used by stackedvector operations.
    // this appears to be a low level reason
    
    bool operator!=(const column & p) const {
        return !(*this == p);
    }

    bool operator==(const column & p) const {
        return m_lower_bound_witness == p.m_lower_bound_witness
            && m_upper_bound_witness == p.m_upper_bound_witness 
            && m_associated_with_row == p.m_associated_with_row;
    }
    column()  = delete;
    column(bool) = delete;

    column(lar_term* term): m_term(term) {}

    column(lpvar j, bool associated_with_row) :
        m_associated_with_row(associated_with_row), m_j(j) {}

    bool associated_with_row() const { return m_associated_with_row; }
};

}