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

class lar_term; // forward definition
class column {
    u_dependency* m_lower_bound_witness = nullptr;
    u_dependency* m_upper_bound_witness = nullptr;
    lar_term*     m_term = nullptr;
public:
    lar_term*  term() const { return m_term; }
 
    u_dependency*& lower_bound_witness() { return m_lower_bound_witness; }
    u_dependency* lower_bound_witness() const { return m_lower_bound_witness; }
    u_dependency*& upper_bound_witness() { return m_upper_bound_witness; }
    u_dependency* upper_bound_witness() const { return m_upper_bound_witness; }

    column() {}

    column(lar_term* term) : m_term(term) {}

    bool associated_with_row() const { return m_term != nullptr; }
};

}
