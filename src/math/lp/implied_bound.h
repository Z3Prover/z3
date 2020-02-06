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
#include "math/lp/lp_settings.h"
#include "math/lp/lar_constraints.h"
namespace lp {
struct implied_bound {
    mpq m_bound;
    unsigned m_j; // the column for which the bound has been found
    bool m_is_lower_bound;
    bool m_coeff_before_j_is_pos;
    unsigned m_row_or_term_index;
    bool m_strict;
    lconstraint_kind kind() const {
        lconstraint_kind k = m_is_lower_bound? GE : LE;
        if (m_strict)
            k = static_cast<lconstraint_kind>(k / 2);
        return k;
    }
    bool operator==(const implied_bound & o) const {
        return m_j == o.m_j && m_is_lower_bound == o.m_is_lower_bound && m_bound == o.m_bound &&
            m_coeff_before_j_is_pos == o.m_coeff_before_j_is_pos &&
            m_row_or_term_index == o.m_row_or_term_index && m_strict == o.m_strict;
    }
    implied_bound(){}
    implied_bound(const mpq & a,
                  unsigned j,
                  bool lower_bound,
                  bool coeff_before_j_is_pos,
                  unsigned row_or_term_index,
                  bool strict):
        m_bound(a),
        m_j(j),
        m_is_lower_bound(lower_bound),
        m_coeff_before_j_is_pos(coeff_before_j_is_pos),
        m_row_or_term_index(row_or_term_index),
        m_strict(strict) {
    }
};
}
