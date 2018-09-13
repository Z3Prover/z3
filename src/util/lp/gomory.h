/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "util/lp/lar_term.h"
#include "util/lp/lia_move.h"
#include "util/lp/explanation.h"

namespace lp {
class gomory {
    lar_term   &          m_t; // the term to return in the cut
    mpq        &          m_k; // the right side of the cut
    explanation&          m_ex; // the conflict explanation
    bool       &          m_upper; // we have a cut m_t*x <= k if m_upper is true nad m_t*x >= k otherwise
    unsigned              m_basic_inf_int_j; // a basis column which has to be an integer but has a not integral value
    const row_strip<mpq>& m_row
public :
    gomory(lar_term   &         m_t,
           mpq        &         m_k,
           explanation&         m_ex,
           bool       &         m_upper, 
           unsigned             m_basic_inf_int_j ) :
        m_t(t),
        m_k(k),
        m_ex(ex),
        m_upper(upper), 
        m_basic_inf_int_j(j) {
    }
};
}
