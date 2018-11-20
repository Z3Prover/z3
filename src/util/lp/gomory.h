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
#include "util/lp/static_matrix.h"

namespace lp {
class int_solver;
class gomory {
    class imp;
    imp                  *m_imp;
public :
    gomory(lar_term & t, mpq & k, explanation& ex, unsigned basic_inf_int_j, const row_strip<mpq>& row, const int_solver& s);
    lia_move create_cut();
    ~gomory();
};
}
