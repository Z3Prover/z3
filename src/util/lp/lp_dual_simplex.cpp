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
#include "util/lp/lp_dual_simplex_def.h"
template lp::mpq lp::lp_dual_simplex<lp::mpq, lp::mpq>::get_current_cost() const;
template void lp::lp_dual_simplex<lp::mpq, lp::mpq>::find_maximal_solution();
template double lp::lp_dual_simplex<double, double>::get_current_cost() const;
template void lp::lp_dual_simplex<double, double>::find_maximal_solution();
