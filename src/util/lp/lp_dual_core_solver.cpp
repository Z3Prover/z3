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
#include <utility>
#include <memory>
#include <string>
#include "util/vector.h"
#include <functional>
#include "util/lp/lp_dual_core_solver_def.h"
template void lp::lp_dual_core_solver<lp::mpq, lp::mpq>::start_with_initial_basis_and_make_it_dual_feasible();
template void lp::lp_dual_core_solver<lp::mpq, lp::mpq>::solve();
template lp::lp_dual_core_solver<double, double>::lp_dual_core_solver(lp::static_matrix<double, double>&, vector<bool>&,
                                                                        vector<double>&,
                                                                        vector<double>&,
                                                                        vector<unsigned int>&,
                                                                        vector<unsigned> &,
                                                                        vector<int> &,
                                                                        vector<double>&,
                                                                        vector<lp::column_type>&,
                                                                        vector<double>&,
                                                                        vector<double>&,
                                                                        lp::lp_settings&, const lp::column_namer&);
template void lp::lp_dual_core_solver<double, double>::start_with_initial_basis_and_make_it_dual_feasible();
template void lp::lp_dual_core_solver<double, double>::solve();
template void lp::lp_dual_core_solver<lp::mpq, lp::mpq>::restore_non_basis();
template void lp::lp_dual_core_solver<double, double>::restore_non_basis();
template void lp::lp_dual_core_solver<double, double>::revert_to_previous_basis();
template void lp::lp_dual_core_solver<lp::mpq, lp::mpq>::revert_to_previous_basis();
