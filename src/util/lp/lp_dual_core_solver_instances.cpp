/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include "util/vector.h"
#include <functional>
#include "util/lp/lp_dual_core_solver.hpp"
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::start_with_initial_basis_and_make_it_dual_feasible();
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::solve();
template lean::lp_dual_core_solver<double, double>::lp_dual_core_solver(lean::static_matrix<double, double>&, vector<bool>&,
                                                                        vector<double>&,
                                                                        vector<double>&,
                                                                        vector<unsigned int>&,
                                                                        vector<unsigned> &,
                                                                        vector<int> &,
                                                                        vector<double>&,
                                                                        vector<lean::column_type>&,
                                                                        vector<double>&,
                                                                        vector<double>&,
                                                                        lean::lp_settings&, const lean::column_namer&);
template void lean::lp_dual_core_solver<double, double>::start_with_initial_basis_and_make_it_dual_feasible();
template void lean::lp_dual_core_solver<double, double>::solve();
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::restore_non_basis();
template void lean::lp_dual_core_solver<double, double>::restore_non_basis();
template void lean::lp_dual_core_solver<double, double>::revert_to_previous_basis();
template void lean::lp_dual_core_solver<lean::mpq, lean::mpq>::revert_to_previous_basis();
