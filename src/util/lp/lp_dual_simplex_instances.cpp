/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/lp_dual_simplex.hpp"
template lean::mpq lean::lp_dual_simplex<lean::mpq, lean::mpq>::get_current_cost() const;
template void lean::lp_dual_simplex<lean::mpq, lean::mpq>::find_maximal_solution();
template double lean::lp_dual_simplex<double, double>::get_current_cost() const;
template void lean::lp_dual_simplex<double, double>::find_maximal_solution();
