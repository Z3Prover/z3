/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include "util/vector.h"
#include <functional>
#include "util/lp/lar_solver.h"
#include "util/lp/lp_primal_core_solver.hpp"
#include "util/lp/lp_primal_core_solver_tableau.hpp"
namespace lean {

template void lp_primal_core_solver<double, double>::find_feasible_solution();
template void lean::lp_primal_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::find_feasible_solution();

template unsigned lp_primal_core_solver<double, double>::solve();
template unsigned lp_primal_core_solver<double, double>::solve_with_tableau();
template unsigned lp_primal_core_solver<mpq, mpq>::solve();
template unsigned lp_primal_core_solver<mpq, numeric_pair<mpq> >::solve();
template void lean::lp_primal_core_solver<double, double>::clear_breakpoints();
template bool lean::lp_primal_core_solver<lean::mpq, lean::mpq>::update_basis_and_x_tableau(int, int, lean::mpq const&);
template bool lean::lp_primal_core_solver<double, double>::update_basis_and_x_tableau(int, int, double const&);
template bool lean::lp_primal_core_solver<lean::mpq, lean::numeric_pair<lean::mpq> >::update_basis_and_x_tableau(int, int, lean::numeric_pair<lean::mpq> const&);

}
