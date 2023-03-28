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
#include "math/lp/lar_solver.h"
#include "math/lp/lp_primal_core_solver_def.h"
#include "math/lp/lp_primal_core_solver_tableau_def.h"
namespace lp {

template void lp::lp_primal_core_solver<lp::mpq, lp::numeric_pair<lp::mpq> >::find_feasible_solution();

template unsigned lp_primal_core_solver<mpq, mpq>::solve();
template unsigned lp_primal_core_solver<mpq, numeric_pair<mpq> >::solve();
template bool lp::lp_primal_core_solver<lp::mpq, lp::mpq>::update_basis_and_x_tableau(int, int, lp::mpq const&);
template bool lp::lp_primal_core_solver<lp::mpq, lp::numeric_pair<lp::mpq> >::update_basis_and_x_tableau(int, int, lp::numeric_pair<lp::mpq> const&);

}
