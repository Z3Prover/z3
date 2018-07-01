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
#include "util/lp/lp_primal_simplex_def.h"
template bool lp::lp_primal_simplex<double, double>::bounds_hold(std::unordered_map<std::string, double, std::hash<std::string>, std::equal_to<std::string>, std::allocator<std::pair<std::string const, double> > > const&);
template bool lp::lp_primal_simplex<double, double>::row_constraints_hold(std::unordered_map<std::string, double, std::hash<std::string>, std::equal_to<std::string>, std::allocator<std::pair<std::string const, double> > > const&);
template double lp::lp_primal_simplex<double, double>::get_current_cost() const;
template double lp::lp_primal_simplex<double, double>::get_column_value(unsigned int) const;
template lp::lp_primal_simplex<double, double>::~lp_primal_simplex();
template lp::lp_primal_simplex<lp::mpq, lp::mpq>::~lp_primal_simplex();
template lp::mpq lp::lp_primal_simplex<lp::mpq, lp::mpq>::get_current_cost() const;
template lp::mpq lp::lp_primal_simplex<lp::mpq, lp::mpq>::get_column_value(unsigned int) const;
template void lp::lp_primal_simplex<double, double>::find_maximal_solution();
template void lp::lp_primal_simplex<lp::mpq, lp::mpq>::find_maximal_solution();
