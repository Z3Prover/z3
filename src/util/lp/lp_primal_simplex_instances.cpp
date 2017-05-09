/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <utility>
#include <memory>
#include <string>
#include "util/vector.h"
#include <functional>
#include "util/lp/lp_primal_simplex.hpp"
template bool lean::lp_primal_simplex<double, double>::bounds_hold(std::unordered_map<std::string, double, std::hash<std::string>, std::equal_to<std::string>, std::allocator<std::pair<std::string const, double> > > const&);
template bool lean::lp_primal_simplex<double, double>::row_constraints_hold(std::unordered_map<std::string, double, std::hash<std::string>, std::equal_to<std::string>, std::allocator<std::pair<std::string const, double> > > const&);
template double lean::lp_primal_simplex<double, double>::get_current_cost() const;
template double lean::lp_primal_simplex<double, double>::get_column_value(unsigned int) const;
template lean::lp_primal_simplex<double, double>::~lp_primal_simplex();
template lean::lp_primal_simplex<lean::mpq, lean::mpq>::~lp_primal_simplex();
template lean::mpq lean::lp_primal_simplex<lean::mpq, lean::mpq>::get_current_cost() const;
template lean::mpq lean::lp_primal_simplex<lean::mpq, lean::mpq>::get_column_value(unsigned int) const;
template void lean::lp_primal_simplex<double, double>::find_maximal_solution();
template void lean::lp_primal_simplex<lean::mpq, lean::mpq>::find_maximal_solution();
