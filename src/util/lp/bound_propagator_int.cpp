/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/bound_propagator_int.hpp"
template lp::bound_propagator_int<rational>::bound_propagator_int(lp::cut_solver<rational>&, unsigned);
template bool lp::bound_propagator_int<rational>::has_upper_bound(unsigned int) const;
template bool lp::bound_propagator_int<rational>::has_lower_bound(unsigned int) const;
template void lp::bound_analyzer_on_int_ineq<rational>::limit_j(unsigned int, rational const&, bool);
template void lp::bound_propagator_int<rational>::add_bound(rational, unsigned int, bool, unsigned int);
template bool lp::bound_propagator_int<rational>::get_upper_bound(unsigned int, rational&) const;
template bool lp::bound_propagator_int<rational>::get_lower_bound(unsigned int, rational&) const;
template void lp::bound_propagator_int<rational>::print_ineq(std::ofstream &, unsigned int) const;
template void lp::bound_propagator_int<rational>::print_var_domain(std::ofstream &, unsigned int) const;
template std::string lp::bound_propagator_int<rational>::var_name(unsigned j) const;


