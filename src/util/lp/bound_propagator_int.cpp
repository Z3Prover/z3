/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/bound_propagator_int.hpp"
template lp::bound_propagator_int<rational>::bound_propagator_int(lp::cut_solver<rational>&);
template bool lp::bound_propagator_int<rational>::has_upper_bound(unsigned int) const;
template bool lp::bound_propagator_int<rational>::has_lower_bound(unsigned int) const;
template void lp::bound_analyzer_on_int_ineq<rational>::limit_j(unsigned int, rational const&, bool, bool);
template void lp::bound_propagator_int<rational>::add_bound(rational, unsigned int, bool, bool, unsigned int);
template bool lp::bound_propagator_int<rational>::get_upper_bound(unsigned int, rational&) const;
template bool lp::bound_propagator_int<rational>::get_lower_bound(unsigned int, rational&) const;

