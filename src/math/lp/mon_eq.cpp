/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner
*/
#include "math/lp/lar_solver.h"
#include "math/lp/monic.h"
namespace nla {

template <typename T>
bool check_assignment(T const& m, variable_map_type & vars) {
    rational r1 = vars[m.var()];
    if (r1.is_zero()) 
        return any_of(m.vars(), [&](auto w) { return vars[w].is_zero(); });    
    rational r2(1);
    for (auto w : m.vars()) 
        r2 *= vars[w];    
    return r1 == r2;
}

template <typename K>
bool check_assignments(const K & monomials,
                       const lp::lar_solver& s,
                       variable_map_type & vars) {
    s.get_model(vars);
    return all_of(monomials, [&](auto const& m) { return check_assignment(m, vars); });
}

template bool check_assignments<vector<mon_eq>>(const vector<mon_eq>&,
                                            const lp::lar_solver& s,
                                            variable_map_type & vars);

}
