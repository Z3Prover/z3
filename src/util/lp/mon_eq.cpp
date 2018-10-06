/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner
*/
#include "util/lp/lar_solver.h"
#include "util/lp/monomial.h"
namespace nla {
typedef monomial mon_eq;
bool check_assignment(mon_eq const& m, variable_map_type & vars) {
    rational r1 = vars[m.var()];
    if (r1.is_zero()) {
        for (auto w : m) {
            if (vars[w].is_zero())
                return true;
        }
        return false;
    }
    rational r2(1);
    for (auto w : m) {
        r2 *= vars[w];
    }
    return r1 == r2;
}

bool check_assignments(const vector<mon_eq> & monomials,
                       const lp::lar_solver& s,
                       variable_map_type & vars) {
    s.get_model(vars);
    for (auto const& m : monomials) {
        if (!check_assignment(m, vars)) return false;
    }
    return true;
}

}
