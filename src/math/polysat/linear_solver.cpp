/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    linear_solver.cpp
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-05-14
    Jakob Rath 2021-05-14

--*/

#include "math/polysat/linear_solver.h"
#include "math/polysat/solver.h"

namespace polysat {

    void linear_solver::push() {}
    void linear_solver::pop(unsigned n) {}
    void linear_solver::new_constraint(constraint& c) {}
    void linear_solver::set_value(pvar v, rational const& value) {}
    void linear_solver::set_bound(pvar v, rational const& lo, rational const& hi) {}
    void linear_solver::activate_constraint(constraint& c) {}
    
    // check integer modular feasibility under current bounds.
    lbool linear_solver::check() { return l_undef; }
    void linear_solver::unsat_core(unsigned_vector& deps) {}

    // current value assigned to (linear) variable according to tableau.
    rational linear_solver::value(pvar v) { return rational(0); }
    
};

