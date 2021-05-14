/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    linear_solver.h

Abstract:

    Fixed-precision unsigned integer linear solver

    This wraps around fixplex and translates polynomials
    into linear form.
    Equalities, Inequalities are converted into rows and slack variables.
    Slack variables are bounded when constraints are activated.
    It also handles backtracking state: bounds that are activated inside one 
    scope are de-activated when exiting the scope.
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-05-14
    Jakob Rath 2021-05-14

--*/

#pragma once

#include "math/polysat/fixplex.h"
#include "math/polysat/constraint.h"
#include "math/polysat/eq_constraint.h"
#include "math/polysat/ule_constraint.h"

namespace polysat {

    class linear_solver {
        reslimit&                m_lim;
        ptr_vector<fixplex_base> m_fix;
        unsigned_vector          m_var2ext;
        unsigned_vector          m_ext2var;
        
        //
        // TBD trail object for 
        // removing variables
        // undoing variable bounds bounds
        // removing rows from fixplex
        //
    public:
        linear_solver(reslimit& lim):
            m_lim(lim)
        {}

        void push();
        void pop(unsigned n); 
        void internalize_constraint(constraint& c);
        void set_value(pvar v, rational const& value);
        void set_bound(pvar v, rational const& lo, rational const& hi);
        void activate_constraint(constraint& c);

        // check integer modular feasibility under current bounds.
        lbool check();
        void unsat_core(unsigned_vector& deps);

        // current value assigned to (linear) variable according to tableau.
        rational value(pvar v);

        std::ostream& display(std::ostream& out) const { return out; }
        void collect_statistics(::statistics & st) const {}

    };



};

