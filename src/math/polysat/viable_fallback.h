/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    viable_fallback to univariate solvers
    (bit-blasting or int-blasting over a single variable)

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "math/polysat/viable.h"

namespace polysat {

    class viable_fallback {
        friend class viable;

        solver& s;

        scoped_ptr<univariate_solver_factory>   m_usolver_factory;
        u_map<scoped_ptr<univariate_solver>>    m_usolver;  // univariate solver for each bit width
        vector<signed_constraints>              m_constraints;
        svector<unsigned>                       m_constraints_trail;

        univariate_solver* usolver(unsigned bit_width);

    public:
        viable_fallback(solver& s);

        // declare and remove var
        void push_var(unsigned bit_width);
        void pop_var();

        // add/remove constraints stored in the fallback solver
        void push_constraint(pvar v, signed_constraint const& c);
        void pop_constraint();

        // Check whether all constraints for 'v' are satisfied;
        // or find an arbitrary violated constraint.
        bool check_constraints(assignment const& a, pvar v) { return !find_violated_constraint(a, v); }
        signed_constraint find_violated_constraint(assignment const& a, pvar v);
    };

}
