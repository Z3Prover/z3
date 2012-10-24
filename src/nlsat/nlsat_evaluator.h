/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_evaluator.h

Abstract:

    Helper class for computing the infeasible intervals of an
    arithmetic literal.

Author:

    Leonardo de Moura (leonardo) 2012-01-12.

Revision History:

--*/
#ifndef _NLSAT_EVALUATOR_H_
#define _NLSAT_EVALUATOR_H_

#include"nlsat_types.h"
#include"nlsat_assignment.h"
#include"nlsat_interval_set.h"

namespace nlsat {

    class evaluator {
        struct imp;
        imp *  m_imp;
    public:
        evaluator(assignment const & x2v, pmanager & pm, small_object_allocator & allocator);
        ~evaluator();

        interval_set_manager & ism() const;

        /**
           \brief Evaluate the given literal in the current model.
           All variables in the atom must be assigned.
           
           The result is true if the literal is satisfied, and false otherwise.
        */
        bool eval(atom * a, bool neg);
        
        /**
           \brief Return the infeasible interval set for the given literal.
           All but the a->max_var() must be assigned in the current model.

           Let x be a->max_var(). Then, the resultant set specifies which
           values of x falsify the given literal.
        */
        interval_set_ref infeasible_intervals(atom * a, bool neg);

        void push();
        void pop(unsigned num_scopes);
    };
    
};

#endif
