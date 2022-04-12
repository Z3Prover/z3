/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat variable elimination

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#include "math/polysat/variable_elimination.h"
#include "math/polysat/solver.h"
#include <algorithm>

namespace polysat {

    bool ve_reduction::perform(solver& s, pvar v, conflict& core) {
        // without any further hints, we just do core reduction with the stronger premise "C contains a c' that evaluates to false",
        // and kick out all other constraints.
        for (signed_constraint c : core) {
            if (!c->contains_var(v) && c.is_currently_false(s)) {
                core.reset();
                core.set(c);
                core.log_inference("ve_reduction");
                return true;
            }                
        }
        return false;
    }

}
