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

    bool ve_reduction::perform(solver& s, pvar v, conflict_core& core) {
        // without any further hints, we just do core reduction with the stronger premise "C contains a c' that evaluates to false",
        // and kick out all other constraints.
        auto pred = [&s, v](signed_constraint c) -> bool {
            return !c->contains_var(v) && c.is_currently_false(s);
        };
        auto it = std::find_if(core.begin(), core.end(), pred);
        if (it != core.end()) {
            signed_constraint c = *it;
            core.reset();
            core.set(c);
            // core.insert(c);
            // core.set_needs_model(true);
            return true;
        }
        return false;
    }

    bool ve_forbidden_intervals::perform(solver& s, pvar v, conflict_core& core) {
        NOT_IMPLEMENTED_YET();
        return false;
    }

}
