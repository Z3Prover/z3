/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat variable elimination

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "math/polysat/types.h"
#include "math/polysat/constraint.h"

namespace polysat {

    class conflict;

    class free_variable_elimination {
        solver& s;
        void find_lemma(pvar v, conflict& core);
        void find_lemma(pvar v, signed_constraint c, conflict& core);
        pdd eval(pdd const& p, conflict& core, assignment_t& out_assignment);
        bool inv(pdd const& p, pdd& out_p_inv);
    public:
        free_variable_elimination(solver& s): s(s) {}
        void find_lemma(conflict& core);
    };

}
