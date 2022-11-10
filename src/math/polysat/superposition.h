/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation by polynomial superposition

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/conflict.h"
#include "math/polysat/constraint.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/interval.h"

namespace polysat {

    class solver;

    class ex_polynomial_superposition {
        solver& s;

        signed_constraint resolve1(pvar v, signed_constraint c1, signed_constraint c2);
        lbool find_replacement(signed_constraint c2, pvar v, conflict& core);
        void reduce_by(pvar v, conflict& core);
        bool reduce_by(pvar, signed_constraint c, conflict& core);
        lbool try_explain1(pvar v, conflict& core);

    public:
        ex_polynomial_superposition(solver& s) : s(s) {}
        bool perform(pvar v, conflict& core);
    };

}
