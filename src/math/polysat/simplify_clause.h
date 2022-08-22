/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Clause Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2022-08-22

--*/
#pragma once
#include "math/polysat/constraint.h"

namespace polysat {

    class solver;

    class simplify_clause {
        solver& s;

    public:
        simplify_clause(solver& s);

        bool apply(clause& cl);
    };

}
