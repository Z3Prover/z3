/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Simplification

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-12

--*/
#pragma once
#include "math/polysat/constraint.h"

namespace polysat {

    class solver;

    class simplify {
        solver& s;

    public:
        simplify(solver& s);

        bool should_apply() const;

        void operator()();
    };

}
