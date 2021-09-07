/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Polysat variable elimination

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/conflict_core.h"

namespace polysat {

    class solver;

    class variable_elimination_engine {
    public:
        virtual ~variable_elimination_engine() {}
        virtual bool perform(solver& s, pvar v, conflict_core& core) = 0;
    };

    class ve_reduction : public variable_elimination_engine {
    public:
        bool perform(solver& s, pvar v, conflict_core& core) override;
    };

}
