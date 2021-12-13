/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Restart

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-12

--*/
#pragma once
#include "math/polysat/constraint.h"

namespace polysat {

    class solver;

    class restart {
        solver& s;
        unsigned m_conflicts_at_restart = 0;
        unsigned m_restart_threshold = 100;
        unsigned m_restart_init = 100;
        unsigned m_luby_idx = 0;

    public:
        restart(solver& s);

        bool should_apply() const;

        void operator()();
    };

}
