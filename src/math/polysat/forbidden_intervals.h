/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Conflict explanation using forbidden intervals as described in
    "Solving bitvectors with MCSAT: explanations from bits and pieces"
    by S. Graham-Lengrand, D. Jovanovic, B. Dutertre.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/constraint.h"
#include "math/polysat/solver.h"
#include "math/polysat/variable_elimination.h"

namespace polysat {

    class forbidden_intervals : public variable_elimination_engine {
        void full_interval_conflict(signed_constraint c, signed_constraint neg_cond, conflict_core& core);
    public:
        bool perform(solver& s, pvar v, conflict_core& core) override;
    };
}
