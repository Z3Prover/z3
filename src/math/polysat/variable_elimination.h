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

    class variable_elimination_engine {
    public:
        virtual ~variable_elimination_engine() {}
        virtual bool perform(pvar v, conflict_core& core) = 0;
    };

    // discovers when a variable has already been removed... (special case of ve_reduction?)
    class ve_trivial final : public variable_elimination_engine {
    public:
        bool perform(pvar v, conflict_core& core) override { NOT_IMPLEMENTED_YET(); return false; }
    };

    // ve by core reduction: try core reduction on all constraints that contain the variable to be eliminated.
    // if we cannot eliminate all such constraints, then should we keep all of them instead of eliminating only some? since they might still be useful for saturation.
    class ve_reduction final : public variable_elimination_engine {
    public:
        bool perform(pvar v, conflict_core& core) override { NOT_IMPLEMENTED_YET(); return false; }
    };

    class ve_forbidden_intervals final : public variable_elimination_engine {
    public:
        bool perform(pvar v, conflict_core& core) override { NOT_IMPLEMENTED_YET(); return false; }
    };

    class variable_elimination final {
        scoped_ptr_vector<variable_elimination_engine> ve_engines;

    public:
        variable_elimination() {}

        /// Try to eliminate the variable v from the given core
        bool perform(pvar v, conflict_core& core) { NOT_IMPLEMENTED_YET(); return false; }
    };
}
