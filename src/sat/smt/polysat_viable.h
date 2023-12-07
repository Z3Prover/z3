/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains
    It uses the interval extraction functions from forbidden intervals.
    An empty viable set corresponds directly to a conflict that does not rely on
    the non-viable variable.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "util/rational.h"
#include "sat/smt/polysat_types.h"

namespace polysat {

    enum class find_t {
        empty,
        singleton,
        multiple,
        resource_out,
    };

    class core;

    class viable {
        core& c;
    public:
        viable(core& c) : c(c) {}

	    /**
         * Find a next viable value for variable.
         */
        find_t find_viable(pvar v, rational& out_val) { throw default_exception("nyi"); }

        /*
        * Explain why the current variable is not viable or signleton.
        */
        dependency_vector explain() { throw default_exception("nyi"); }

        /*
        * Register constraint at index 'idx' as unitary in v.
        */
        void add_unitary(pvar v, unsigned idx) { throw default_exception("nyi"); }

    };

}
