/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Extract fixed bits of variables from univariate constraints

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner), Clemens Eisenhofer 2022-08-22

--*/
#pragma once
#include "sat/smt/polysat/types.h"
#include "sat/smt/polysat/constraints.h"
#include "sat/smt/polysat/forbidden_intervals.h"
#include "util/vector.h"

namespace polysat {

    class core;

    class fixed_bits {
        core& c;
        pvar m_var = null_var;
        fixed_bits_vector m_fixed_slices;
    public:
        fixed_bits(core& c) : c(c) {}

        // reset without variable reference.
        void reset();

        // reset with fixed bits information for variable v
        void init(pvar v);

        bool check(rational const& val, fi_record& fi);

        std::ostream& display(std::ostream& out) const;
    };
}
