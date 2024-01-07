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

    bool get_eq_fixed_lsb(pdd const& p, fixed_slice& out);
    bool get_eq_fixed_slice(pdd const& p, fixed_slice& out);

    bool get_ule_fixed_lsb(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_slice& out);
    bool get_ule_fixed_msb(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_slice& out);
    bool get_ule_fixed_bit(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_slice& out);
    bool get_ule_fixed_slice(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_slice& out);
    bool get_fixed_slice(signed_constraint c, fixed_slice& out);

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
