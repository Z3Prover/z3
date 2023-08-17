/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Extract fixed bits of variables from univariate constraints

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner), Clemens Eisenhofer 2022-08-22

--*/
#pragma once
#include "math/polysat/types.h"
#include "math/polysat/constraint.h"
#include "util/vector.h"

namespace polysat {

    struct fixed_bits {
        unsigned hi = 0;
        unsigned lo = 0;
        rational value;

        /// The constraint is equivalent to setting fixed bits on a variable.
        // bool is_equivalent;

        fixed_bits() = default;
        fixed_bits(unsigned hi, unsigned lo, rational value): hi(hi), lo(lo), value(value) {}
    };

    using fixed_bits_vector = vector<fixed_bits>;

    bool get_eq_fixed_lsb(pdd const& p, fixed_bits& out);
    bool get_eq_fixed_bits(pdd const& p, fixed_bits& out);

    bool get_ule_fixed_lsb(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_ule_fixed_msb(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_ule_fixed_bit(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_ule_fixed_bits(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_fixed_bits(signed_constraint c, fixed_bits& out);

}
