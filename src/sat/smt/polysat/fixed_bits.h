/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    Extract fixed bits of variables from univariate constraints

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner), Clemens Eisenhofer 2022-08-22

--*/
#pragma once
#include "sat/smt/polysat/polysat_types.h"
#include "sat/smt/polysat/polysat_constraints.h"
#include "util/vector.h"

namespace polysat {

    using fixed_bits_vector = vector<fixed_bits>;

    bool get_eq_fixed_lsb(pdd const& p, fixed_bits& out);
    bool get_eq_fixed_bits(pdd const& p, fixed_bits& out);

    bool get_ule_fixed_lsb(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_ule_fixed_msb(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_ule_fixed_bit(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_ule_fixed_bits(pdd const& lhs, pdd const& rhs, bool is_positive, fixed_bits& out);
    bool get_fixed_bits(signed_constraint c, fixed_bits& out);

}
