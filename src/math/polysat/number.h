/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat numbers

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "math/polysat/types.h"

namespace polysat {

    inline unsigned get_parity(rational const& val, unsigned num_bits) {
        if (val.is_zero())
            return num_bits;
        return val.trailing_zeros();
    };

    /** Return val with the lower k bits set to zero. */
    inline rational clear_lower_bits(rational const& val, unsigned k) {
        return val - mod(val, rational::power_of_two(k));
    }

}
