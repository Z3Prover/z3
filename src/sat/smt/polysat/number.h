/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat numbers

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "sat/smt/polysat/types.h"

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

    /** floor(a / 2^k) for a >= 0 */
    inline rational div2k_floor(rational const& a, unsigned k)
    {
        SASSERT(a >= 0);  // machine_div2k rounds towards 0
        return machine_div2k(a, k);
    }

    /** ceil(a / 2^k) for a >= 0 */
    inline rational div2k_ceil(rational const& a, unsigned k)
    {
        // Note: ceil(a/b) == floor((a-1)/b) + 1 for integers a,b and b > 0
        // Special case for a = 0, because machine_div2k(a, k) does not return floor(a/2^k), but rounds towards 0 instead.
        if (a.is_zero())
            return a;
        SASSERT(a > 0);  // machine_div2k rounds towards 0
        return machine_div2k(a - 1, k) + 1;
    }

}
