/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    helpers for refining intervals

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "math/polysat/types.h"

namespace polysat {

    namespace refine_equal {

        /**
         * Given a*y0 mod M \in [lo;hi], try to find the largest y_max >= y0 such that for all y \in [y0;y_max] . a*y mod M \in [lo;hi].
         * Result may not be optimal.
         * NOTE: upper bound is inclusive.
         */
        rational compute_y_max(rational const& y0, rational const& a, rational const& lo0, rational const& hi, rational const& M);

        /**
         * Given a*y0 mod M \in [lo;hi], try to find the smallest y_min <= y0 such that for all y \in [y_min;y0] . a*y mod M \in [lo;hi].
         * Result may not be optimal.
         * NOTE: upper bound is inclusive.
         */
        rational compute_y_min(rational const& y0, rational const& a, rational const& lo, rational const& hi, rational const& M);

        /**
         * Given a*y0 mod M \in [lo;hi],
         * find the largest interval [y_min;y_max] around y0 such that for all y \in [y_min;y_max] . a*y mod M \in [lo;hi].
         * Result may not be optimal.
         * NOTE: upper bounds are inclusive.
         */
        std::pair<rational, rational> compute_y_bounds(rational const& y0, rational const& a, rational const& lo, rational const& hi, rational const& M);

    }

}
