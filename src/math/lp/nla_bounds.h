
/*++
  Copyright (c) 2025 Microsoft Corporation

  Module Name:

  nla_bounds.h

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

  Abstract:
     Create bounds for variables that occur in non-linear monomials.
     The bounds should ensure that variables are either fixes at -1, 0, 1, below or above these values.
     This ensures that basic lemmas that case split on values -1, 0, 1 are robust under model changes.

--*/
#pragma once

#include "math/lp/nla_common.h"


namespace nla {
    class core;

    class bounds : common {

        bool add_bounds_to_free_variable(monic const& m, lp::lpvar j);
        bool add_bounds_to_variable_at_value(lp::lpvar j, int i);
    public:
        bounds(core *core);
        void operator()();
    
    };

}  // namespace nla
