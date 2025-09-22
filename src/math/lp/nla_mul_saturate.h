/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

namespace nla {

    class core;
    class lar_solver;
    class mul_saturate : common {
        lp::lar_solver& lra;
        lp::lar_base_constraint* multiply_constraint(lp::lar_base_constraint const& c, monic const& m, lpvar x);
    public:
        mul_saturate(core* core);

        lbool saturate();
    };

}
