
/*++
  Copyright (c) 2025 Microsoft Corporation

  Module Name:

  nla_bounds.cpp

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/

#include "nla_bounds.h"
#include "nla_core.h"


namespace nla {

    bounds::bounds(core *c) : common(c) {}

    // looking for a free variable inside of a monic to split
    void bounds::operator()() {
        for (lpvar i : c().to_refine()) {
            auto const &m = c().emons()[i];
            for (lpvar j : m.vars()) {
                if (!c().var_is_free(j))
                    continue;
                if (m.is_bound_propagated())
                    continue;
                c().emons().set_bound_propagated(m);
                // split the free variable (j <= 0, or j > 0), and return
                auto i(ineq(j, lp::lconstraint_kind::LE, rational::zero()));
                c().add_literal(i);
                TRACE(nla_solver, c().print_ineq(i, tout) << "\n");
                ++c().lp_settings().stats().m_nla_add_bounds;
                return;
            }
        }
    }
}  // namespace nla
