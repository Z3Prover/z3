/*++
  Copyright (c) 2025 Microsoft Corporation

  given a monic m = x * y * z ... with evaluation val(m) != val(x) * val(y) * val(z) ...

  saturate constraints with respect to m
  in other words, if a constraint contains x*y + p >= 0, 
  then include the constraint z >= 0 => x*y*z + z*p >= 0
  assuming current value of z is non-negative.
  Check if the system with new constraints is LP feasible.
  If it is not, then produce a lemma that explains the infeasibility.

  The lemma is in terms of the original constraints and bounds.

  --*/

#include "math/lp/nla_core.h"
#include "math/lp/nla_mul_saturate.h"


namespace nla {

    mul_saturate::mul_saturate(core* core) : 
        common(core), 
        lra(m_core.lra) {}

    lbool mul_saturate::saturate() {
        lra.push();
        for (auto j : c().m_to_refine) {
            auto& m = c().emons()[j];
            for (auto& con : lra.constraints().active()) {                
                for (auto v : m.vars()) {
                    for (auto [coeff, u] : con.coeffs()) {
                        if (u == v) {
                            // add new constraint
                            // multiply by remaining vars
                        }
                    }
                }
            }
        }       
        // record new monomials that are created and recursively down-saturate with respect to these.

        auto st = lra.solve();
        lbool r = l_undef;
        if (st == lp::lp_status::INFEASIBLE) {
            // now we need to filter new constraints into bounds and old constraints.

            r = l_false;
        }
        if (st == lp::lp_status::OPTIMAL || st == lp::lp_status::FEASIBLE) {
            // TODO: check model just in case it got lucky.           
        }
        lra.pop(1);
        return r;
    }

    lp::lar_base_constraint* mul_saturate::multiply_constraint(lp::lar_base_constraint const& c, monic const& m, lpvar x) {

        return nullptr;
    }
}
