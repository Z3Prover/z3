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
                        if (u == v) 
                            // multiply by remaining vars
                            multiply_constraint(con, m, v);
                            // add new constraint
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

    // multiply by remaining vars
    void mul_saturate::multiply_constraint(lp::lar_base_constraint const& con, monic const& m, lpvar x) {
        auto const& lhs = con.coeffs();
        auto const& rhs = con.rhs();
        auto k = con.kind();
        auto sign = false;
        svector<lpvar> vars;
        bool first = true;
        for (auto v : m.vars()) {
            if (v != x || !first)
                vars.push_back(v);
            else
                first = false;
        }
        vector<std::pair<rational, lpvar>> new_lhs;
        rational new_rhs(rhs);
        for (auto [coeff, v] : lhs) {
            vars.push_back(v);

            auto new_m = c().emons().find_canonical(vars);
            if (!new_m) {
                bool is_int = lra.var_is_int(x);  // assume all vars in monic have the same type, can be changed for MIP
                lpvar new_monic_var = 0; // lra.add_var(is_int);
                c().emons().add(new_monic_var, vars);
                new_m = c().emons().find_canonical(vars);
                SASSERT(new_m);
            }
            new_lhs.push_back({coeff, new_m->var()});
            vars.pop_back();
        }
        if (rhs != 0) {
            new_lhs.push_back({-rhs, m.var()});
            new_rhs = 0;
        }
        // compute sign of vars
        for (auto v : vars) 
            if (c().val(v).is_neg())
                sign = !sign;
        if (sign) {
            switch (k) {
            case lp::lconstraint_kind::LE: k = lp::lconstraint_kind::GE; break;
            case lp::lconstraint_kind::LT: k = lp::lconstraint_kind::GT; break;
            case lp::lconstraint_kind::GE: k = lp::lconstraint_kind::LE; break;
            case lp::lconstraint_kind::GT: k = lp::lconstraint_kind::LT; break;
            default: break;
            }
        }
        // instead of adding a constraint here, add row to tableau based on the new_lhs, new_rhs, k.
    }
}
