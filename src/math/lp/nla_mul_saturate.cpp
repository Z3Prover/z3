/*++
  Copyright (c) 2025 Microsoft Corporation

  given a monic m = x * y * z ... with evaluation val(m) != val(x) * val(y) * val(z) ...

  saturate constraints with respect to m
  in other words, if a constraint contains x*y + p >= 0, 
  then include the constraint z >= 0 => x*y*z + z*p >= 0
  assuming current value of z is non-negative.
  Check if the system with new constraints is LP feasible.
  If it is not, then produce a lemma that explains the infeasibility.

  Strategy 1: The lemma is in terms of the original constraints and bounds.
  Strategy 2: Attempt to eliminate new monomials from the lemma by relying on Farkas multipliers.
              If it succeeds to eliminate new monomials we have a lemma that is a linear 
              combination of existing variables. 
  Strategy 3: The lemma uses the new constraints.

  --*/

#include "math/lp/nla_core.h"
#include "math/lp/nla_mul_saturate.h"


namespace nla {

    mul_saturate::mul_saturate(core* core) : 
        common(core) {}

    lbool mul_saturate::saturate() {
        lp::explanation ex;
        init_solver();
        add_multiply_constraints();
        lbool r = solve(ex);
        if (r == l_false)
            add_lemma(ex);
        return r;
    }

    void mul_saturate::init_solver() {
        local_solver = alloc(lp::lar_solver);
    }

    void mul_saturate::add_lemma(lp::explanation const& ex1) {
        lp::explanation ex2;
        for (auto p : ex1) {
            lp::constraint_index src_ci;
            if (m_new_mul_constraints.find(p.ci(), src_ci))
                ex2.add_pair(src_ci, mpq(1));
            else
                ex2.add_pair(p.ci(), p.coeff());
        }
        lemma_builder new_lemma(c(), "stellensatz");
        new_lemma &= ex2;
        for (auto [v, sign] : m_var_signs) {
            if (sign)
                new_lemma.explain_existing_upper_bound(v);
            else
                new_lemma.explain_existing_lower_bound(v);
        }
        IF_VERBOSE(1, verbose_stream() << "unsat \n" << new_lemma << "\n");
    }

    lbool mul_saturate::solve(lp::explanation& ex) {
        for (auto const& [new_ci, old_ci] : m_new_mul_constraints)
            local_solver->activate(new_ci);
        auto st = local_solver->solve();
        lbool r = l_undef;
        if (st == lp::lp_status::INFEASIBLE) {
            local_solver->get_infeasibility_explanation(ex);
            IF_VERBOSE(0, c().print_explanation(ex, verbose_stream()) << "\n";);
            r = l_false;
        }
        if (st == lp::lp_status::OPTIMAL || st == lp::lp_status::FEASIBLE) {
            // TODO: check model just in case it got lucky.
            IF_VERBOSE(1, verbose_stream() << "saturation is LP feasible, maybe it is a model of the NLA problem\n");
        }
        IF_VERBOSE(0, local_solver->display(verbose_stream()); c().display(verbose_stream()));
        return r;
    }

    // record new monomials that are created and recursively down-saturate with respect to these.
    void mul_saturate::add_multiply_constraints() {
        m_new_mul_constraints.reset();
        m_seen_vars.reset();
        m_var_signs.reset();
        for (auto j : c().m_to_refine) {
            for (auto con_id : local_solver->constraints().indices()) {
                unsigned num_vars = c().emon(j).vars().size();
                for (unsigned i = 0; i < num_vars; ++i) {
                    auto v = c().emon(j).vars()[i];
                    for (auto [coeff, u] : local_solver->constraints()[con_id].coeffs())
                        if (u == v)
                            add_multiply_constraint(con_id, j, v);
                }
            }
        }
    }

    // multiply by remaining vars
    void mul_saturate::add_multiply_constraint(lp::constraint_index old_ci, lp::lpvar mi, lpvar x) {
        lp::lar_base_constraint const& con = local_solver->constraints()[old_ci];
        auto const& lhs = con.coeffs();
        auto const& rhs = con.rhs();
        auto k = con.kind();        
        if (k == lp::lconstraint_kind::NE || k == lp::lconstraint_kind::EQ)
            return;  // not supported
        auto sign = false;
        svector<lpvar> vars;
        bool first = true;
        for (auto v : c().emon(mi).vars()) {
            if (v != x || !first) 
                vars.push_back(v);            
            else
                first = false;
        }
        // compute sign of vars
        for (auto v : vars) {
            if (m_seen_vars.contains(v))
                continue;
            // retrieve bounds of v
            // if v has non-negative lower bound add as positive
            // if v has non-positive upper bound add as negative
            // otherwise, fail
            if (local_solver->column_has_lower_bound(v) && !local_solver->get_lower_bound(v).is_neg()) {
                m_var_signs.push_back({v, false});
                m_seen_vars.insert(v);
            } 
            else if (local_solver->column_has_upper_bound(v) && !local_solver->get_upper_bound(v).is_pos()) {
                m_var_signs.push_back({v, true});
                m_seen_vars.insert(v);
                sign = !sign;
            }
            else 
                return;
        }
        lp::lar_term new_lhs;        
        rational new_rhs(rhs);
        for (auto [coeff, v] : lhs) {
            #if 0
            vars.push_back(v);
            lpvar new_monic_var = c().m_add_monomial(vars);
            auto const& new_m = c().emons()[new_monic_var];            
            verbose_stream() << vars << " v " << new_m.var() << " coeff " << coeff << "\n";
            new_lhs.add_monomial(coeff, new_m.var());
            vars.pop_back();
            #endif
        }
        if (rhs != 0) {
            if (vars.size() == 1) {
                new_lhs.add_monomial(-rhs, vars[0]);
                verbose_stream() << "rhs mul " << -rhs << " * j" << vars[0] << "\n";
            } 
            else {
#if 0
                lpvar new_monic_var = c().m_add_monomial(vars);
                auto const& new_m = c().emons()[new_monic_var];
                verbose_stream() << vars << " v " << new_m.var() << " coeff " << coeff << "\n";
                new_lhs.add_monomial(-rhs, new_m.var());
                verbose_stream() << "rhs mul " << -rhs << " * j" << new_m.var() << "\n";
#endif
            }
            new_rhs = 0;
        }

        if (sign) {
            switch (k) {
            case lp::lconstraint_kind::LE: k = lp::lconstraint_kind::GE; break;
            case lp::lconstraint_kind::LT: k = lp::lconstraint_kind::GT; break;
            case lp::lconstraint_kind::GE: k = lp::lconstraint_kind::LE; break;
            case lp::lconstraint_kind::GT: k = lp::lconstraint_kind::LT; break;
            default: break;
            }
        }   
        c().display_constraint(verbose_stream(), old_ci) << " -> ";
        c().display_constraint(verbose_stream(), new_lhs, k, new_rhs) << "\n";
        // TODO: 
        // auto new_ci = lra.m_add_constraint(new_lhs, k, new_rhs);
        // m_new_mul_constraints.insert(new_ci, old_ci);        
    }
}
