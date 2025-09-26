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
#include "math/lp/nla_coi.h"
#include "math/lp/nla_mul_saturate.h"


namespace nla {

    mul_saturate::mul_saturate(core* core) : common(core), m_coi(*core) {}

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
        m_vars2mon.reset();
        m_mon2vars.reset();
        m_values.reset();
        m_coi.init();
        init_vars();
    }

    void mul_saturate::init_vars() {
        auto const& lra = c().lra_solver();
        auto sz = lra.number_of_vars();
        for (unsigned v = 0; v < sz; ++v) {
            unsigned w;
            if (m_coi.mons().contains(v))
                init_monomial(v);
            else 
                m_values.push_back(c().val(v));
            if (m_coi.terms().contains(v)) {
                auto const& t = lra.get_term(v);
                // Assumption: variables in coefficients are always declared before term variable.
                SASSERT(all_of(t, [&](auto p) { return p.j() < v; }));
                w = local_solver->add_term(t.coeffs_as_vector(), v);
            } 
            else
                w = local_solver->add_var(v, lra.var_is_int(v));

            VERIFY(w == v);
            if (lra.column_has_lower_bound(v)) {
                auto lo_dep = lra.get_column_lower_bound_witness(v);
                auto lo_bound = lra.get_lower_bound(v);
                auto k = lo_bound.y > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                auto ci = local_solver->add_var_bound(v, k, lo_bound.x);
            }
            if (lra.column_has_upper_bound(v)) {
                auto hi_dep = lra.get_column_upper_bound_witness(v);
                auto hi_bound = lra.get_upper_bound(v);
                auto k = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto ci = local_solver->add_var_bound(v, k, hi_bound.x);
                m_ci2dep.setx(ci, hi_dep, nullptr);
            }
        }
    }

    void mul_saturate::init_monomial(unsigned mon_var) {
        auto& mon = c().emons()[mon_var];
        svector<lpvar> vars(mon.vars());
        std::sort(vars.begin(), vars.end());
        m_vars2mon.insert(vars, mon_var);
        m_mon2vars.insert(mon_var, vars);
        rational p(1);
        for (auto v : vars)
            p *= m_values[v];
        m_values.push_back(p);
    }

    void mul_saturate::add_lemma(lp::explanation const& ex1) {
        auto& lra = c().lra_solver();
        lp::explanation ex2;
        for (auto p : ex1) {
            lp::constraint_index src_ci;
            if (!m_new_mul_constraints.find(p.ci(), src_ci))
                src_ci = p.ci();
            auto dep = m_ci2dep.get(src_ci, nullptr);
            local_solver->push_explanation(dep, ex2);
        }
        for (auto [v, sign, dep] : m_var_signs) {            
            if (!dep) {
                verbose_stream() << "TODO explain non-implied bound\n";
                continue;
            }
            local_solver->push_explanation(dep, ex2);
        }
        lemma_builder new_lemma(c(), "stellensatz");
        new_lemma &= ex2;
        IF_VERBOSE(1, verbose_stream() << "unsat \n" << new_lemma << "\n");
        TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
    }

    lbool mul_saturate::solve(lp::explanation& ex) {
        for (auto const& [new_ci, old_ci] : m_new_mul_constraints)
            local_solver->activate(new_ci);
        auto st = local_solver->solve();
        lbool r = l_undef;
        if (st == lp::lp_status::INFEASIBLE) {
            local_solver->get_infeasibility_explanation(ex);
            r = l_false;
        }
        if (st == lp::lp_status::OPTIMAL || st == lp::lp_status::FEASIBLE) {
            // TODO: check model just in case it got lucky.
            IF_VERBOSE(1, verbose_stream() << "saturation is LP feasible, maybe it is a model of the NLA problem\n");
        }
        IF_VERBOSE(0, display(verbose_stream()));
        return r;
    }

    // record new monomials that are created and recursively down-saturate with respect to these.
    // this is a simplistic pass
    void mul_saturate::add_multiply_constraints() {
        m_new_mul_constraints.reset();
        m_seen_vars.reset();
        m_var_signs.reset();
        m_to_refine.reset();
        vector<svector<lp::constraint_index>> var2cs;

        for (auto ci : local_solver->constraints().indices()) {
            auto const& con = local_solver->constraints()[ci];
            for (auto [coeff, v] : con.coeffs()) {
                if (v >= var2cs.size())
                    var2cs.resize(v + 1);
                var2cs[v].push_back(ci);
            }

            // insert monomials to be refined
            insert_monomials_from_constraint(ci);            
        }

        for (unsigned it = 0; it < m_to_refine.size(); ++it) {
            auto j = m_to_refine[it];
            verbose_stream() << "refining " << j << " := " << m_mon2vars[j] << "\n";
            auto vars = m_mon2vars[j];
            for (auto v : vars) {
                if (v >= var2cs.size())
                    continue;
                auto cs = var2cs[v];
                for (auto ci : cs) {
                    for (auto [coeff, u] : local_solver->constraints()[ci].coeffs()) {
                        if (u == v)
                            add_multiply_constraint(ci, j, v);
                    }                    
                }
            }
        }
        IF_VERBOSE(0,
                   c().lra_solver().display(verbose_stream() << "original\n");
                   c().display(verbose_stream());
                   display(verbose_stream() << "saturated\n"));
    }

    // multiply by remaining vars
    void mul_saturate::add_multiply_constraint(lp::constraint_index old_ci, lp::lpvar mi, lpvar x) {
        lp::lar_base_constraint const& con = local_solver->constraints()[old_ci];
        auto &lra = c().lra_solver();
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
            m_seen_vars.insert(v);
            // retrieve bounds of v
            // if v has positive lower bound add as positive
            // if v has negative upper bound add as negative
            // otherwise, soft-fail (for now unsound)
            // proper signs of variables from old tableau should be extracted using lra_solver()
            // instead of local_solver.
            // TODO is to also add case where lower or upper bound is zero and then the sign
            // of the inequality is relaxed if it is strict.
            if (lra.number_of_vars() > v && lra.column_has_lower_bound(v) && lra.get_lower_bound(v).is_pos()) {
                m_var_signs.push_back({v, false, lra.get_column_lower_bound_witness(v)});
            } 
            else if (lra.number_of_vars() > v && lra.column_has_upper_bound(v) && lra.get_upper_bound(v).is_neg()) {
                m_var_signs.push_back({v, true, lra.get_column_upper_bound_witness(v)});
                sign = !sign;
            } 
            else if (m_values[v].is_neg()) {
                m_var_signs.push_back({v, true, nullptr});
                sign = !sign;
            } 
            else if (m_values[v].is_pos()) {
                m_var_signs.push_back({v, false, nullptr});
            } 
            else {
                IF_VERBOSE(0, verbose_stream() << "not separated from 0\n");
                return;
            }
        }
        lp::lar_term new_lhs;
        rational new_rhs(rhs), term_value(0);
        for (auto const & [coeff, v] : lhs) {
            unsigned old_sz = vars.size();
            if (m_mon2vars.contains(v))
                vars.append(m_mon2vars[v]);
            else
                vars.push_back(v);
            lpvar new_monic_var = add_monomial(vars);
            new_lhs.add_monomial(coeff, new_monic_var);
            term_value += coeff * m_values[new_monic_var];
            vars.shrink(old_sz);
        }
        if (rhs != 0) {
            lpvar new_monic_var = add_monomial(vars);
            new_lhs.add_monomial(-rhs, new_monic_var);
            term_value -= rhs * m_values[new_monic_var];
            new_rhs = 0;
        }

        if (sign) {
            switch (k) {
            case lp::lconstraint_kind::LE:
                k = lp::lconstraint_kind::GE;
                break;
            case lp::lconstraint_kind::LT:
                k = lp::lconstraint_kind::GT;
                break;
            case lp::lconstraint_kind::GE:
                k = lp::lconstraint_kind::LE;
                break;
            case lp::lconstraint_kind::GT:
                k = lp::lconstraint_kind::LT;
                break;
            default:
                break;
            }
        }
        display_constraint(verbose_stream(), old_ci) << " -> ";
        display_constraint(verbose_stream(), new_lhs.coeffs_as_vector(), k, new_rhs) << "\n";
        auto ti = local_solver->add_term(new_lhs.coeffs_as_vector(), local_solver->number_of_vars());
        auto new_ci = local_solver->add_var_bound(ti, k, new_rhs);
        insert_monomials_from_constraint(new_ci);
        m_values.push_back(term_value);
        SASSERT(m_values.size() - 1 == ti);
        m_new_mul_constraints.insert(new_ci, old_ci);
    }

    lpvar mul_saturate::add_monomial(svector<lpvar> const& vars) {
        lpvar v;
        if (vars.size() == 1)
            return vars[0];
        svector<lpvar> _vars(vars);
        std::sort(_vars.begin(), _vars.end());
        if (m_vars2mon.find(_vars, v))
            return v;

        v = add_var(is_int(vars));
        m_vars2mon.insert(_vars, v);
        m_mon2vars.insert(v, _vars);
        rational p(1);
        for (auto v : vars)
            p *= m_values[v];
        m_values.push_back(p);
        SASSERT(m_values.size() - 1 == v);
        return v;
    }

    bool mul_saturate::is_int(svector<lp::lpvar> const& vars) const {
        auto const& lra = m_core.lra;
        return all_of(vars, [&](lpvar v) { return lra.var_is_int(v); });
    }

    lpvar mul_saturate::add_var(bool is_int) {
        auto v = local_solver->number_of_vars();
        auto w = local_solver->add_var(v, is_int);
        VERIFY(v == w);
        return w;
    }

    void mul_saturate::insert_monomials_from_constraint(lp::constraint_index ci) {
        if (constraint_is_true(ci))
            return;
        auto const& con = local_solver->constraints()[ci];
        for (auto [coeff, v] : con.coeffs()) 
            if (c().is_monic_var(v))
                m_to_refine.insert(v);        
    }

    bool mul_saturate::constraint_is_true(lp::constraint_index ci) {
        auto const& con = local_solver->constraints()[ci];
        auto lhs = -con.rhs();
        for (auto const& [coeff, v] : con.coeffs())
            lhs += coeff * m_values[v];
        switch (con.kind()) {
            case lp::lconstraint_kind::GT:
                return lhs > 0;
            case lp::lconstraint_kind::GE:
                return lhs >= 0;
            case lp::lconstraint_kind::LE:
                return lhs <= 0;
            case lp::lconstraint_kind::LT:
                return lhs < 0;
            case lp::lconstraint_kind::EQ:
                return lhs == 0;
            case lp::lconstraint_kind::NE:
                return lhs != 0;
            default:
                UNREACHABLE();
                return false;        
        }
    }

    std::ostream& mul_saturate::display(std::ostream& out) const {
        local_solver->display(out);
        for (auto const& [vars, v] : m_vars2mon) {
            out << "j" << v << " := ";
            display_product(out, vars);
            out << "\n";
        }
        return out;
    }

    std::ostream& mul_saturate::display_product(std::ostream& out, svector<lpvar> const& vars) const {
        bool first = true;
        for (auto v : vars) {
            if (first)
                first = false;
            else
                out << " * ";
            out << "j" << v;
        }
        return out;
    }

    std::ostream& mul_saturate::display_constraint(std::ostream& out, lp::constraint_index ci) const {
        auto const& con = local_solver->constraints()[ci];
        return display_constraint(out, con.coeffs(), con.kind(), con.rhs());
    }

    std::ostream& mul_saturate::display_constraint(std::ostream& out, 
        vector<std::pair<rational, lpvar>> const& lhs,
        lp::lconstraint_kind k, rational const& rhs) const {
        bool first = true;
        for (auto [coeff, v] : lhs) {
            c().display_coeff(out, first, coeff);
            first = false;
            if (m_mon2vars.contains(v))
                display_product(out, m_mon2vars[v]);
            else
                out << "j" << v;
        }
        return out << " " << k << " " << rhs;
    }
}
