/*++
  Copyright (c) 2025 Microsoft Corporation

  given a monic m = x * y * z ... used in a constraint that is false under the current evaluation of x,y,z

  saturate constraints with respect to m
  in other words, if a constraint contains x*y + p >= 0, 
  then include the constraint x*y*z + z*p >= 0
  assuming current value of z is non-negative.
  Check if the system with new constraints is LP (and MIP) feasible.
  If it is not, then produce a lemma that explains infeasibility.

  Strategy 1: The lemma is in terms of the original constraints and bounds.
  Strategy 2: Attempt to eliminate new monomials from the lemma by relying on Farkas multipliers.
              If it succeeds to eliminate new monomials we have a lemma that is a linear 
              combination of existing variables. 
              The idea is that a conflict over the new system is a set of multipliers lambda, such
              that lambda * A is separated from b for the constraints Axy >= b.
              The coefficients in lambda are non-negative.
              They correspond to variables x, y where x are variables from the input constraints
              and y are new variables introduced for new monomials.
              We can test if lambda allows eliminating y by taking a subset of lambda indices where
              A has rows containing y_i for some fresh y_i. Replace those rows r_j by the partial sum of
              of rows multiplied by lambda_j. The sum r_j1 * lambda_j1 + .. + r_jk * lambda_jk does not
              contain y_i. Repeat the same process with other variables y_i'. If a sum is
              generated without any y, it is a linear consequence of the new constraints but not
              necessarily derivable with the old constraints.
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
        lra_solver = alloc(lp::lar_solver);
        int_solver = alloc(lp::int_solver, *lra_solver);
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
            // Declare v into lra_solver
            unsigned w;
            if (m_coi.mons().contains(v))
                init_monomial(v);
            else 
                m_values.push_back(c().val(v));
            if (m_coi.terms().contains(v)) {
                auto const& t = lra.get_term(v);
                // Assumption: variables in coefficients are always declared before term variable.
                SASSERT(all_of(t, [&](auto p) { return p.j() < v; }));
                w = lra_solver->add_term(t.coeffs_as_vector(), v);
            } 
            else
                w = lra_solver->add_var(v, lra.var_is_int(v));

            // assert bounds on v in the new solver.
            VERIFY(w == v);
            if (lra.column_has_lower_bound(v)) {
                auto lo_bound = lra.get_lower_bound(v);
                auto k = lo_bound.y > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                auto rhs = lo_bound.x;
                auto dep = lra.get_column_lower_bound_witness(v);
                auto ci = lra_solver->add_var_bound(v, k, rhs);
                m_ci2dep.setx(ci, dep, nullptr);
            }
            if (lra.column_has_upper_bound(v)) {
                auto hi_bound = lra.get_upper_bound(v);
                auto k = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto rhs = hi_bound.x;
                auto dep = lra.get_column_upper_bound_witness(v);
                auto ci = lra_solver->add_var_bound(v, k, rhs);
                m_ci2dep.setx(ci, dep, nullptr);
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
        lemma_builder new_lemma(c(), "stellensatz");
        for (auto p : ex1) {
            auto dep = m_ci2dep.get(p.ci(), nullptr);
            lra_solver->push_explanation(dep, ex2);
            if (!m_new_mul_constraints.contains(p.ci()))
                continue;
            
            auto const& bounds = m_new_mul_constraints[p.ci()];
            for (auto const& b : bounds) {
                if (std::holds_alternative<u_dependency*>(b)) {
                    auto dep = *std::get_if<u_dependency*>(&b);
                    lra_solver->push_explanation(dep, ex2);
                } 
                else {
                    auto const &[v, k, rhs] = *std::get_if<bound>(&b);    
                    new_lemma |= ineq(v, negate(k), rhs);
                }
            }
        }

        new_lemma &= ex2;
        IF_VERBOSE(5, verbose_stream() << "unsat \n" << new_lemma << "\n");
        TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
        c().lra_solver().settings().stats().m_nla_stellensatz++;
    }


    lbool mul_saturate::solve(lp::explanation& ex) {
        lbool r = solve_lra(ex);
        if (r != l_true)
            return r;
        r = solve_lia(ex);
        if (r != l_true)
            return r;
        // if (r == l_true) check if solution satisfies constraints
        // variables outside the slice have values from the outer solver.
        return l_undef;
    }

    lbool mul_saturate::solve_lra(lp::explanation& ex) {         
        auto st = lra_solver->solve();
        if (st == lp::lp_status::INFEASIBLE) {
            lra_solver->get_infeasibility_explanation(ex);
            return l_false;
        } 
        else if (lra_solver->is_feasible())
            return l_true;
        else
            return l_undef;
    }

    lbool mul_saturate::solve_lia(lp::explanation& ex) {
        switch (int_solver->check(&ex)) {
        case lp::lia_move::sat:
            return l_true;
        case lp::lia_move::conflict:
            return l_false;
        default: // TODO: an option is to perform (bounded) search here to get an LIA verdict.
            return l_undef;
        }
        return l_undef;
    }

    // record new monomials that are created and recursively down-saturate with respect to these.
    // this is a simplistic pass
    void mul_saturate::add_multiply_constraints() {
        m_new_mul_constraints.reset();
        m_to_refine.reset();
        vector<svector<lp::constraint_index>> var2cs; 

        // current approach: only resolve against var2cs, which is initialized
        // with monomials in the input.

        for (auto ci : lra_solver->constraints().indices()) {
            auto const& con = lra_solver->constraints()[ci];
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
            auto vars = m_mon2vars[j];
            for (auto v : vars) {
                if (v >= var2cs.size())
                    continue;
                auto cs = var2cs[v];
                for (auto ci : cs) {
                    for (auto [coeff, u] : lra_solver->constraints()[ci].coeffs()) {
                        if (u == v)
                            add_multiply_constraint(ci, j, v);
                    }                    
                }
            }
        }
        IF_VERBOSE(5,
                   c().lra_solver().display(verbose_stream() << "original\n");
                   c().display(verbose_stream());
                   display(verbose_stream() << "saturated\n"));
    }

    // multiply by remaining vars
    void mul_saturate::add_multiply_constraint(lp::constraint_index old_ci, lp::lpvar mi, lpvar x) {
        lp::lar_base_constraint const& con = lra_solver->constraints()[old_ci];
        auto &lra = c().lra_solver();
        auto const& lhs = con.coeffs();
        auto const& rhs = con.rhs();
        auto k = con.kind();
        if (k == lp::lconstraint_kind::NE || k == lp::lconstraint_kind::EQ)
            return;  // not supported
        auto sign = false, strict = true;
        svector<lpvar> vars;
        bool first = true;
        for (auto v : m_mon2vars[mi]) {
            if (v != x || !first)
                vars.push_back(v);
            else
                first = false;
        }
        SASSERT(!first); // v was a member and was removed

        vector<bound_justification> bounds;
        // compute bounds constraints and sign of vars

        auto add_bound = [&](lpvar v, lp::lconstraint_kind k, int r) { 
            bound b(v, k, rational(r));
            bounds.push_back(b);
        };
        for (auto v : vars) {
            // retrieve bounds of v
            // if v has positive lower bound add as positive
            // if v has negative upper bound add as negative
            // otherwise look at the current value of v and add bounds assumption based on current sign.
            if (lra.number_of_vars() > v && lra.column_has_lower_bound(v) && lra.get_lower_bound(v).is_pos()) {
                bounds.push_back(lra.get_column_lower_bound_witness(v));
            } 
            else if (lra.number_of_vars() > v && lra.column_has_upper_bound(v) && lra.get_upper_bound(v).is_neg()) {
                bounds.push_back(lra.get_column_upper_bound_witness(v));                
                sign = !sign;
            } 
            else if (m_values[v].is_neg()) {
                if (lra.var_is_int(v))
                    add_bound(v, lp::lconstraint_kind::LE, -1);
                else
                    add_bound(v, lp::lconstraint_kind::LT, 0);
                sign = !sign;
            } 
            else if (m_values[v].is_pos()) {
                if (lra.var_is_int(v)) 
                    add_bound(v, lp::lconstraint_kind::GE, 1);                
                else 
                    add_bound(v, lp::lconstraint_kind::GT, 0);                
            } 
            else {
                SASSERT(m_values[v] == 0);
                strict = false;
                add_bound(v, lp::lconstraint_kind::GE, 0);                
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

        if (sign) 
            k = swap_side(k);
        
        if (!strict) {
            switch (k) {
            case lp::lconstraint_kind::GT:
                k = lp::lconstraint_kind::GE;
                break;
            case lp::lconstraint_kind::LT:
                k = lp::lconstraint_kind::LE;
                break;
            }
        }

        auto ti = lra_solver->add_term(new_lhs.coeffs_as_vector(), lra_solver->number_of_vars());
        auto new_ci = lra_solver->add_var_bound(ti, k, new_rhs);
        IF_VERBOSE(4, display_constraint(verbose_stream(), old_ci) << " -> ";
                   display_constraint(verbose_stream(), new_lhs.coeffs_as_vector(), k, new_rhs) << "\n");
        insert_monomials_from_constraint(new_ci);
        m_values.push_back(term_value);
        SASSERT(m_values.size() - 1 == ti);
        m_new_mul_constraints.insert(new_ci, bounds);
        m_ci2dep.setx(new_ci, m_ci2dep.get(old_ci, nullptr), nullptr);
    }

    // Insert a (new) monomial representing product of vars.
    // if the length of vars is 1 then the new monomial is vars[0]
    // if the same monomial was previous defined, return the previously defined monomial.
    // otherwise create a fresh variable representing the monomial.
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
        auto v = lra_solver->number_of_vars();
        auto w = lra_solver->add_var(v, is_int);
        SASSERT(v == w);
        return w;
    }

    // if a constraint is false, then insert _all_ monomials from that constraint.
    // other approach: use a lex ordering on monomials and insert the lex leading monomial.   
    void mul_saturate::insert_monomials_from_constraint(lp::constraint_index ci) {
        if (constraint_is_true(ci))
            return;
        auto const& con = lra_solver->constraints()[ci];
        for (auto [coeff, v] : con.coeffs()) 
            if (c().is_monic_var(v))
                m_to_refine.insert(v);        
    }

    bool mul_saturate::constraint_is_true(lp::constraint_index ci) {
        auto const& con = lra_solver->constraints()[ci];
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
        lra_solver->display(out);
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
        auto const& con = lra_solver->constraints()[ci];
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
