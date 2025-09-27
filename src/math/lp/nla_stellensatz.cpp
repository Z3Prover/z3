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
#include "math/lp/nla_stellensatz.h"


namespace nla {

    stellensatz::stellensatz(core* core) : common(core), m_coi(*core) {}

    lbool stellensatz::saturate() {
        lp::explanation ex;
        init_solver();
        saturate_constraints();
        lbool r = m_solver.solve(ex);
        if (r == l_false)
            add_lemma(ex);
        return r;
    }

    void stellensatz::init_solver() {
        m_solver.init();
        m_vars2mon.reset();
        m_mon2vars.reset();
        m_values.reset();
        m_coi.init();
        init_vars();
    }

    void stellensatz::init_vars() {
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
                w = m_solver.lra().add_term(t.coeffs_as_vector(), v);
            } 
            else
                w = m_solver.lra().add_var(v, lra.var_is_int(v));

            // assert bounds on v in the new solver.
            VERIFY(w == v);
            if (lra.column_has_lower_bound(v)) {
                auto lo_bound = lra.get_lower_bound(v);
                auto k = lo_bound.y > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                auto rhs = lo_bound.x;
                auto dep = lra.get_column_lower_bound_witness(v);
                auto ci = m_solver.lra().add_var_bound(v, k, rhs);
                m_ci2dep.setx(ci, dep, nullptr);
            }
            if (lra.column_has_upper_bound(v)) {
                auto hi_bound = lra.get_upper_bound(v);
                auto k = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto rhs = hi_bound.x;
                auto dep = lra.get_column_upper_bound_witness(v);
                auto ci = m_solver.lra().add_var_bound(v, k, rhs);
                m_ci2dep.setx(ci, dep, nullptr);
            }
        }
    }

    void stellensatz::init_monomial(unsigned mon_var) {
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

    void stellensatz::add_lemma(lp::explanation const& ex1) {
        auto& lra = c().lra_solver();
        lp::explanation ex2;
        lemma_builder new_lemma(c(), "stellensatz");
        for (auto p : ex1) {
            auto dep = m_ci2dep.get(p.ci(), nullptr);
            m_solver.lra().push_explanation(dep, ex2);
            if (!m_new_mul_constraints.contains(p.ci()))
                continue;
            
            auto const& bounds = m_new_mul_constraints[p.ci()];
            for (auto const& b : bounds) {
                if (std::holds_alternative<u_dependency*>(b)) {
                    auto dep = *std::get_if<u_dependency*>(&b);
                    m_solver.lra().push_explanation(dep, ex2);
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

    //
    // TODO - also possible:
    // derive units
    // x*y = +/-x => y = +/-1
    // 
    // derive monotonicity:
    // x >= 1 => |xy| > |y|
    //
    // add monotonicity axioms for squares
    // 
    // Use to_refine and model from c().lra_solver() for initial pass.
    // Use model from m_solver.lra() for subsequent passes.
    //    
    void stellensatz::saturate_basic_linearize() {
        auto &lra = c().lra_solver();
        for (auto j : c().to_refine()) {
            auto const &vars = m_mon2vars[j];
            auto val_j = c().val(j);
            auto val_vars = m_values[j];
            saturate_signs(j, val_j, vars, val_vars);
            saturate_units(j, vars);            
        }
    }

    //
    // Sign axioms:
    // x = 0 => x*y = 0
    // the equation x*y = 0 is asserted with assumption x = 0
    // x > 0 & y < 0 => x*y < 0
    // 
    void stellensatz::saturate_signs(lpvar j, rational const& val_j, svector<lpvar> const& vars,
        rational const& val_vars) {
        if (val_vars == 0 && val_j != 0) {
            bound_justifications bounds;
            lbool sign = add_bounds(vars, bounds);
            SASSERT(sign == l_undef);
            auto new_ci = m_solver.lra().add_var_bound(j, lp::lconstraint_kind::EQ, rational(0));
            m_new_mul_constraints.insert(new_ci, bounds);
            m_ci2dep.setx(new_ci, nullptr, nullptr);
        } 
        else if (val_j <= 0 && 0 < val_vars) {
            bound_justifications bounds;
            lbool sign = add_bounds(vars, bounds);
            SASSERT(sign == l_false);
            auto new_ci = m_solver.lra().add_var_bound(j, lp::lconstraint_kind::GT, rational(0));
            m_new_mul_constraints.insert(new_ci, bounds);
            m_ci2dep.setx(new_ci, nullptr, nullptr);
        } 
        else if (val_j >= 0 && 0 > val_vars) {
            bound_justifications bounds;
            lbool sign = add_bounds(vars, bounds);
            SASSERT(sign == l_true);
            auto new_ci = m_solver.lra().add_var_bound(j, lp::lconstraint_kind::LT, rational(0));
            m_new_mul_constraints.insert(new_ci, bounds);
            m_ci2dep.setx(new_ci, nullptr, nullptr);
        }
    }

    //
    // Unit axioms:
    // x = -1 => x*y = -y
    // x = 1 => x*y = y
    //
    void stellensatz::saturate_units(lpvar j, svector<lpvar> const &vars) {
        lpvar non_unit = lp::null_lpvar;
        bool sign = false;
        for (auto v : vars) {
            if (m_values[v] == 1)
                continue;
            if (m_values[v] == -1) {
                sign = !sign;
                continue;
            }
            if (non_unit != lp::null_lpvar)
                return;
            non_unit = v;
        }
        bound_justifications bounds;
        for (auto v : vars) {
            if (m_values[v] == 1 || m_values[v] == -1) {
                bound b(v, lp::lconstraint_kind::EQ, rational(m_values[v]));
                bounds.push_back(b);
            }
        }
        // assert j = +/- non_unit
        lp::lar_term new_lhs;
        new_lhs.add_monomial(rational(1), j);
        new_lhs.add_monomial(rational(sign ? 1 : -1), non_unit);
        auto ti = m_solver.lra().add_term(new_lhs.coeffs_as_vector(), m_solver.lra().number_of_vars());
        m_values.push_back(m_values[j] - (sign ? 1 : -1) * m_values[non_unit]);
        auto k = lp::lconstraint_kind::EQ;
        auto new_ci = m_solver.lra().add_var_bound(ti, k, rational(0));
        SASSERT(m_values.size() - 1 == ti);
        m_new_mul_constraints.insert(new_ci, bounds);
        m_ci2dep.setx(new_ci, nullptr, nullptr);
    }

    // record new monomials that are created and recursively down-saturate with respect to these.
    // this is a simplistic pass
    void stellensatz::saturate_constraints() {
        m_new_mul_constraints.reset();
        m_to_refine.reset();
        vector<svector<lp::constraint_index>> var2cs; 

        // current approach: only resolve against var2cs, which is initialized
        // with monomials in the input.

        for (auto ci : m_solver.lra().constraints().indices()) {
            auto const& con = m_solver.lra().constraints()[ci];
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
                    for (auto [coeff, u] : m_solver.lra().constraints()[ci].coeffs()) {
                        if (u == v)
                            saturate_constraint(ci, j, v);
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
    void stellensatz::saturate_constraint(lp::constraint_index old_ci, lp::lpvar mi, lpvar x) {
        lp::lar_base_constraint const& con = m_solver.lra().constraints()[old_ci];
        auto const& lhs = con.coeffs();
        auto const& rhs = con.rhs();
        auto k = con.kind();
        if (k == lp::lconstraint_kind::NE || k == lp::lconstraint_kind::EQ)
            return;  // not supported
        svector<lpvar> vars;
        bool first = true;
        for (auto v : m_mon2vars[mi]) {
            if (v != x || !first)
                vars.push_back(v);
            else
                first = false;
        }
        SASSERT(!first); // v was a member and was removed

        bound_justifications bounds;
        // compute bounds constraints and sign of vars
        lbool sign = add_bounds(vars, bounds);
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

        if (sign == l_true) 
            k = swap_side(k);
        
        if (sign == l_undef) {
            switch (k) {
            case lp::lconstraint_kind::GT:
                k = lp::lconstraint_kind::GE;
                break;
            case lp::lconstraint_kind::LT:
                k = lp::lconstraint_kind::LE;
                break;
            }
        }

        auto ti = m_solver.lra().add_term(new_lhs.coeffs_as_vector(), m_solver.lra().number_of_vars());
        auto new_ci = m_solver.lra().add_var_bound(ti, k, new_rhs);
        IF_VERBOSE(4, display_constraint(verbose_stream(), old_ci) << " -> ";
                   display_constraint(verbose_stream(), new_lhs.coeffs_as_vector(), k, new_rhs) << "\n");
        insert_monomials_from_constraint(new_ci);
        m_values.push_back(term_value);
        SASSERT(m_values.size() - 1 == ti);
        m_new_mul_constraints.insert(new_ci, bounds);
        m_ci2dep.setx(new_ci, m_ci2dep.get(old_ci, nullptr), nullptr);
    }

    lbool stellensatz::add_bounds(svector<lpvar> const& vars, bound_justifications& bounds) {
        bool sign = false;
        auto &lra = c().lra_solver();
        auto add_bound = [&](lpvar v, lp::lconstraint_kind k, int r) {
            bound b(v, k, rational(r));
            bounds.push_back(b);
        };
        for (auto v : vars) {
            if (m_values[v] != 0)
                continue;
            add_bound(v, lp::lconstraint_kind::EQ, 0); 
            return l_undef;
        }
        for (auto v : vars) {
            // retrieve bounds of v
            // if v has positive lower bound add as positive
            // if v has negative upper bound add as negative
            // otherwise look at the current value of v and add bounds assumption based on current sign.
            // todo: detect squares, allow for EQ but skip bounds assumptions.
            if (lra.number_of_vars() > v && lra.column_has_lower_bound(v) && lra.get_lower_bound(v).is_pos()) {
                bounds.push_back(lra.get_column_lower_bound_witness(v));
            } else if (lra.number_of_vars() > v && lra.column_has_upper_bound(v) && lra.get_upper_bound(v).is_neg()) {
                bounds.push_back(lra.get_column_upper_bound_witness(v));
                sign = !sign;
            } else if (m_values[v].is_neg()) {
                if (lra.var_is_int(v))
                    add_bound(v, lp::lconstraint_kind::LE, -1);
                else
                    add_bound(v, lp::lconstraint_kind::LT, 0);
                sign = !sign;
            } else if (m_values[v].is_pos()) {
                if (lra.var_is_int(v))
                    add_bound(v, lp::lconstraint_kind::GE, 1);
                else
                    add_bound(v, lp::lconstraint_kind::GT, 0);
            } else {
                UNREACHABLE();
            }
        }
        return sign ? l_true : l_false;
    }

    // Insert a (new) monomial representing product of vars.
    // if the length of vars is 1 then the new monomial is vars[0]
    // if the same monomial was previous defined, return the previously defined monomial.
    // otherwise create a fresh variable representing the monomial.
    // todo: if _vars is a square, then add bound axiom.
    lpvar stellensatz::add_monomial(svector<lpvar> const& vars) {
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

    bool stellensatz::is_int(svector<lp::lpvar> const& vars) const {
        return all_of(vars, [&](lpvar v) { return m_solver.lra().var_is_int(v); });
    }

    lpvar stellensatz::add_var(bool is_int) {
        auto v = m_solver.lra().number_of_vars();
        auto w = m_solver.lra().add_var(v, is_int);
        SASSERT(v == w);
        return w;
    }

    // if a constraint is false, then insert _all_ monomials from that constraint.
    // other approach: use a lex ordering on monomials and insert the lex leading monomial.   
    void stellensatz::insert_monomials_from_constraint(lp::constraint_index ci) {
        if (constraint_is_true(ci))
            return;
        auto const& con = m_solver.lra().constraints()[ci];
        for (auto [coeff, v] : con.coeffs())
            if (c().is_monic_var(v))
                m_to_refine.insert(v);        
    }

    bool stellensatz::constraint_is_true(lp::constraint_index ci) {
        auto const& con = m_solver.lra().constraints()[ci];
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

    std::ostream& stellensatz::display(std::ostream& out) const {
        m_solver.lra().display(out);
        for (auto const& [vars, v] : m_vars2mon) {
            out << "j" << v << " := ";
            display_product(out, vars);
            out << "\n";
        }
        return out;
    }

    std::ostream& stellensatz::display_product(std::ostream& out, svector<lpvar> const& vars) const {
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

    std::ostream& stellensatz::display_constraint(std::ostream& out, lp::constraint_index ci) const {
        auto const& con = m_solver.lra().constraints()[ci];
        return display_constraint(out, con.coeffs(), con.kind(), con.rhs());
    }

    std::ostream& stellensatz::display_constraint(std::ostream& out, 
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

    
    // Solver component
    // check LRA feasibilty
    // (partial) check LIA feasibility
    // try patch LIA model
    // option: iterate by continuing saturation based on partial results
    // option: add incremental linearization axioms
    // option: detect squares and add axioms for violated squares
    // option: add NIA filters (non-linear divisbility axioms)    

    void stellensatz::solver::init() {
        lra_solver = alloc(lp::lar_solver);
        int_solver = alloc(lp::int_solver, *lra_solver);
    }

    lbool stellensatz::solver::solve(lp::explanation &ex) {
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

    lbool stellensatz::solver::solve_lra(lp::explanation &ex) {
        auto st = lra_solver->solve();
        if (st == lp::lp_status::INFEASIBLE) {
            lra_solver->get_infeasibility_explanation(ex);
            return l_false;
        } else if (lra_solver->is_feasible())
            return l_true;
        else
            return l_undef;
    }

    lbool stellensatz::solver::solve_lia(lp::explanation &ex) {
        switch (int_solver->check(&ex)) {
        case lp::lia_move::sat:
            return l_true;
        case lp::lia_move::conflict:
            return l_false;
        default:  // TODO: an option is to perform (bounded) search here to get an LIA verdict.
            return l_undef;
        }
        return l_undef;
    }
}
