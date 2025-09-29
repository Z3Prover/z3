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

Auxiliary methods:
- basic lemmas
- factoring

Potential auxiliary methods:
- tangent, ordering lemmas (lemmas that use values from the current model)
- with internal bounded backtracking.

Currently missed lemma:

(30) j17 >= 0
(15) j4 - j7 >= 1
(51) j25 - j27 >= 1
(38) j11 - j23 >= 0
(9) j4 >= 1
(26) j5*j7 - j4*j11_ - j17 >= 0
(57) j11 >= 1
(10) j5 - j4 >= 0
(12) j7 >= 1
(46) - j5 + j23 + j27 >= 0
(44) j4 - j7 - j25 >= 0

j4 - j7 - j27 >= 1
j4 - j5 - j7 + j23 >= 1  (from (46))
j4 - j5 + j23 >= 2
j4 - j5 + j11 >= 2
j4 - j5 >= 3
..

  */

#include "math/lp/nla_core.h"
#include "math/lp/nla_coi.h"
#include "math/lp/nla_stellensatz.h"

namespace nla {

    stellensatz::stellensatz(core* core) : 
        common(core), 
        m_solver(*this), 
        m_coi(*core), 
        m_pm(c().reslim(), m_qm, &m_allocator)   
    {}

    lbool stellensatz::saturate() {
        lp::explanation ex;
        vector<ineq> ineqs;
        init_solver();
        saturate_constraints();
        saturate_basic_linearize();
        TRACE(arith, display(tout << "stellensatz after saturation\n"));
        lbool r = m_solver.solve(ex, ineqs);
        if (r == l_false)
            add_lemma(ex, ineqs);
        return r;
    }

    void stellensatz::init_solver() {
        m_solver.init();
        m_vars2mon.reset();
        m_mon2vars.reset();
        m_values.reset();
        m_resolvents.reset();
        m_old_constraints.reset();
        m_new_bounds.reset();
        m_to_refine.reset();
        m_factored_constraints.reset();
        m_coi.init();
        init_vars();
    }

    void stellensatz::init_vars() {
        auto const& src = c().lra_solver();
        auto &dst = m_solver.lra();
        auto sz = src.number_of_vars();
        for (unsigned v = 0; v < sz; ++v) {
            // Declare v into m_solver.lra()
            unsigned w;
            if (m_coi.mons().contains(v))
                init_monomial(v);
            else 
                m_values.push_back(c().val(v));
            if (m_coi.terms().contains(v)) {
                auto const& t = src.get_term(v);
                // Assumption: variables in coefficients are always declared before term variable.
                SASSERT(all_of(t, [&](auto p) { return p.j() < v; }));
                w = dst.add_term(t.coeffs_as_vector(), v);
            } 
            else
                w = dst.add_var(v, src.var_is_int(v));

            // assert bounds on v in the new solver.
            VERIFY(w == v);
            if (src.column_has_lower_bound(v)) {
                auto lo_bound = src.get_lower_bound(v);
                SASSERT(lo_bound.y >= 0);
                auto k   = lo_bound.y > 0 ? lp::lconstraint_kind::GT : lp::lconstraint_kind::GE;
                auto rhs = lo_bound.x;
                auto dep = src.get_column_lower_bound_witness(v);
                auto ci  = dst.add_var_bound(v, k, rhs);
                m_ci2dep.setx(ci, dep, nullptr);
            }
            if (src.column_has_upper_bound(v)) {
                auto hi_bound = src.get_upper_bound(v);
                SASSERT(hi_bound.y <= 0);
                auto k   = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto rhs = hi_bound.x;
                auto dep = src.get_column_upper_bound_witness(v);
                auto ci  = dst.add_var_bound(v, k, rhs);
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
        m_values.push_back(value(vars));
    }

    //
    // convert a conflict from m_solver.lra()/lia() into
    // a conflict for c().lra_solver()
    // 1. constraints that are obtained by multiplication are explained from the original constraint
    // 2. bounds assumptions are added as assumptions to the lemma.
    // 
    void stellensatz::add_lemma(lp::explanation const& ex1, vector<ineq> const& ineqs) {
        auto& lra = c().lra_solver();
        lp::explanation ex2;
        lemma_builder new_lemma(c(), "stellensatz");
        m_constraints_in_conflict.reset();
        for (auto p : ex1) 
            explain_constraint(new_lemma, p.ci(), ex2);        
        new_lemma &= ex2;
        for (auto const &ineq : ineqs)
            new_lemma |= ineq;
        IF_VERBOSE(5, verbose_stream() << "unsat \n" << new_lemma << "\n");
        TRACE(arith, tout << "unsat\n" << new_lemma << "\n");
        c().lra_solver().settings().stats().m_nla_stellensatz++;
    }

    //
    // a constraint can be explained by a set of bounds used as assumptions
    // and by an original constraint.
    // 
    void stellensatz::explain_constraint(lemma_builder& new_lemma, lp::constraint_index ci, lp::explanation& ex) {
        if (m_constraints_in_conflict.contains(ci))
            return;
        m_constraints_in_conflict.insert(ci);
        auto dep = m_ci2dep[ci];
        m_solver.lra().push_explanation(dep, ex);        
        lp::constraint_index old_ci;
        if (m_old_constraints.find(ci, old_ci))
            explain_constraint(new_lemma, old_ci, ex);
        if (!m_new_bounds.contains(ci))
            return;
        auto const &bounds = m_new_bounds[ci];
        for (auto const &b : bounds) {
            if (std::holds_alternative<u_dependency *>(b)) {
                auto dep = *std::get_if<u_dependency *>(&b);
                m_solver.lra().push_explanation(dep, ex);
            } 
            else {
                //
                // the inequality was posted as an assumption
                // negate it to add to the lemma
                // recall that lemmas are represented in the form: /\ Assumptions => \/ C
                //
                auto [v, k, rhs] = *std::get_if<bound>(&b);
                k = negate(k);
                if (m_solver.lra().var_is_int(v)) {
                    if (k == lp::lconstraint_kind::GT) {
                        rhs += 1;
                        k = lp::lconstraint_kind::GE;
                    }
                    if (k == lp::lconstraint_kind::LT) {
                        rhs -= 1;
                        k = lp::lconstraint_kind::LE;
                    }
                }
                new_lemma |= ineq(v, k, rhs);
            }
        }
    }

    //
    // Emulate linearization within stellensatz to enforce simple axioms.
    // Incremental linearization in the main procedure produces new atoms that are pushed to lemmas
    // Here, it creates potentially new atoms from bounds assumptions, but it checks linear 
    // feasibility first. 
    //
    // Use to_refine and model from c().lra_solver() for initial pass.
    // Use model from m_solver.lra() for subsequent passes.
    //
    // Basic linearization - encoded   
    // - sign axioms - implicit in down saturation (establish redundancy?)
    // - unit axioms - do not follow
    // - monotonicity - implicit in down saturation (establish redundancy?)
    // - squares - do not follow from anything else
    // Order lemmas - claim: are subsumed by downwards saturation.
    // x > 0, y > z => xy > xz because y > z gets multiplied by x due to the subterm xy.
    // Monotonicity lemmas - x >= |val(x)| & y >= |val(y)| => xy >= |val(x)||val(y)|
    //                     - not encoded
    // Tangent lemmas -     (x - |val(x)|+1) * (y - |val(y)| + 1) > 0 in case |val(xy)| < |val(x)||val(y)|
    //                     - not encoded
    // 
    void stellensatz::saturate_basic_linearize() {
        for (auto j : c().to_refine()) {
            auto const &vars = m_mon2vars[j];
            auto val_j = c().val(j);
            auto val_vars = m_values[j];
            saturate_basic_linearize(j, val_j, vars, val_vars);
        }
    }

    void stellensatz::saturate_basic_linearize(lpvar j, rational const& val_j, svector<lpvar> const& vars,
        rational const& val_vars) {
        saturate_signs(j, val_j, vars, val_vars);
        saturate_units(j, vars);
        saturate_monotonicity(j, val_j, vars, val_vars);
        saturate_squares(j, val_j, vars);
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
            VERIFY(sign == l_undef);
            add_ineq("signs = 0", bounds, j, lp::lconstraint_kind::EQ, rational(0));
        } 
        else if (val_j <= 0 && 0 < val_vars) {
            bound_justifications bounds;
            lbool sign = add_bounds(vars, bounds);
            VERIFY(sign == l_false);
            add_ineq("signs > 0", bounds, j, lp::lconstraint_kind::GT, rational(0));
        } 
        else if (val_j >= 0 && 0 > val_vars) {
            bound_justifications bounds;
            lbool sign = add_bounds(vars, bounds);
            VERIFY(sign == l_true);
            add_ineq("signs < 0", bounds, j, lp::lconstraint_kind::LT, rational(0));
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
                bound b(v, lp::lconstraint_kind::EQ, m_values[v]);
                bounds.push_back(b);
            }
        }
        // assert j = +/- non_unit
        lp::lar_term lhs;
        lhs.add_monomial(rational(1), j);
        lhs.add_monomial(rational(sign ? 1 : -1), non_unit);
        add_ineq("unit mul", bounds, lhs, lp::lconstraint_kind::EQ, rational(0));
    }

    // Monotonicity axioms:
    // x > 1 & y > 0  => x*y > y
    // x < -1 & y > 0 => -x*y > -x
    // x > 1 & y < 0  => -x*y > x
    // x < -1 & y < 0 => x*y > -y
    void stellensatz::saturate_monotonicity(lpvar j, rational const &val_j, svector<lpvar> const &vars,
                                            rational const &val_vars) {
        if (vars.size() != 2)
            return;
        lpvar x = vars[0];
        lpvar y = vars[1];
        if (m_values[x] == 0 || m_values[y] == 0)
            return;
        if (abs(m_values[x]) <= 1 && abs(m_values[y]) <= 1)
            return;
        saturate_monotonicity(j, val_j, x, y);
        saturate_monotonicity(j, val_j, y, x);
    }

    void stellensatz::saturate_monotonicity(lpvar j, rational const &val_j, lpvar x, lpvar y) {
        auto valx = m_values[x];
        auto valy = m_values[y];
        if (valx > 1 && valy > 0 && val_j <= valy)
            saturate_monotonicity(j, val_j, x, 1, y, 1);
        else if (valx > 1 && valy < 0 && -val_j <= -valy)
            saturate_monotonicity(j, val_j, x, 1, y, -1);
        else if (valx < -1 && valy > 0 && -val_j <= valy)
            saturate_monotonicity(j, val_j, x, -1, y, 1);
        else if (valx < -1 && valy < 0 && val_j <= -valy)
            saturate_monotonicity(j, val_j, x, -1, y, -1);
    }

    // x > 1, y > 0 => xy > y
    // x > 1, y < 1 => -xy > -y
    void stellensatz::saturate_monotonicity(lpvar j, rational const& val_j, lpvar x, int sign_x, lpvar y, int sign_y) {
        bound_justifications bounds;
        bound b1(x, sign_x < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::GT, rational(sign_x));
        bound b2(y, sign_y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::GT, rational(0));
        bounds.push_back(b1);
        bounds.push_back(b2);
        lp::lar_term lhs;
        lhs.add_monomial(rational(sign_x * sign_y), j);
        lhs.add_monomial(rational(-sign_y), y);
        add_ineq("monotonicity", bounds, lhs, lp::lconstraint_kind::GT, rational(0));
    }

    void stellensatz::saturate_squares(lpvar j, rational const& val_j, svector<lpvar> const& vars) {
        if (val_j >= 0)
            return;
        if (vars.size() % 2 != 0)
            return;
        for (unsigned i = 0; i + 1 < vars.size(); i += 2) {
            if (vars[i] != vars[i + 1])
                return;
        }
        // it is a square.
        bound_justifications bounds;
        add_ineq("squares", bounds, j, lp::lconstraint_kind::GE, rational(0));
    }

    rational stellensatz::value(lp::lar_term const &t) const {
        rational r(0);
        for (auto cv : t)
            r += m_values[cv.j()] * cv.coeff();
        return r;
    }

    rational stellensatz::value(svector<lpvar> const &prod) const {
        rational p(1);
        for (auto v : prod)
            p *= m_values[v];
        return p;
    }

    lp::constraint_index stellensatz::add_ineq(char const* rule, 
        bound_justifications const& bounds,
        lp::lar_term const& t, lp::lconstraint_kind k,
        rational const& rhs) {
        SASSERT(!t.coeffs_as_vector().empty());
        auto ti = m_solver.lra().add_term(t.coeffs_as_vector(), m_solver.lra().number_of_vars());
        m_values.push_back(value(t));
        auto new_ci = m_solver.lra().add_var_bound(ti, k, rhs);
        TRACE(arith, 
            display_constraint(tout << rule << ": ", new_ci) << "\n"; 
            if (!bounds.empty()) display(tout << "\t <- ", bounds) << "\n";);
        SASSERT(m_values.size() - 1 == ti);
        m_new_bounds.insert(new_ci, bounds);
        m_ci2dep.setx(new_ci, nullptr, nullptr);
        return new_ci;
    }

    lp::constraint_index stellensatz::add_ineq(char const* rule, bound_justifications const& bounds, lpvar j, lp::lconstraint_kind k,
        rational const& rhs) {
        auto new_ci = m_solver.lra().add_var_bound(j, k, rhs);
        m_new_bounds.insert(new_ci, bounds);
        m_ci2dep.setx(new_ci, nullptr, nullptr);
        return new_ci;
    }

    // record new monomials that are created and recursively down-saturate with respect to these.
    // this is a simplistic pass
    void stellensatz::saturate_constraints() {
        vector<svector<lp::constraint_index>> var2cs;  // cs contain a term using v
        vector<svector<lp::constraint_index>> vars2cs; // cs contain a term with a monomial using v

        // current approach: only resolve against var2cs, which is initialized
        // with monomials in the input.

        for (auto ci : m_solver.lra().constraints().indices()) {
            auto const& con = m_solver.lra().constraints()[ci];
            for (auto [coeff, v] : con.coeffs()) {
                if (v >= var2cs.size())
                    var2cs.resize(v + 1);
                var2cs[v].push_back(ci);
                if (m_mon2vars.contains(v)) {
                    for (auto w : m_mon2vars[v]) {
                        if (w >= vars2cs.size())
                            vars2cs.resize(w + 1);
                        vars2cs[w].push_back(ci);
                    }
                }
            }
            // insert monomials to be refined
            insert_monomials_from_constraint(ci);            
        }

        auto is_subset = [&](svector<lpvar> const &a, svector<lpvar> const& b) {
            if (a.size() >= b.size())
                return false;
            // check if a is a subset of b, counting multiplicies, assume a, b are sorted
            unsigned i = 0, j = 0;
            while (i < a.size() && j < b.size()) {
                if (a[i] == b[j]) 
                    ++i;
                ++j;
            }
            return i == a.size();           
        };

        for (unsigned it = 0; it < m_to_refine.size(); ++it) {
            auto j = m_to_refine[it];
            auto vars = m_mon2vars[j];
            for (auto v : vars) {
                if (v >= var2cs.size())
                    continue;
                svector<lpvar> _vars;
                _vars.push_back(v);
                for (auto ci : var2cs[v]) {
                    for (auto [coeff, u] : m_solver.lra().constraints()[ci].coeffs()) {
                        if (u == v)
                            saturate_constraint(ci, j, _vars);
                    }
                }
            }
            for (auto v : vars) {
                if (v >= vars2cs.size())
                    continue;
                for (auto ci : vars2cs[v]) {
                    for (auto [coeff, u] : m_solver.lra().constraints()[ci].coeffs())
                        if (m_mon2vars.contains(u) && is_subset(m_mon2vars[u], vars))
                            saturate_constraint(ci, j, m_mon2vars[u]);
                }
            }
        }
        IF_VERBOSE(5,
                   c().lra_solver().display(verbose_stream() << "original\n");
                   c().display(verbose_stream());
                   display(verbose_stream() << "saturated\n"));
    }

    // multiply by remaining vars
    void stellensatz::saturate_constraint(lp::constraint_index old_ci, lpvar mi, svector<lpvar> const& xs) {
        resolvent r = {old_ci, mi, xs};
        if (m_resolvents.contains(r))
            return;
        m_resolvents.insert(r);
        lp::lar_base_constraint const& con = m_solver.lra().constraints()[old_ci];
        auto const& lhs = con.coeffs();
        auto const& rhs = con.rhs();
        auto k = con.kind();
        if (k == lp::lconstraint_kind::NE || k == lp::lconstraint_kind::EQ)
            return;  // not supported


        // xs is a proper subset of vars in mi
        svector<lpvar> vars(m_mon2vars[mi]);

        for (auto x : xs) {
            SASSERT(vars.contains(x));
            vars.erase(x);
        }
        SASSERT(!vars.empty());
        SASSERT(vars.size() + xs.size() == m_mon2vars[mi].size());

        bound_justifications bounds;
        // compute bounds constraints and sign of vars
        lbool sign = add_bounds(vars, bounds);
        lp::lar_term new_lhs;
        rational new_rhs(rhs);
        for (auto const & [coeff, v] : lhs) {
            unsigned old_sz = vars.size();
            if (m_mon2vars.contains(v))
                vars.append(m_mon2vars[v]);
            else
                vars.push_back(v);
            lpvar new_monic_var = add_monomial(vars);
            new_lhs.add_monomial(coeff, new_monic_var);
            vars.shrink(old_sz);
        }
        if (rhs != 0) {
            lpvar new_monic_var = add_monomial(vars);
            new_lhs.add_monomial(-rhs, new_monic_var);
            new_rhs = 0;
        }

        if (sign == l_true) 
            k = swap_side(k);
        
        if (sign == l_undef) {
            // x = 0 => x*y >= 0
            switch (k) {
            case lp::lconstraint_kind::GT:
                k = lp::lconstraint_kind::GE;
                break;
            case lp::lconstraint_kind::LT:
                k = lp::lconstraint_kind::LE;
                break;
            }
        }

        auto new_ci = add_ineq("superpose", bounds, new_lhs, k, new_rhs);
        IF_VERBOSE(4, display_constraint(verbose_stream(), old_ci) << " -> ";
                   display_constraint(verbose_stream(), new_lhs.coeffs_as_vector(), k, new_rhs) << "\n");
        insert_monomials_from_constraint(new_ci);
        m_ci2dep.setx(new_ci, nullptr, nullptr);
        m_old_constraints.insert(new_ci, old_ci);
        m_factored_constraints.insert(new_ci); // don't bother to factor this because it comes from factors already
    }
    
    // call polynomial factorization using the polynomial manager
    // return true if there is a non-trivial factorization
    // need the following:
    // term -> polynomial translation
    // polynomial -> term translation
    // the call to factorization
    bool stellensatz::get_factors(term_offset& t, vector<std::pair<term_offset, unsigned>>& factors) {        
        auto p = to_poly(t);
        polynomial::factors fs(m_pm);
        m_pm.factor(p, fs);
        if (fs.total_factors() <= 1)
            return false;
        unsigned df = fs.distinct_factors();
        for (unsigned i = 0; i < df; ++i) {
            auto f = fs[i];
            auto degree = fs.get_degree(i);
            factors.push_back({to_term(*f), degree});
        }        
        SASSERT(!factors.empty());
        return true;
    }

    polynomial::polynomial_ref stellensatz::to_poly(term_offset const& t) {
        ptr_vector<polynomial::monomial> ms;
        polynomial::scoped_numeral_vector coeffs(m_pm.m());
        rational den(1);
        for (lp::lar_term::ival kv : t.first) {
            auto v = kv.j();
            while (v >= m_pm.num_vars())
                m_pm.mk_var();
            if (m_mon2vars.contains(v)) {
                auto const &vars = m_mon2vars[v];
                ms.push_back(m_pm.mk_monomial(vars.size(), vars.data()));
            } 
            else
                ms.push_back(m_pm.mk_monomial(v));
            den = lcm(den, denominator(kv.coeff()));
        }
        
        for (auto kv : t.first) 
            coeffs.push_back((den * kv.coeff()).to_mpq().numerator());
        coeffs.push_back((den * t.second).to_mpq().numerator());
        ms.push_back(m_pm.mk_monomial(0, nullptr));                
        polynomial::polynomial_ref p(m_pm);
        p = m_pm.mk_polynomial(ms.size(), coeffs.data(), ms.data()); 
        return p;
    }

    stellensatz::term_offset stellensatz::to_term(polynomial::polynomial const& p) {
        term_offset t;
        auto sz = m_pm.size(&p);
        for (unsigned i = 0; i < sz; ++i) {
            auto m = m_pm.get_monomial(&p, i);
            auto const &c = m_pm.coeff(&p, i);
            svector<lpvar> vars;
            for (unsigned j = 0; j < m_pm.size(m); ++j)
                vars.push_back(m_pm.get_var(m, j));
            if (vars.empty())
                t.second += c;
            else 
                t.first.add_monomial(c, add_monomial(vars));            
        }
        return t;
    }

    bool stellensatz::saturate_factors(lp::explanation &ex, vector<ineq> &ineqs) {
        auto indices = m_solver.lra().constraints().indices();
        return all_of(indices, [&](auto ci) { return saturate_factors(ci, ex, ineqs); });      
    }

    bool stellensatz::saturate_factors(lp::constraint_index ci, lp::explanation& ex, vector<ineq>& ineqs) {
        if (m_factored_constraints.contains(ci))
            return true;
        m_factored_constraints.insert(ci);
        auto const &con = m_solver.lra().constraints()[ci];
        if (all_of(con.coeffs(), [&](auto const& cv) { return !m_mon2vars.contains(cv.second); }))
            return true;
        term_offset t;
        // ignore nested terms and nested polynomials..
        for (auto const& [coeff, v] : con.coeffs()) 
            t.first.add_monomial(coeff, v);
        t.second = -con.rhs();
        
        vector<std::pair<term_offset, unsigned>> factors;
        if (!get_factors(t, factors))
            return true;

        vector<rational> values;
        rational prod(1);
        for (auto const & [t, degree] : factors) {
            values.push_back(value(t.first) + t.second);
            prod *= values.back();
            if (degree % 2 == 0)
                prod *= values.back();
        }

        bool is_square = all_of(factors, [&](auto const &f) { return f.second % 2 == 0; });
        if (is_square) {
            auto v = add_term(t);
            bound_justifications bounds;
            add_ineq("squares", bounds, v, lp::lconstraint_kind::GE, rational(0));
        }
        
        IF_VERBOSE(
            3, display_constraint(verbose_stream() << "factored ", ci) << "\n";
            for (auto const &[t, degree] : factors) {
                display(verbose_stream() << "  factor ", t)
                    << " ^ " << degree << " = " << (value(t.first) + t.second) << "\n";
            });

        //
        // p * q >= 0 => (p >= 0 & q >= 0) or (p <= 0 & q <= 0)
        // assert both factors with bound assumptions, and reference to original constraint
        //    p >= 0 <- q >= 0 and 
        //    q >= 0 <- p >= 0
        // the values of p, q in the current interpretation may not satisfy p*q >= 0
        // therefore, assume all but one polynomial satisfies the bound (ignoring multiplicities in this argument).
        // Then derive the bound on the remaining polynomial from the others.
        //
        // prod > 0 and k is <=, <: pick random entry to flip value and sign.
        // prod = 0 and k is <=, >=, pick random 0 entry and assert it
        // prod = 0 and k is >, <, revert 0s from values, recalculate prod, flip random entry if needed.
        //
        auto k = con.kind(); 

        if (prod == 0 && (k == lp::lconstraint_kind::LE || k == lp::lconstraint_kind::GE || k == lp::lconstraint_kind::EQ)) {
            unsigned n = 0, k = factors.size();
            for (unsigned i = 0; i < factors.size(); ++i)
                if (values[i] == 0 && rand() % (++n) == 0)
                    k = i;
            SASSERT(k < factors.size());

            auto v = add_term(factors[k].first);
            bound_justifications bounds;
            bound b(v, lp::lconstraint_kind::EQ, rational(0));
            bounds.push_back(b);
            add_ineq("factor = 0", bounds, v, lp::lconstraint_kind::EQ, rational(0));
            return true;
        }

        if ((prod > 0 && k == lp::lconstraint_kind::GE) || (prod < 0 && k == lp::lconstraint_kind::LE)) {
            // the current evaluation is consistent with inequalities.
            // add factors that enforce the current evaluation.
            for (auto & f : factors)  {               
                if (f.second % 2 == 0)
                    continue;
                bound_justifications bounds;
                auto v = add_term(f.first);
                auto k = m_values[v] > 0 ? lp::lconstraint_kind::GE : lp::lconstraint_kind::LE;
                bounds.push_back(bound(v, k, rational(0)));
                add_ineq("factor >= 0", bounds, v, k, rational(0));
            }
            return true;
        }

        if ((prod > 0 && k == lp::lconstraint_kind::LE) || (prod < 0 && k == lp::lconstraint_kind::GE)) {
            // this is a conflict with the current evaluation. Produce a lemma that blocks
            ex.push_back(ci);
            for (auto &f : factors) {
                auto [t, offset] = f.first;
                auto val = value(t) + offset;
                auto k = val > 0 ? lp::lconstraint_kind::LE : lp::lconstraint_kind::GE;
                ineqs.push_back(ineq(t, k, -offset));
            }
            TRACE(arith, tout << "factor conflict\n";
                  for (auto const &f : factors) display(tout, f.first) << "; "; tout << "\n";
                );
            return false;
        }

        verbose_stream() << "still todo\n";
        return true;
    }

    //
    // add bound assumptions from vars
    // return the sign of the product of vars under the current interpretation.
    // 
    lbool stellensatz::add_bounds(svector<lpvar> const& vars, bound_justifications& bounds) {
        bool sign = false;
        auto &src = c().lra_solver();
        auto &dst = m_solver.lra();
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
            if (src.number_of_vars() > v && src.column_has_lower_bound(v) && src.get_lower_bound(v).is_pos()) {
                bounds.push_back(src.get_column_lower_bound_witness(v));
            } 
            else if (src.number_of_vars() > v && src.column_has_upper_bound(v) && src.get_upper_bound(v).is_neg()) {
                bounds.push_back(src.get_column_upper_bound_witness(v));
                sign = !sign;
            } 
            else if (m_values[v] < 0) {
                add_bound(v, lp::lconstraint_kind::LT, 0);
                sign = !sign;
            } 
            else if (m_values[v] > 0) {
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
        SASSERT(m_values.size() == v);
        m_values.push_back(value(vars));
        return v;
    }

    lpvar stellensatz::add_term(term_offset& t) {
        if (t.second != 0) {            
            auto w = add_var(t.second.is_int()); // or reuse the constant 1 that is already there.
            m_values.push_back(t.second);
            m_solver.lra().add_var_bound(w, lp::lconstraint_kind::GE, t.second);
            m_solver.lra().add_var_bound(w, lp::lconstraint_kind::LE, t.second);
            t.first.add_monomial(rational(1), w);
            t.second = 0;
        }
        auto ti = m_solver.lra().add_term(t.first.coeffs_as_vector(), m_solver.lra().number_of_vars());
        m_values.push_back(value(t.first));
        return ti;
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
            if (c().emons().is_monic_var(v))
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
        for (auto ci : m_solver.lra().constraints().indices()) {
            lp::constraint_index old_ci;
            out << "(" << ci << ") ";
            display_constraint(out, ci);
            if (m_old_constraints.find(ci, old_ci))
                out << " [parent (" << old_ci << ")] ";
            out << "\n";
            if (!m_new_bounds.contains(ci))
                continue;            
            out << "\t<- ";
            display(out, m_new_bounds[ci]);
            out << "\n";
        }
        return out;
    }

    std::ostream& stellensatz::display(std::ostream& out, bound_justifications const& bounds) const {
        for (auto b : bounds) {
            if (std::holds_alternative<u_dependency *>(b)) {
                auto dep = *std::get_if<u_dependency *>(&b);
                unsigned_vector cs;
                c().lra_solver().dep_manager().linearize(dep, cs);
                for (auto c : cs)
                    out << "[o " << c << "] ";  // constraint index from c().lra_solver.
            } else {
                auto [v, k, rhs] = *std::get_if<bound>(&b);
                out << "[j" << v << " " << k << " " << rhs << "] ";
            }
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

    std::ostream& stellensatz::display(std::ostream& out, term_offset const& t) const {
        bool first = true;
        for (auto [v, coeff] : t.first) {
            c().display_coeff(out, first, coeff);
            first = false;
            if (m_mon2vars.contains(v))
                display_product(out, m_mon2vars[v]);
            else
                out << "j" << v;
        }
        if (t.second != 0)
            out << " + " << t.second;
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

    lbool stellensatz::solver::solve(lp::explanation &ex, vector<ineq>& ineqs) {
        while (true) {
            lbool r = solve_lra(ex);
            if (r != l_true)
                return r;
            r = solve_lia(ex);
            if (r != l_true)
                return r;
            unsigned sz = lra_solver->number_of_vars();
            if (update_values())
                return l_true;

            TRACE(arith, s.display(tout));
            if (!s.saturate_factors(ex, ineqs))
                return l_false;
            // s.saturate_constraints(); ?
            if (sz == lra_solver->number_of_vars())
                return l_undef;
        }
    }

    lbool stellensatz::solver::solve_lra(lp::explanation &ex) {
        auto status = lra_solver->find_feasible_solution();;
        if (lra_solver->is_feasible())
            return l_true;
        if (status == lp::lp_status::INFEASIBLE) {
            lra_solver->get_infeasibility_explanation(ex);
            return l_false;
        }
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

    // update m_values
    // return true if the new assignment satisfies the products.
    // return false if value constraints are not satisfied on monomials and there is a false constaint.
    bool stellensatz::solver::update_values() {
        std::unordered_map<lpvar, rational> values;
        lra_solver->get_model(values);
        unsigned sz = lra_solver->number_of_vars();
        for (unsigned i = 0; i < sz; ++i) {
            auto const &value = values[i];
            bool is_int = lra_solver->var_is_int(i); 
            SASSERT(!is_int || value.is_int());
            if (s.m_mon2vars.contains(i)) 
                s.m_values[i] = s.value(s.m_mon2vars[i]);             
            else
                s.m_values[i] = value;
        }
        auto indices = lra_solver->constraints().indices();
        bool satisfies_products = all_of(indices, [&](auto ci) {
            return s.constraint_is_true(ci);});
        s.m_to_refine.reset();
        // check if all constraints are satisfied
        // if they are, then update the model of parent lra solver.
        for (auto ci : indices) 
            s.insert_monomials_from_constraint(ci);
        SASSERT(satisfies_products == s.m_to_refine.empty());
        if (satisfies_products) {
            TRACE(arith, tout << "found satisfying model\n");
            for (auto v : s.m_coi.vars()) 
                s.c().lra_solver().set_column_value(v, lp::impq(s.m_values[v], rational(0)));            
        }
        for (auto j : s.m_to_refine) {
            auto val_j = values[j];
            auto const &vars = s.m_mon2vars[j];
            auto val_vars = s.m_values[j];
            TRACE(arith, tout << "refine j" << j << " " << vars << "\n");
            if (val_j != val_vars)
                s.saturate_basic_linearize(j, val_j, vars, val_vars);
        }
        return satisfies_products;
    }
}
