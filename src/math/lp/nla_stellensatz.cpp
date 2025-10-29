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

  */

#include "util/heap.h"
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
        init_solver();
        saturate_constraints2();
//        saturate_constraints();
        saturate_basic_linearize();
        TRACE(arith, display(tout << "stellensatz after saturation\n"));
        lbool r = m_solver.solve();
        if (r == l_false)
            add_lemma();
        return r;
    }

    void stellensatz::init_solver() {
        m_solver.init();
        m_vars2mon.reset();
        m_mon2vars.reset();
        m_values.reset();
        m_multiplications.reset();
        m_resolvents.reset();
        m_inequality_table.reset();
        m_justifications.reset();
        m_monomials_to_refine.reset();
        m_false_constraints.reset();
        m_factored_constraints.reset();
        m_max_monomial_degree = 0;
        m_coi.init();
        init_vars();
        init_occurs();
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
                // justification: variables in coefficients are always declared before term variable.
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
                add_justification(ci, external_justification(dep));
            }
            if (src.column_has_upper_bound(v)) {
                auto hi_bound = src.get_upper_bound(v);
                SASSERT(hi_bound.y <= 0);
                auto k   = hi_bound.y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;
                auto rhs = hi_bound.x;
                auto dep = src.get_column_upper_bound_witness(v);
                auto ci  = dst.add_var_bound(v, k, rhs);
                add_justification(ci, external_justification(dep));
            }
        }
        m_occurs.reserve(sz);
        for (auto const &[v, vars] : m_mon2vars) 
            m_max_monomial_degree = std::max(m_max_monomial_degree, vars.size());        
    }

    void stellensatz::init_monomial(unsigned mon_var) {
        auto& mon = c().emons()[mon_var];
        svector<lpvar> vars(mon.vars());
        std::sort(vars.begin(), vars.end());
        m_vars2mon.insert(vars, mon_var);
        m_mon2vars.insert(mon_var, vars);
        m_values.push_back(cvalue(vars));
    }

    //
    // convert a conflict from m_solver.lra()/lia() into
    // a conflict for c().lra_solver()
    // 1. constraints that are obtained by multiplication are explained from the original constraint
    // 2. bounds justifications are added as justifications to the lemma.
    // 
    void stellensatz::add_lemma() {
        lp::explanation const &ex1 = m_solver.ex();
        vector<ineq> const &ineqs = m_solver.ineqs();
        TRACE(arith, display(tout); display_lemma(tout, ex1, ineqs));
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
    // a constraint can be explained by a set of bounds used as justifications
    // and by an original constraint.
    // 
    void stellensatz::explain_constraint(lemma_builder &new_lemma, lp::constraint_index ci, lp::explanation &ex) {
        if (m_constraints_in_conflict.contains(ci))
            return;
        m_constraints_in_conflict.insert(ci);
        auto just = m_justifications.get(ci);
        if (just == nullptr)
            return;
        auto add_ineq = [&](bound_assumption const& i) {
            auto [j, k, rhs] = i;
            k = negate(k);
            if (m_solver.lra().var_is_int(j)) {
                if (k == lp::lconstraint_kind::GT) {
                    rhs += 1;
                    k = lp::lconstraint_kind::GE;
                }
                if (k == lp::lconstraint_kind::LT) {
                    rhs -= 1;
                    k = lp::lconstraint_kind::LE;
                }
            }
            new_lemma |= ineq(j, k, rhs);
        };
        auto &b = *just;
        if (std::holds_alternative<external_justification>(b)) {
            auto dep = *std::get_if<external_justification>(&b);
            m_solver.lra().push_explanation(dep.dep, ex);
        } 
        else if (std::holds_alternative<internal_justification>(b)) {
            auto c = *std::get_if<internal_justification>(&b);
            svector<lp::constraint_index> cis;
            m_solver.lra().dep_manager().linearize(c.dep, cis);
            for (auto ci : cis)
                explain_constraint(new_lemma, ci, ex);
        } 
        else if (std::holds_alternative<multiplication_justification>(b)) {
            auto m = *std::get_if<multiplication_justification>(&b);
            explain_constraint(new_lemma, m.ci, ex);
            for (auto const &i : m.assumptions)
                add_ineq(i);
        } 
        else if (std::holds_alternative<resolvent_justification>(b)) {
            auto m = *std::get_if<resolvent_justification>(&b);
            explain_constraint(new_lemma, m.ci1, ex);
            explain_constraint(new_lemma, m.ci2, ex);
            for (auto const &i : m.assumptions)
                add_ineq(i);
        } 
        else if (std::holds_alternative<bound_assumptions>(b)) {
            auto ba = *std::get_if<bound_assumptions>(&b);
            for (auto const &i : ba.bounds)
                add_ineq(i);            
        } 
        else
            UNREACHABLE();
    }

    //
    // Emulate linearization within stellensatz to enforce simple axioms.
    // Incremental linearization in the main procedure produces new atoms that are pushed to lemmas
    // Here, it creates potentially new atoms from bounds justifications, but it checks linear 
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
    // the equation x*y = 0 is asserted with justification x = 0
    // x > 0 & y < 0 => x*y < 0
    // 
    void stellensatz::saturate_signs(lpvar j, rational const& val_j, svector<lpvar> const& vars,
        rational const& val_vars) {
        if (val_vars == 0 && val_j != 0) {
            bound_assumptions bounds{"signs = 0"};        
            lbool sign = add_bounds(vars, bounds.bounds);
            VERIFY(sign == l_undef);
            add_ineq(bounds, j, lp::lconstraint_kind::EQ, rational(0));
        } 
        else if (val_j <= 0 && 0 < val_vars) {
            bound_assumptions bounds{"signs > 0"};   
            lbool sign = add_bounds(vars, bounds.bounds);
            VERIFY(sign == l_false);
            add_ineq(bounds, j, lp::lconstraint_kind::GT, rational(0));
        } 
        else if (val_j >= 0 && 0 > val_vars) {
            bound_assumptions bounds{"signs < 0"};
            lbool sign = add_bounds(vars, bounds.bounds);
            VERIFY(sign == l_true);
            add_ineq(bounds, j, lp::lconstraint_kind::LT, rational(0));
        }
    }

    //
    // Unit axioms:
    // x = -1 => x*y = -y
    // x = 1 => x*y = y
    //
    void stellensatz::saturate_units(lpvar j, svector<lpvar> const &vars) {
        lpvar non_unit = lp::null_lpvar;
        int sign = 1;
        for (auto v : vars) {
            if (c().val(v) == 1)
                continue;
            if (c().val(v) == -1) {
                sign = -sign;
                continue;
            }
            if (non_unit != lp::null_lpvar)
                return;
            non_unit = v;
        }
        bound_assumptions bounds{"units"};
        for (auto v : vars) {
            if (m_values[v] == 1 || m_values[v] == -1) {
                bound_assumption b(v, lp::lconstraint_kind::EQ, m_values[v]);
                bounds.bounds.push_back(b);
            }
        }
        // assert j = +/- non_unit
        lp::lar_term lhs;
        lhs.add_monomial(rational(1), j);
        if (non_unit != lp::null_lpvar) {
            lhs.add_monomial(rational(-sign), non_unit);
            add_ineq(bounds, lhs, lp::lconstraint_kind::GE, rational(0));
            add_ineq(bounds, lhs, lp::lconstraint_kind::LE, rational(0));
        } else {
            add_ineq(bounds, lhs, lp::lconstraint_kind::GE, rational(sign));
            add_ineq(bounds, lhs, lp::lconstraint_kind::LE, rational(sign));
        }
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
        if (c().val(x) == 0 || c().val(y) == 0)
            return;
        if (abs(c().val(x)) <= 1 && abs(c().val(y)) <= 1)
            return;
        saturate_monotonicity(j, val_j, x, y);
        saturate_monotonicity(j, val_j, y, x);
    }

    void stellensatz::saturate_monotonicity(lpvar j, rational const &val_j, lpvar x, lpvar y) {
        auto valx = c().val(x);
        auto valy = c().val(y);
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
        bound_assumptions bounds{"monotonicity"};
        bound_assumption b1(x, sign_x < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::GT, rational(sign_x));
        bound_assumption b2(y, sign_y < 0 ? lp::lconstraint_kind::LT : lp::lconstraint_kind::GT, rational(0));
        bounds.bounds.push_back(b1);
        bounds.bounds.push_back(b2);
        lp::lar_term lhs;
        lhs.add_monomial(rational(sign_x * sign_y), j);
        lhs.add_monomial(rational(-sign_y), y);
        add_ineq(bounds, lhs, lp::lconstraint_kind::GT, rational(0));
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
        bound_assumptions bounds{"squares"};
        add_ineq(bounds, j, lp::lconstraint_kind::GE, rational(0));
    }

    rational stellensatz::cvalue(lp::lar_term const &t) const {
        rational r(0);
        for (auto cv : t)
            r += c().val(cv.j()) * cv.coeff();
        return r;
    }

    rational stellensatz::mvalue(lp::lar_term const &t) const {
        rational r(0);
        for (auto cv : t)
            r += m_values[cv.j()] * cv.coeff();
        return r;
    }

    rational stellensatz::cvalue(svector<lpvar> const &prod) const {
        rational p(1);
        for (auto v : prod)
            p *= c().val(v);
        return p;
    }

    rational stellensatz::mvalue(svector<lpvar> const &prod) const {
        rational p(1);
            for (auto v : prod)
                p *= m_values[v];
        return p;
    }

    void stellensatz::gcd_normalize(vector<std::pair<rational, lpvar>> &t, lp::lconstraint_kind k, rational &rhs) {
        rational d(1);
        for (auto &[c,v] : t)
            d = lcm(d, denominator(c));
        d = lcm(d, denominator(rhs));
        if (d != 1) {
            for (auto &[c, v] : t)
                c *= d;
            rhs *= d;
        }
        rational g(0);
        for (auto &[c, v] : t)
            g = gcd(g, c);
        bool is_int = true;
        for (auto &[c, v] : t)
            is_int &= m_solver.lra().var_is_int(v);
        if (!is_int)
            g = gcd(g, rhs);
        if (g == 1 || g == 0)
            return;
        switch (k) {
        case lp::lconstraint_kind::GE:
            for (auto &[c, v] : t)
                c /= g;
            rhs /= g;
            rhs = ceil(rhs);
            break;
        case lp::lconstraint_kind::GT:
            for (auto &[c, v] : t)
                c /= g;
            if (is_int)
                rhs += 1;
            rhs /= g;
            rhs = ceil(rhs);
            break;
        case lp::lconstraint_kind::LE:
            for (auto &[c, v] : t)
                c /= g;
            rhs /= g;
            rhs = floor(rhs);
            break;
        case lp::lconstraint_kind::LT:
            for (auto &[c, v] : t)
                c /= g;
            if (is_int)
                rhs -= 1;
            rhs /= g;
            rhs = floor(rhs);
            break;
        case lp::lconstraint_kind::EQ:
        case lp::lconstraint_kind::NE:
            if (!divides(g, rhs))
                break;
            for (auto &[c, v] : t)
                c /= g;
            rhs /= g;
            break;
        }    
    }

    bool stellensatz::is_new_inequality(vector<std::pair<rational, lpvar>> lhs, lp::lconstraint_kind k,
                                        rational const &rhs) {
        std::stable_sort(lhs.begin(), lhs.end(),
                         [](std::pair<rational, lpvar> const &a, std::pair<rational, lpvar> const &b) {
                             return a.second < b.second;
                         });
        ineq_sig sig{lhs, k, rhs};
        if (m_inequality_table.contains(sig))
            return false;
        m_inequality_table.insert(sig);
        return true;
    }

    lp::constraint_index stellensatz::add_ineq( 
        justification const& just, lp::lar_term & t, lp::lconstraint_kind k,
        rational const & rhs_) {
        rational rhs(rhs_);
        auto coeffs = t.coeffs_as_vector();
        gcd_normalize(coeffs, k, rhs);

        if (!is_new_inequality(coeffs, k, rhs))
            return lp::null_ci;

        SASSERT(!coeffs.empty());
        auto ti = m_solver.lra().add_term(coeffs, m_solver.lra().number_of_vars());
        m_occurs.reserve(m_solver.lra().number_of_vars());
        m_values.push_back(mvalue(t));
        auto new_ci = m_solver.lra().add_var_bound(ti, k, rhs);
        TRACE(arith, display(tout, just) << "\n");
        SASSERT(m_values.size() - 1 == ti);
        add_justification(new_ci, just);
        init_occurs(new_ci);
        return new_ci;
    }

    lp::constraint_index stellensatz::add_ineq(justification const& just, lpvar j, lp::lconstraint_kind k,
        rational const& rhs) {
        auto new_ci = m_solver.lra().add_var_bound(j, k, rhs);
        add_justification(new_ci, just);
        init_occurs(new_ci);
        return new_ci;
    }

    void stellensatz::init_occurs() {
        m_occurs.reset();
        m_occurs.reserve(c().lra_solver().number_of_vars());
        for (auto ci : m_solver.lra().constraints().indices())
            init_occurs(ci);        
    }

    void stellensatz::init_occurs(lp::constraint_index ci) {
        if (ci == lp::null_ci)
            return;
        auto const &con = m_solver.lra().constraints()[ci];
        for (auto cv : con.lhs()) {
            auto v = cv.j();
            if (is_mon_var(v)) {
                for (auto w : m_mon2vars[v]) 
                    m_occurs[w].push_back(ci);                
            }
            else 
                m_occurs[v].push_back(ci);
        }
    }

    // record new monomials that are created and recursively down-saturate with respect to these.
    // this is a simplistic pass
    void stellensatz::saturate_constraints() {
        auto &constraints = m_solver.lra().constraints();
        for (auto ci : constraints.indices()) 
            insert_monomials_from_constraint(ci);                    


        unsigned initial_false_constraints = m_false_constraints.size();
        for (unsigned it = 0; it < m_false_constraints.size(); ++it) {
            if (it > 10 * initial_false_constraints)
                break;
            auto ci1 = m_false_constraints[it];
            auto const &con = constraints[ci1];
            auto [j, coeff] = find_max_lex_monomial(con.lhs());
            if (j == lp::null_lpvar)
                continue;
            auto vars = m_mon2vars[j];
            if (vars.size() > m_max_monomial_degree)
                continue;

            for (auto v : vars) {
                if (v >= m_occurs.size())
                    continue;
                for (unsigned cidx = 0; cidx < m_occurs[v].size(); ++cidx) {
                    auto ci2 = m_occurs[v][cidx];
                    if (ci1 == ci2)
                        continue;
                    for (auto const &cv2 : constraints[ci2].lhs()) {
                        auto u = cv2.j();
                        if (u == v)
                            resolve(j, ci1, saturate_multiply(ci2, j, u));
                        else if (is_mon_var(u) && is_subset(m_mon2vars[u], vars))
                            resolve(j, ci1, saturate_multiply(ci2, j, u));
                    }
                }
            }
        }
        IF_VERBOSE(1, verbose_stream() << "stsz " << initial_false_constraints << " -> " << m_false_constraints.size()
                                       << " false constraints\n");
        IF_VERBOSE(5,
                   c().lra_solver().display(verbose_stream() << "original\n");
                   c().display(verbose_stream());
                   display(verbose_stream() << "saturated\n"));
    }

    void stellensatz::saturate_constraints2() {
        // pick lex leading monomial mx in to_refine, with x being leading variable and with maximal degree d.
        // find lub and glb constraints with respect to mx, and subsets of mx, and superset of x.
        // glb/lub are computed based on coefficents and divisions of remaing of polynomials with current model.
        // resolve glb with all upper bounds and resolve lub with all lower bounds.
        // mark polynomias used for resolvents as processed.
        // repeat until to_refine is empty.

        // Saturation can be called repeatedly for different glb/lub solutions by the LIA solver.
        // Eventually it can saturate to full pseudo-elimination of mx.
        // or better: a conflict or a solution.

        IF_VERBOSE(3, verbose_stream() << "saturate2\n");
        auto &constraints = m_solver.lra().constraints();
        for (auto ci : constraints.indices())
            insert_monomials_from_constraint(ci);

        struct lt {
            stellensatz &s;
            lt(stellensatz &s) : s(s) {}
            bool operator()(lpvar a, lpvar b) const {
                auto const &v1 = s.m_mon2vars[a];
                auto const &v2 = s.m_mon2vars[b];
                return std::lexicographical_compare(v2.begin(), v2.end(), v1.begin(), v1.end());
            }
        };
        unsigned max_index = m_monomials_to_refine.max_var() + 1;

        lt lt_op(*this);
        heap<lt> to_refine(max_index, lt_op);
        for (auto j : m_monomials_to_refine)
            to_refine.insert(j);

        while (!to_refine.empty()) {
            lpvar j = to_refine.erase_min();            
            unsigned sz = m_monomials_to_refine.size();
            TRACE(arith, tout << "refining " << m_mon2vars[j] << " sz " << sz << "\n");
            eliminate(j);
            for (unsigned i = sz; i < m_monomials_to_refine.size(); ++i) {
                auto e = m_monomials_to_refine.elem_at(i);
                IF_VERBOSE(2, display_product(verbose_stream() << "next monomial  ", m_mon2vars[j]) << " >= ";
                display_product(verbose_stream(), m_mon2vars[e]) << "\n");
                SASSERT(!lt_op(e, j));
                to_refine.reserve(e + 1);
                to_refine.insert(e);
            }
        }
    }

    void stellensatz::eliminate(lpvar mi) {
        auto const& vars = m_mon2vars[mi];
        if (vars.size() > m_max_monomial_degree)
            return;
        auto &constraints = m_solver.lra().constraints();

        unsigned_vector los, his;
        uint_set visited;
        lp::constraint_index lo_ci = lp::null_ci, hi_ci = lp::null_ci;
        bool lo_strict = false, hi_strict = false;
        rational lo_value, hi_value;
        unsigned lo_n = 0, hi_n = 0;
        svector<lpvar> quot;
        for (auto v : vars) {
            for (auto ci : m_occurs[v]) {
                if (visited.contains(ci))
                    continue;
                visited.insert(ci);
                auto const &con = constraints[ci];
                auto [j, coeff] = find_max_lex_term(con.lhs());
                // verbose_stream() << "lex-max " << j << " " << coeff << " vars: " << vars << ":= j" << mi << "\n";
                // display_constraint(verbose_stream() << ci << ": ", ci) << "\n";
                // filter out constraints with lex-leading monomials that can resolve with vars
                if (j == lp::null_lpvar)
                    continue;
                if (!vars.contains(j) && (!is_mon_var(j) || !is_subset_eq(m_mon2vars[j], vars)))
                    continue;
                auto [bound, is_lower, is_strict] = compute_bound(vars, quot, j, coeff, ci);
                if (is_lower) {
                    if (lo_ci == lp::null_ci || lo_value < bound || (lo_value == bound && !lo_strict && is_strict))
                        lo_value = bound, lo_strict = is_strict, lo_ci = ci;
                    else if (lo_ci != lp::null_ci && lo_value == bound && (is_strict == lo_strict) &&
                             random(++lo_n) == 0)
                        lo_ci = ci;
                    los.push_back(ci);
                }
                else {
                    if (hi_ci == lp::null_ci || hi_value > bound || (hi_value == bound && !hi_strict && is_strict))
                        hi_value = bound, hi_strict = is_strict, hi_ci = ci;
                    else if (hi_ci != lp::null_ci && hi_value == bound && (is_strict == hi_strict) &&
                             random(++hi_n) == 0)
                        hi_ci = ci;
                    his.push_back(ci);
                }
                // punt on equality constraints for now
            }
        }
        TRACE(arith, tout << "eliminate " << m_mon2vars[mi] << " los: " << los << " his: " << his << "\n");
        if (los.empty() || his.empty())
            return;
        IF_VERBOSE(3, verbose_stream() << "lo " << los << " hi " << his << "\n");
        for (auto lo : los) 
            ext_resolve(mi, lo, hi_ci);
        for (auto hi : his)
            ext_resolve(mi, lo_ci, hi);
    }

    void stellensatz::ext_resolve(lpvar mi, lp::constraint_index lo, lp::constraint_index hi) {
        resolvent r = {lo, hi, mi};
        if (m_resolvents.contains(r))
            return;
        m_resolvents.insert(r);
        svector<lpvar> quot_lo, quot_hi;
        auto &constraints = m_solver.lra().constraints();
        auto const &vars = m_mon2vars[mi];
        auto const &con_lo = constraints[lo];
        auto [j_lo, coeff_lo] = find_max_lex_term(con_lo.lhs());
        auto [bound_lo, is_lo, lo_is_strict] = compute_bound(vars, quot_lo, j_lo, coeff_lo, lo);
        auto const &con_hi = constraints[hi];
        auto [j_hi, coeff_hi] = find_max_lex_term(con_hi.lhs());
        auto [bound_hi, is_lo2, hi_is_strict] = compute_bound(vars, quot_hi, j_hi, coeff_hi, hi);

        // lo.lhs() ~ lo.rhs() - a lower bound for mi
        // hi.lhs() ~ hi.rhs() - an upper bound for mi
        // 
        SASSERT(is_lo);
        SASSERT(!is_lo2);
        bool is_strict = lo_is_strict || hi_is_strict;
        int lo_sign = (con_lo.kind() == lp::lconstraint_kind::LE || con_lo.kind() == lp::lconstraint_kind::LT) ? 1 : -1;
        if (coeff_lo < 0)
            lo_sign = -lo_sign;
        int hi_sign = (con_hi.kind() == lp::lconstraint_kind::LE || con_hi.kind() == lp::lconstraint_kind::LT) ? 1 : -1;
        if (coeff_hi < 0)
            hi_sign = -hi_sign;       
        lp::lar_term lhs;
        rational rhs;
        for (auto const& cv : con_lo.lhs()) {
            auto j = mk_monomial(quot_lo, cv.j());
            auto coeff = lo_sign * cv.coeff() / coeff_lo;
            lhs.add_monomial(coeff, j);
        }
        if (quot_lo.empty()) {
            auto coeff = lo_sign * con_lo.rhs() / coeff_lo;
            rhs += coeff;
        }
        else if (con_lo.rhs() != 0) {
            auto j = mk_monomial(quot_lo);
            auto coeff = -lo_sign * con_lo.rhs() / coeff_lo;
            lhs.add_monomial(coeff, j);
        }
        for (auto const &cv : con_hi.lhs()) {
            auto j = mk_monomial(quot_hi, cv.j());
            auto coeff = hi_sign * cv.coeff() / coeff_hi;
            lhs.add_monomial(coeff, j);
        }
        if (quot_hi.empty()) {
            auto coeff = hi_sign * con_hi.rhs() / coeff_hi;
            rhs += coeff;
        }
        else if (con_hi.rhs() != 0) {
            auto j = mk_monomial(quot_hi);
            auto coeff = -hi_sign * con_hi.rhs() / coeff_hi;
            lhs.add_monomial(coeff, j);
        }

        IF_VERBOSE(3, verbose_stream() << "resolve on " << m_mon2vars[mi] << " lo: " << lo << " hi: " << hi << "\n";
                   display_constraint(verbose_stream() << lo << ": ", lo) << "\n";
                   display_constraint(verbose_stream() << hi << ": ", hi) << "\n";
                   verbose_stream() << "rhs " << con_lo.rhs() << " " << con_hi.rhs() << "\n");
        if (lhs.size() == 0) {
            IF_VERBOSE(2, verbose_stream() << rhs << " " << "empty\n");
            return;
        }
        resolvent_justification just(r);
        add_bounds(quot_lo, just.assumptions);
        add_bounds(quot_hi, just.assumptions);

        // lo-bound: (quot_lo * p_lo - quot_lo * rhs_lo) / coeff_lo
        //           <= (quot_hi * p_hi - quot_hi * rhs_hi) / coeff_hi
        // mul(quot_lo, con_lo.lhs())/coeff_lo - mul(quot_lo, con_lo.rhs())/coeff_lo ;
        lp::lconstraint_kind k = is_strict ? lp::lconstraint_kind::LT : lp::lconstraint_kind::LE;

        auto new_ci = add_ineq(just, lhs, k, rhs);
        if (new_ci == lp::null_ci)
            return;
        insert_monomials_from_constraint(new_ci);
        IF_VERBOSE(3, display_constraint(verbose_stream() << new_ci << ": ", new_ci) << "\n");
    }

    std::tuple<rational, bool, bool> stellensatz::compute_bound(svector<lpvar> const& vars, svector<lpvar>& quot, lpvar j, rational const& coeff, lp::constraint_index ci) {
        auto const &con = m_solver.lra().constraints()[ci];
        quot.reset();
        quot.append(vars);          
        if (is_mon_var(j)) {
            auto const &vars2 = m_mon2vars[j];
            SASSERT(is_subset_eq(vars2, vars));
            for (auto v : vars2)
                quot.erase(v);    
        }
        else {
            SASSERT(vars.contains(j));
            quot.erase(j);
        }
        rational alpha(1);
        for (auto v : quot)
            alpha *= m_values[v];
        if (alpha == 0)
            return {rational::zero(), false, false};
        SASSERT(alpha != 0);
        int flip = (alpha >= 0) != (coeff >= 0);
        IF_VERBOSE(3, verbose_stream() << "alpha " << alpha << " coeff " << coeff << " flip: " << flip << " " << con.kind() << "\n");
        IF_VERBOSE(3, display_constraint(verbose_stream(), ci) << "\n");
        // quot * j = vars
        // 
        // coeff * j + p <= r
        // coeff * j <= r - p
        // coeff * quot * j <= alpha * (r - p)
        // quot * j <= alpha * (r - p) / coeff    if coeff > 0
        // 
        rational r_val = alpha * (con.rhs() - mvalue(con.lhs())) / coeff;       
        switch (con.kind()) {
        case lp::lconstraint_kind::LE:
            return {r_val, flip, false};
        case lp::lconstraint_kind::LT: 
            return {r_val, flip, true};
        case lp::lconstraint_kind::GE: 
            return {r_val, !flip, false};
        case lp::lconstraint_kind::GT: 
            return {r_val, !flip, true};
        case lp::lconstraint_kind::EQ: 
            NOT_IMPLEMENTED_YET(); 
            return {r_val, false, false};
        default: 
            NOT_IMPLEMENTED_YET(); 
            break;
        }
        return {r_val, false, false};
    }

    std::pair<lpvar, rational> stellensatz::find_max_lex_monomial(lp::lar_term const &t) const {
        lpvar result = lp::null_lpvar;
        rational r(0);
        for (auto const &cv : t) {
            auto j = cv.j();
            if (!is_mon_var(j))
                continue;
            auto const &vars = m_mon2vars[j];
            if (result == lp::null_lpvar)
                result = j, r = cv.coeff();
            else if (std::lexicographical_compare(m_mon2vars[result].begin(), m_mon2vars[result].end(), vars.begin(),
                                                  vars.end()))
                result = j, r = cv.coeff();
        }
        return {result, r};
    }

    std::pair<lpvar, rational> stellensatz::find_max_lex_term(lp::lar_term const& t) const {
        lpvar result = lp::null_lpvar;
        rational r(0);
        for (auto const &cv : t) {
            auto j = cv.j();
            if (result == lp::null_lpvar)
                result = j, r = cv.coeff();
            else if (!is_mon_var(j)) {
                if (!is_mon_var(result) && j > result)
                    result = j, r = cv.coeff();
            } 
            else if (is_mon_var(result)) {
                auto const &vars = m_mon2vars[j];
                if (std::lexicographical_compare(m_mon2vars[result].begin(), m_mon2vars[result].end(), vars.begin(),
                                                 vars.end()))
                    result = j, r = cv.coeff();
            }
        }
        return {result, r};
    }

    bool stellensatz::is_subset(svector<lpvar> const &a, svector<lpvar> const &b) const {
        return a.size() < b.size() && is_subset_eq(a, b);
    };

    bool stellensatz::is_subset_eq(svector<lpvar> const &a, svector<lpvar> const &b) const {
        if (a.size() > b.size())
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

    bool stellensatz::is_lex_greater(svector<lpvar> const& a, svector<lpvar> const& b) const {
       if (a.size() != b.size())
            return a.size() > b.size();
        for (unsigned i = a.size(); i-- > 0;) {
            if (a[i] != b[i])
                return a[i] > b[i];
        }
        return false;
    }

    void stellensatz::resolve(lpvar j, lp::constraint_index ci1, lp::constraint_index ci2) {
        // resolution of saturate_constraint could swap inequality,
        // so the premise of is_resolveable may not hold.
        auto const &constraints = m_solver.lra().constraints();
        if (!constraints.valid_index(ci1))
            return;
        if (!constraints.valid_index(ci2))
            return;
        auto const &con1 = constraints[ci1];
        auto const &con2 = constraints[ci2];
        for (auto const &cv : con1.lhs())
            if (is_mon_var(cv.j()) && m_mon2vars[cv.j()].size() > m_max_monomial_degree)
                return;
        for (auto const &cv : con2.lhs())
            if (is_mon_var(cv.j()) && m_mon2vars[cv.j()].size() > m_max_monomial_degree)
                return;

        auto k1 = con1.kind();
        auto k2 = con2.kind();
        auto const &lhs1 = con1.lhs();
        auto const &lhs2 = con2.lhs();
        auto const &c1 = lhs1.get_coeff(j);
        auto const &c2 = lhs2.get_coeff(j);
        rational mul1, mul2;
        bool is_le1 = (k1 == lp::lconstraint_kind::LE || k1 == lp::lconstraint_kind::LT);
        bool is_le2 = (k2 == lp::lconstraint_kind::LE || k2 == lp::lconstraint_kind::LT);
        bool is_strict = (k1 == lp::lconstraint_kind::LT || k2 == lp::lconstraint_kind::LT);
        if (k1 == lp::lconstraint_kind::EQ) {
            mul1 = (c1 > 0 ? -1 : 1) * c2;
            mul2 = (c1 > 0 ? c1 : -c1);
        }
        else if (k2 == lp::lconstraint_kind::EQ) {
            mul1 = (c2 > 0 ? c2 : -c2);
            mul2 = (c2 > 0 ? -1 : 1) * c1;
        }
        else if (is_le1 == is_le2) {
            if (c1.is_pos() == c2.is_pos())
                return;
            mul1 = abs(c2);
            mul2 = abs(c1);
        }
        else {
            if (c1.is_pos() != c2.is_pos())
                return;
            mul1 = abs(c2);
            mul2 = -abs(c1);
        }
        auto lhs = mul1 * lhs1 + mul2 * lhs2;
        auto rhs = mul1 * con1.rhs() + mul2 * con2.rhs();
        if (lhs.size() == 0) {  // trivial conflict, will be found using LIA
            IF_VERBOSE(0, verbose_stream() << "trivial conflict\n");
            TRACE(arith, tout << "trivial conflict\n");
            return;
        }
        resolvent_justification r = {ci1, ci2, j};
        auto new_ci = add_ineq(r, lhs, k1, rhs);
        if (new_ci == lp::null_ci)
            return;
        insert_monomials_from_constraint(new_ci);
        IF_VERBOSE(3, verbose_stream() << "resolve on " << m_mon2vars[j] << " c1: " << c1 << " c2: " << c2 << "\n";
                   display_constraint(verbose_stream(), ci1) << "\n";
                   display_constraint(verbose_stream(), ci2) << "\n";
                   display_constraint(verbose_stream(), new_ci) << "\n");
    }

    // multiply by remaining vars
    lp::constraint_index stellensatz::saturate_multiply(lp::constraint_index old_ci, lpvar mi, lpvar j2) {
        multiplication m = {old_ci, mi, j2};
        if (m_multiplications.contains(m))
            return lp::null_ci;
        m_multiplications.insert(m);

        lp::lar_base_constraint const& con = m_solver.lra().constraints()[old_ci];
        auto const& lhs = con.lhs();
        auto const& rhs = con.rhs();
        auto k = con.kind();
        if (k == lp::lconstraint_kind::NE || k == lp::lconstraint_kind::EQ)
            return lp::null_ci;  // not supported


        // xs is a proper subset of vars in mi
        svector<lpvar> vars(m_mon2vars[mi]);
        if (is_mon_var(j2)) {
            auto const &xs = m_mon2vars[j2];
            for (auto x : xs) {
                SASSERT(vars.contains(x));
                vars.erase(x);
            }
            SASSERT(!vars.empty());
            SASSERT(vars.size() + xs.size() == m_mon2vars[mi].size());
        } 
        else {
            SASSERT(vars.contains(j2));
            vars.erase(j2);
        }

        multiplication_justification just{old_ci, mi, j2}; 
        // compute bounds constraints and sign of vars
        lbool sign = add_bounds(vars, just.assumptions);

        #if 1
        // just skip vacuous lemmas?
        if (l_undef == sign)
            return lp::null_ci;
        #endif

        lp::lar_term new_lhs;
        rational new_rhs(rhs);
        for (auto const & cv : lhs) {
            unsigned old_sz = vars.size();
            if (is_mon_var(cv.j()))
                vars.append(m_mon2vars[cv.j()]);
            else
                vars.push_back(cv.j());
            lpvar new_monic_var = mk_monomial(vars);
            new_lhs.add_monomial(cv.coeff(), new_monic_var);
            vars.shrink(old_sz);
        }
        if (rhs != 0) {
            lpvar new_monic_var = mk_monomial(vars);
            new_lhs.add_monomial(-rhs, new_monic_var);
            new_rhs = 0;
        }

        if (sign == l_undef) {
            switch (k) {
            case lp::lconstraint_kind::LT: k = lp::lconstraint_kind::LE; break;
            case lp::lconstraint_kind::GT: k = lp::lconstraint_kind::GE; break;
            default: break;
            }
        }


        if (sign == l_true) 
            k = swap_side(k);       

        auto new_ci = add_ineq(just, new_lhs, k, new_rhs);
        if (new_ci == lp::null_ci)
            return lp::null_ci;
        IF_VERBOSE(4, display_constraint(verbose_stream(), old_ci) << " -> ";
                   display_constraint(verbose_stream(), new_lhs.coeffs_as_vector(), k, new_rhs) << "\n");
        //insert_monomials_from_constraint(new_ci);
        m_factored_constraints.insert(new_ci); // don't bother to factor this because it comes from factors already
        return new_ci;
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
            if (is_mon_var(v)) {
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
                t.first.add_monomial(c, mk_monomial(vars));            
        }
        return t;
    }

    bool stellensatz::saturate_factors() {
        return true;
        auto indices = m_solver.lra().constraints().indices();
        return all_of(indices, [&](auto ci) { return saturate_factors(ci); });      
    }

    bool stellensatz::saturate_factors(lp::constraint_index ci) {
        if (m_factored_constraints.contains(ci))
            return true;
        m_factored_constraints.insert(ci);
        auto const &con = m_solver.lra().constraints()[ci];
        if (all_of(con.lhs(), [&](auto const& cv) { return !is_mon_var(cv.j()); }))
            return true;
        term_offset t;
        // ignore nested terms and nested polynomials..
        for (auto const& cv : con.lhs()) 
            t.first.add_monomial(cv.coeff(), cv.j());
        t.second = -con.rhs();
        
        vector<std::pair<term_offset, unsigned>> factors;
        if (!get_factors(t, factors))
            return true;

        vector<rational> values;
        rational prod(1);
        for (auto const & [t, degree] : factors) {
            values.push_back(cvalue(t.first) + t.second);
            prod *= values.back();
            if (degree % 2 == 0)
                prod *= values.back();
        }

        bool is_square = all_of(factors, [&](auto const &f) { return f.second % 2 == 0; });
        if (is_square) {
            auto v = mk_term(t);
            bound_assumptions bounds{"square >= 0"};                
            add_ineq(bounds, v, lp::lconstraint_kind::GE, rational(0));
        }
        
        IF_VERBOSE(
            3, display_constraint(verbose_stream() << "factored ", ci) << "\n";
            for (auto const &[t, degree] : factors) {
                display(verbose_stream() << "  factor ", t)
                    << " ^ " << degree << " = " << (cvalue(t.first) + t.second) << "\n";
            });

        //
        // p * q >= 0 => (p >= 0 & q >= 0) or (p <= 0 & q <= 0)
        // assert both factors with bound justifications, and reference to original constraint
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
                if (values[i] == 0 && random(++n) == 0)
                    k = i;
            SASSERT(k < factors.size());

            auto v = mk_term(factors[k].first);
            bound_assumptions bounds{"factor = 0"};        
            bound_assumption b(v, lp::lconstraint_kind::EQ, rational(0));
            bounds.bounds.push_back(b);
            add_ineq(bounds, v, lp::lconstraint_kind::EQ, rational(0));
            return true;
        }

        if ((prod > 0 && k == lp::lconstraint_kind::GE) || (prod < 0 && k == lp::lconstraint_kind::LE)) {
            // the current evaluation is consistent with inequalities.
            // add factors that enforce the current evaluation.
            for (auto & f : factors)  {               
                if (f.second % 2 == 0)
                    continue;
                bound_assumptions bounds{"factor >= 0"};
                auto v = mk_term(f.first);
                auto k = m_values[v] > 0 ? lp::lconstraint_kind::GE : lp::lconstraint_kind::LE;
                bounds.bounds.push_back(bound_assumption(v, k, rational(0)));
                add_ineq(bounds, v, k, rational(0));
            }
            return true;
        }

        if ((prod > 0 && k == lp::lconstraint_kind::LE) || (prod < 0 && k == lp::lconstraint_kind::GE)) {
            return true;
            // this is a conflict with the current evaluation. Produce a lemma that blocks
            // TODO, need to check if variables use fresh monomials
            m_solver.ex().push_back(ci);
            for (auto &f : factors) {
                auto [t, offset] = f.first;
                auto val = cvalue(t) + offset;
                auto k = val > 0 ? lp::lconstraint_kind::LE : lp::lconstraint_kind::GE;
                m_solver.ineqs().push_back(ineq(t, k, -offset));
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
    // add bound justifications from vars
    // return the sign of the product of vars under the current interpretation.
    // 
    lbool stellensatz::add_bounds(svector<lpvar> const& vars, vector<bound_assumption>& bounds) {
        bool sign = false;
        auto &src = c().lra_solver();
        auto &dst = m_solver.lra();
        auto add_bound = [&](lpvar v, lp::lconstraint_kind k, int r) {
            bound_assumption b(v, k, rational(r));
            bounds.push_back(b);
        };
        for (auto v : vars) {
            if (m_values[v] != 0)
                continue;
            add_bound(v, lp::lconstraint_kind::EQ, 0); 
            return l_undef;
        }
        for (auto v : vars) {
            if (m_values[v] < 0) {
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
    lpvar stellensatz::mk_monomial(svector<lpvar> const& vars) {
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
        m_values.push_back(cvalue(vars));
        return v;
    }

    lpvar stellensatz::mk_monomial(svector<lp::lpvar> const &_vars, lp::lpvar j) {
        svector<lpvar> vars(_vars);
        if (is_mon_var(j))
            vars.append(m_mon2vars[j]);
        else
            vars.push_back(j);
        return mk_monomial(vars);
    }

    lpvar stellensatz::mk_term(term_offset& t) {
        if (t.second != 0) {            
            auto w = add_var(t.second.is_int()); // or reuse the constant 1 that is already there.
            m_values.push_back(t.second);
            m_solver.lra().add_var_bound(w, lp::lconstraint_kind::GE, t.second);
            m_solver.lra().add_var_bound(w, lp::lconstraint_kind::LE, t.second);
            m_justifications.push_back(nullptr);
            m_justifications.push_back(nullptr);
            t.first.add_monomial(rational(1), w);
            t.second = 0;
        }
        auto ti = m_solver.lra().add_term(t.first.coeffs_as_vector(), m_solver.lra().number_of_vars());
        m_values.push_back(cvalue(t.first));
        m_occurs.reserve(m_solver.lra().number_of_vars());
        return ti;
    }

    bool stellensatz::is_int(svector<lp::lpvar> const& vars) const {
        return all_of(vars, [&](lpvar v) { return m_solver.lra().var_is_int(v); });
    }

    lpvar stellensatz::add_var(bool is_int) {
        auto v = m_solver.lra().number_of_vars();
        auto w = m_solver.lra().add_var(v, is_int);
        SASSERT(v == w);
        m_occurs.reserve(m_solver.lra().number_of_vars());
        return w;
    }

    // if a constraint is false, then insert _all_ monomials from that constraint.
    // other approach: use a lex ordering on monomials and insert the lex leading monomial.   
    // to avoid blowup, only insert monomials up to a certain degree.
    void stellensatz::insert_monomials_from_constraint(lp::constraint_index ci) {
        if (constraint_is_true(ci))
            return;
        m_false_constraints.insert(ci);
        auto const& con = m_solver.lra().constraints()[ci];
        for (auto cv : con.lhs())
            if (is_mon_var(cv.j()) && m_mon2vars[cv.j()].size() <= m_max_monomial_degree)
                m_monomials_to_refine.insert(cv.j());        
    }

    bool stellensatz::constraint_is_true(lp::constraint_index ci) const {
        auto const& con = m_solver.lra().constraints()[ci];
        auto lhs = -con.rhs();
        for (auto const& cv : con.lhs())
            lhs += cv.coeff() * m_values[cv.j()];
        switch (con.kind()) {
        case lp::lconstraint_kind::GT: return lhs > 0;
        case lp::lconstraint_kind::GE: return lhs >= 0;
        case lp::lconstraint_kind::LE: return lhs <= 0;
        case lp::lconstraint_kind::LT: return lhs < 0;
        case lp::lconstraint_kind::EQ: return lhs == 0;
        case lp::lconstraint_kind::NE: return lhs != 0;
        default: UNREACHABLE(); return false;
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
            out << "(" << ci << ") ";
            display_constraint(out, ci);
            bool is_true = constraint_is_true(ci);
            out << (is_true ? " [true]" : " [false]") << "\n";
            auto j = m_justifications.get(ci);
            if (!j)
                continue;
            out << "\t<- ";
            display(out, *j);
            out << "\n";
        }
        return out;
    }

    std::ostream& stellensatz::display(std::ostream& out, justification const& b) const {
        auto display_assumptions = [&](vector<bound_assumption> const &asms) {
            for (auto const &ineq : asms) {
                auto [v, k, rhs] = ineq;
                out << "[j" << v << " " << k << " " << rhs << "] ";
            }
        };
        if (std::holds_alternative<external_justification>(b)) {
            auto dep = *std::get_if<external_justification>(&b);
            unsigned_vector cs;
            c().lra_solver().dep_manager().linearize(dep.dep, cs);
            for (auto c : cs)
                out << "[o " << c << "] ";  // constraint index from c().lra_solver.
        } 
        else if (std::holds_alternative<internal_justification>(b)) {
            auto c = *std::get_if<internal_justification>(&b);
            svector<lp::constraint_index> cis;
            m_solver.lra().dep_manager().linearize(c.dep, cis);
            for (auto ci : cis)
                out << "(" << ci << ") ";  // constraint index from this solver.                
        } 
        else if (std::holds_alternative<multiplication_justification>(b)) {
            auto m = *std::get_if<multiplication_justification>(&b);
            out << "[(" << m.ci << ") *= " << pp_j(*this, m.j1) << " / " << pp_j(*this, m.j2) << "] ";
            display_assumptions(m.assumptions);
        } 
        else if (std::holds_alternative<resolvent_justification>(b)) {
            auto m = *std::get_if<resolvent_justification>(&b);
            out << "[resolve (" << m.ci1 << ") (" << m.ci2 << ") on " << pp_j(*this, m.j) << "] ";
            display_assumptions(m.assumptions);
        } 
        else if (std::holds_alternative<bound_assumptions>(b)) {
            auto ba = *std::get_if<bound_assumptions>(&b);
            out << ba.rule << " ";
            display_assumptions(ba.bounds);
        } else
            UNREACHABLE();
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
            out << pp_j(*this, v);
        }
        if (t.second != 0)
            out << " + " << t.second;
        return out;
    }

    std::ostream& stellensatz::display_var(std::ostream& out, lpvar j) const {
        if (is_mon_var(j))
            display_product(out, m_mon2vars[j]);
        else
            out << "j" << j;
        return out;
    }

    std::ostream& stellensatz::display_constraint(std::ostream& out, lp::constraint_index ci) const {
        auto const& con = m_solver.lra().constraints()[ci];
        return display_constraint(out, con.lhs(), con.kind(), con.rhs());
    }

    std::ostream& stellensatz::display_constraint(std::ostream& out, 
        lp::lar_term const& lhs,
        lp::lconstraint_kind k, rational const& rhs) const {
        bool first = true;
        for (auto cv : lhs) {
            auto v = cv.j();
            c().display_coeff(out, first, cv.coeff());
            first = false;
            if (is_mon_var(v))
                display_product(out, m_mon2vars[v]);
            else
                out << "j" << v;
        }
        return out << " " << k << " " << rhs;
    }

    std::ostream& stellensatz::display_lemma(std::ostream& out, lp::explanation const& ex,
        vector<ineq> const& ineqs) {
        m_constraints_in_conflict.reset();
        svector<lp::constraint_index> todo;
        for (auto c : ex) 
            todo.push_back(c.ci());
        for (unsigned i = 0; i < todo.size(); ++i) {
            auto ci = todo[i];
            if (m_constraints_in_conflict.contains(ci))
                continue;
            m_constraints_in_conflict.insert(ci);
            out << "(" << ci << ") ";
            display_constraint(out, ci) << " ";
            auto j = m_justifications.get(ci);
            if (!j)
                continue;
            display(out, *j) << "\n";
            if (std::holds_alternative<multiplication_justification>(*j)) {
                auto m = *std::get_if<multiplication_justification>(j);
                todo.push_back(m.ci);
            }
            else if (std::holds_alternative<resolvent_justification>(*j)) {
                auto m = *std::get_if<resolvent_justification>(j);
                todo.push_back(m.ci1);
                todo.push_back(m.ci2);                
            }
            else if (std::holds_alternative<internal_justification>(*j)) {
                auto m = *std::get_if<internal_justification>(j);
                svector<lp::constraint_index> cis;
                m_solver.lra().dep_manager().linearize(m.dep, cis);
                for (auto ci : cis)
                    todo.push_back(ci);
            }
        }
        for (auto ineq : ineqs) {
            term_offset t(ineq.term(), rational(0));
            display(out, t) << " " << ineq.cmp() << " " << ineq.rs() << "\n";
        }
        return out;
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
        m_ex.clear();
        m_ineqs.reset();
    }

    lbool stellensatz::solver::solve() {
        while (true) {
            lbool r = solve_lra();
            if (r != l_true)
                return r;
            r = solve_lia();
            if (r != l_true)
                return r;
            unsigned sz = lra_solver->number_of_vars();
            if (update_values())
                return l_true;

            return l_undef;
            // At this point it is not sound to use value justifications 
            // because the model changed from the outer LRA solver.
            // Also value justifications made in a previous iteration may no longer be valid.
            // this can be fixed by asserting the value justifications as bounds directly and 
            // making them depend on themselves.
            TRACE(arith, s.display(tout));
            if (!s.saturate_factors())
                return l_false;
            s.saturate_constraints2();
            if (sz == lra_solver->number_of_vars())
                return l_undef;
        }
    }

    lbool stellensatz::solver::solve_lra() {
        auto status = lra_solver->find_feasible_solution();;
        if (lra_solver->is_feasible())
            return l_true;
        if (status == lp::lp_status::INFEASIBLE) {
            lra_solver->get_infeasibility_explanation(m_ex);
            return l_false;
        }
        return l_undef;
    }

    lbool stellensatz::solver::solve_lia() {
        switch (int_solver->check(&m_ex)) {
        case lp::lia_move::sat: return l_true;
        case lp::lia_move::conflict: return l_false;
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
            if (s.is_mon_var(i)) 
                s.m_values[i] = s.mvalue(s.m_mon2vars[i]);             
            else
                s.m_values[i] = value;
        }
        auto indices = lra_solver->constraints().indices();
        bool satisfies_products = all_of(indices, [&](auto ci) {
            return s.constraint_is_true(ci);});
        s.m_monomials_to_refine.reset();
        s.m_false_constraints.reset();
        // check if all constraints are satisfied
        // if they are, then update the model of parent lra solver.
        for (auto ci : indices) 
            s.insert_monomials_from_constraint(ci);
        SASSERT(satisfies_products == s.m_monomials_to_refine.empty());
        if (satisfies_products) {
            TRACE(arith, tout << "found satisfying model\n");
            for (auto v : s.m_coi.vars()) 
                s.c().lra_solver().set_column_value(v, lp::impq(s.m_values[v], rational(0)));            
        }
        for (auto j : s.m_monomials_to_refine) {
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
