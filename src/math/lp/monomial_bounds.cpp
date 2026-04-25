/*++
  Copyright (c) 2020 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/

#include "math/lp/monomial_bounds.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_intervals.h"
#include "math/lp/numeric_pair.h"

namespace nla {

    monomial_bounds::monomial_bounds(core* c):
        common(c), 
        dep(c->m_intervals.get_dep_intervals()) {
    
        std::function<void(lpvar v)> fixed_eh = [c, this](lpvar v) {
            c->trail().push(push_back_vector(m_fixed_var_trail));
            m_fixed_var_trail.push_back(v);
        };
// uncomment to enable:
//        c->lra.m_fixed_var_eh = fixed_eh;
    }

    void monomial_bounds::propagate() {
        for (lpvar v : c().m_to_refine) {
            propagate(c().emon(v));
            if (add_lemma()) 
                break;
        }
        propagate_fixed_vars();
    }

    void monomial_bounds::propagate_fixed_vars() {
        if (m_fixed_var_qhead == m_fixed_var_trail.size())
            return;
        c().trail().push(value_trail(m_fixed_var_qhead));
        while (m_fixed_var_qhead < m_fixed_var_trail.size()) 
            propagate_fixed_var(m_fixed_var_trail[m_fixed_var_qhead++]);        
    }

    void monomial_bounds::propagate_fixed_var(lpvar v) {
        SASSERT(c().var_is_fixed(v));
        TRACE(nla_solver, tout << "propagate fixed var: " << c().var_str(v) << "\n";);
        for (auto const& m : c().emons().get_use_list(v)) 
            propagate_fixed_var(m, v);
    }

    void monomial_bounds::propagate_fixed_var(monic const& m, lpvar v) {
        unsigned num_free = 0;
        lpvar free_var = null_lpvar;
        for (auto w : m)
            if (!c().var_is_fixed(w))
                ++num_free, free_var = w;
        if (num_free != 1)
            return;
        u_dependency* d = nullptr;
        auto& lra = c().lra;
        lp::mpq coeff(1);
        for (auto w : m) {
            if (c().var_is_fixed(w)) {
                d =  lra.join_deps(d, lra.get_bound_constraint_witnesses_for_column(w));
                coeff *= lra.get_lower_bound(w).x;
            }
        }
        vector<std::pair<lp::mpq, lpvar>> coeffs;
        coeffs.push_back({coeff, free_var});
        coeffs.push_back({mpq(-1), m.var()});
        lpvar j = lra.add_term(coeffs, UINT_MAX);
        lra.update_column_type_and_bound(j, llc::EQ, mpq(0), d);
    }

    bool monomial_bounds::is_too_big(mpq const& q) const {
        return rational(q).bitsize() > 256;
    }

    /**
     * Accumulate product of variables in monomial starting at position 'start'
     */
    void monomial_bounds::compute_product(unsigned start, monic const& m, scoped_dep_interval& product) {
        scoped_dep_interval vi(dep);
        unsigned power = 1;
        for (unsigned i = start; i < m.size(); ) {
            lpvar v = m.vars()[i];
            var2interval(v, vi);
            ++i;
            for (power = 1; i < m.size() && m.vars()[i] == v; ++i, ++power);
            dep.power<dep_intervals::with_deps>(vi, power, vi);            
            dep.mul<dep_intervals::with_deps>(product, vi, product);
        }
    }

    /**
     * Monomial definition implies that a variable v is within 'range'
     * If the current value of v is outside of the range, we add
     * a bounds axiom.
     */
    bool monomial_bounds::propagate_value(dep_interval& range, lpvar v) {
        
        bool propagated = false;
        if (should_propagate_upper(range, v, 1)) {
            auto const& upper = dep.upper(range);
            auto cmp = dep.upper_is_open(range) ? llc::LT : llc::LE;
            ++c().lra.settings().stats().m_nla_propagate_bounds;
            lp::explanation ex;
            dep.get_upper_dep(range, ex);
            if (is_too_big(upper))
                return false;
            lemma_builder lemma(c(), "propagate value - upper bound of range is below value");
            lemma &= ex;
            lemma |= ineq(v, cmp, upper); 
            TRACE(nla_solver, dep.display(tout << c().val(v) << " > ", range) << "\n" << lemma << "\n";);
            propagated = true;           
        }
        if (should_propagate_lower(range, v, 1)) {
            auto const& lower = dep.lower(range);
            auto cmp = dep.lower_is_open(range) ? llc::GT : llc::GE;
            ++c().lra.settings().stats().m_nla_propagate_bounds;
            lp::explanation ex;
            dep.get_lower_dep(range, ex);
            if (is_too_big(lower))
                return false;
            lemma_builder lemma(c(), "propagate value - lower bound of range is above value");
            lemma &= ex;
            lemma |= ineq(v, cmp, lower); 
            TRACE(nla_solver, dep.display(tout << c().val(v) << " < ", range) << "\n" << lemma << "\n";);
            propagated = true;
        }
        return propagated;
    }

    bool monomial_bounds::should_propagate_lower(dep_interval const& range, lpvar v, unsigned p) {
        if (dep.lower_is_inf(range))
            return false;
        auto bound = c().val(v);
        auto const& lower = dep.lower(range);
        if (p > 1)
            bound = power(bound, p);
        return bound < lower;
    }

    bool monomial_bounds::should_propagate_upper(dep_interval const& range, lpvar v, unsigned p) {
        if (dep.upper_is_inf(range))
            return false;
        auto bound = c().val(v);
        auto const& upper = dep.upper(range);
        if (p > 1)
            bound = power(bound, p);
        return bound > upper;
    }

    /**
     * Ensure that bounds are integral when the variable is integer.
     */
    void monomial_bounds::propagate_bound(lpvar v, lp::lconstraint_kind cmp, rational const& q, u_dependency* d) {
        SASSERT(cmp != llc::EQ && cmp != llc::NE);
        if (!c().var_is_int(v))
            c().lra.update_column_type_and_bound(v, cmp, q, d);
        else if (q.is_int()) {
            if (cmp == llc::GT)
                c().lra.update_column_type_and_bound(v, llc::GE, q + 1, d);
            else if(cmp == llc::LT)
                c().lra.update_column_type_and_bound(v, llc::LE, q - 1, d);
            else
                c().lra.update_column_type_and_bound(v, cmp, q, d);
        }
        else if (cmp == llc::GE || cmp == llc::GT) 
            c().lra.update_column_type_and_bound(v, llc::GE, ceil(q), d);
        else
            c().lra.update_column_type_and_bound(v, llc::LE, floor(q), d);
    }


    /**
     * val(v)^p should be in range.
     * if val(v)^p > upper(range) add 
     *             v <= root(p, upper(range)) and v >= -root(p, upper(range)) if p is even
     *             v <= root(p, upper(range))                                 if p is odd
     * if val(v)^p < lower(range) add
     *             v >= root(p, lower(range)) or v <= -root(p, lower(range)) if p is even
     *             v >= root(p, lower(range))                                if p is odd
     */

    bool monomial_bounds::propagate_value(dep_interval& range, lpvar v, unsigned p) {
        SASSERT(p > 0);
        if (p == 1) 
            return propagate_value(range, v);
        rational r;
        if (should_propagate_upper(range, v, p)) {  // v.upper^p > range.upper
            lp::explanation ex;
            dep.get_upper_dep(range, ex);
            // p even, range.upper < 0, v^p >= 0 -> infeasible
            if (p % 2 == 0 && rational(dep.upper(range)).is_neg()) {
                ++c().lra.settings().stats().m_nla_propagate_bounds;
                lemma_builder lemma(c(), "range requires a non-negative upper bound");
                lemma &= ex;
                return true;
            }

            if (rational(dep.upper(range)).root(p, r)) {
                // v = -2, [-4,-3]^3 < v^3 -> add bound v <= -3
                // v = -2, [-1,+1]^2 < v^2 -> add bound v >= -1

                if ((p % 2 == 1) || c().val(v).is_pos()) {
                    ++c().lra.settings().stats().m_nla_propagate_bounds;
                    auto le = dep.upper_is_open(range) ? llc::LT : llc::LE;
                    lemma_builder lemma(c(), "propagate value - root case - upper bound of range is below value");
                    lemma &= ex;
                    lemma |= ineq(v, le, r);
                    return true;
                }

                if (p % 2 == 0 && c().val(v).is_neg()) {
                    ++c().lra.settings().stats().m_nla_propagate_bounds;
                    SASSERT(!r.is_neg());
                    auto ge = dep.upper_is_open(range) ? llc::GT : llc::GE;
                    lemma_builder lemma(c(), "propagate value - root case - upper bound of range is below negative value");
                    lemma &= ex;
                    lemma |= ineq(v, ge, -r);
                    return true;
                }
            }
        }

        if (should_propagate_lower(range, v, p)) { // v.lower^p < range.lower
            //
            // range.lower < 0 -> v.lower >= root(p, range.lower)
            // range.lower >= 0, p odd -> v.lower >= root(p, range.lower)
            // range.lower >= 0, p even, v.lower >= 0 -> v.lower >= root(p, range.lower)
            // default:
            //    v.lower >= root(p, range.lower) || (p even & v.upper <= -root(p, range.lower))
            // 
            // pre-condition: p even -> range.lower >= 0
            //  
            if (rational(dep.lower(range)).root(p, r)) {
                ++c().lra.settings().stats().m_nla_propagate_bounds;
                auto ge = dep.lower_is_open(range) ? llc::GT : llc::GE;
                auto le = dep.lower_is_open(range) ? llc::LT : llc::LE;
                lp::explanation ex;
                dep.get_lower_dep(range, ex);
                lemma_builder lemma(c(), "propagate value - root case - lower bound of range is above value");
                lemma &= ex;
                lemma |= ineq(v, ge, r);
                if (p % 2 == 0)
                    lemma |= ineq(v, le, -r);
                return true;                
            }
        }
        return false;
    }

    void monomial_bounds::var2interval(lpvar v, scoped_dep_interval& i) {
        u_dependency* d = nullptr;
        rational bound;
        bool is_strict;
        if (c().has_lower_bound(v, d, bound, is_strict)) {
            dep.set_lower_is_open(i, is_strict);
            dep.set_lower(i, bound);
            dep.set_lower_dep(i, d);
            dep.set_lower_is_inf(i, false);
        }
        else {
            dep.set_lower_is_inf(i, true);
        }
        if (c().has_upper_bound(v, d, bound, is_strict)) {
            dep.set_upper_is_open(i, is_strict);
            dep.set_upper(i, bound);
            dep.set_upper_dep(i, d);            
            dep.set_upper_is_inf(i, false);
        }
        else {
            dep.set_upper_is_inf(i, true);
        }
    }

    /**
     * Propagate bounds for monomial 'm'.
     * For each variable v in m, compute the intervals of the remaining variables in m.
     * Compute also the interval for m.var() as mi
     * If the value of v is outside of mi / product_of_other, add a bounds lemma.
     * If the value of m.var() is outside of product_of_all_vars, add a bounds lemma.
     */
    bool monomial_bounds::propagate(monic const& m) {
        unsigned num_free, power;
        lpvar free_var;
        analyze_monomial(m, num_free, free_var, power);
        bool do_propagate_up   = num_free == 0;
        bool do_propagate_down = !is_free(m.var()) && num_free <= 1;
        if (!do_propagate_up && !do_propagate_down)
            return false;
        scoped_dep_interval product(dep);
        scoped_dep_interval vi(dep), mi(dep);
        scoped_dep_interval other_product(dep);
        var2interval(m.var(), mi);
        dep.set_value(product, rational::one());
        for (unsigned i = 0; i < m.size(); ) {
            lpvar v = m.vars()[i];
            ++i;
            for (power = 1; i < m.size() && v == m.vars()[i]; ++i, ++power); 
            var2interval(v, vi);
            dep.power<dep_intervals::with_deps>(vi, power, vi);            

            if (do_propagate_down && (num_free == 0 || free_var == v)) {
                dep.set<dep_intervals::with_deps>(other_product, product);
                compute_product(i, m, other_product);
                if (propagate_down(m, mi, v, power, other_product))
                    return true;
            }
            dep.mul<dep_intervals::with_deps>(product, vi, product);
        }
        if (do_propagate_down && c().params().arith_nl_monomial_sandwich() &&
            propagate_shared_factor(m))
            return true;
        if (c().params().arith_nl_monomial_binomial_sign() &&
            propagate_binomial_sign(m))
            return true;
        return do_propagate_up && propagate_value(product, m.var());
    }

    bool monomial_bounds::propagate_down(monic const& m, dep_interval& mi, lpvar v, unsigned power, dep_interval& product) {
        if (!dep.separated_from_zero(product)) 
            return false;
        scoped_dep_interval range(dep);
        dep.div<dep_intervals::with_deps>(mi, product, range);
        return propagate_value(range, v, power);
    }

    bool monomial_bounds::is_free(lpvar v) const {
        return !c().has_lower_bound(v) && !c().has_upper_bound(v);
    }    

    bool monomial_bounds::is_zero(lpvar v) const {
        return 
            c().has_lower_bound(v) && 
            c().has_upper_bound(v) &&
            c().get_lower_bound(v).is_zero() && 
            c().get_upper_bound(v).is_zero();
    }    

    /**
     * Count the number of unbound (free) variables.
     * Variables with no lower and no upper bound multiplied 
     * to an odd degree have unbound ranges when it comes to 
     * bounds propagation.
     */
    void monomial_bounds::analyze_monomial(monic const& m, unsigned& num_free, lpvar& fv, unsigned& fv_power) const {
        unsigned power = 1;
        num_free = 0;
        fv = null_lpvar;
        fv_power = 0;
        for (unsigned i = 0; i < m.vars().size(); ) {
            lpvar v = m.vars()[i];
            ++i;
            for (power = 1; i < m.vars().size() && m.vars()[i] == v; ++i, ++power);
            if (is_zero(v)) {
                num_free = 0;
                return;
            }
            if (power % 2 == 1 && is_free(v)) {
                ++num_free;
                fv_power = power;
                fv = v;
            }
        }
    }

    void monomial_bounds::unit_propagate() {        
        for (lpvar v : c().m_monics_with_changed_bounds) {
            if (!c().is_monic_var(v))
                continue;
            monic& m = c().emon(v);
            unit_propagate(m);
            if (add_lemma()) 
                break;
            if (c().m_conflicts > 0) 
                break;
        }   
    }

    bool monomial_bounds::add_lemma() {
        if (c().lra.get_status() != lp::lp_status::INFEASIBLE)
            return false;
        lp::explanation exp;
        c().lra.get_infeasibility_explanation(exp);
        lemma_builder lemma(c(), "propagate fixed - infeasible lra");
        lemma &= exp;
        return true;
    }

    void monomial_bounds::unit_propagate(monic & m) {
        if (m.is_propagated())
            return;
        lpvar w, fixed_to_zero;

        if (!is_linear(m, w, fixed_to_zero)) 
            return;

        c().emons().set_propagated(m);

        if (fixed_to_zero != null_lpvar) {
            propagate_fixed_to_zero(m, fixed_to_zero);
        } 
        else {
            rational k = fixed_var_product(m, w);
            if (w == null_lpvar)
                propagate_fixed(m, k);
            else
                propagate_nonfixed(m, k, w);
        }
        ++c().lra.settings().stats().m_nla_propagate_eq;
    }

    lp::explanation monomial_bounds::get_explanation(u_dependency* dep) {
        lp::explanation exp;
        svector<lp::constraint_index> cs;
        c().lra.dep_manager().linearize(dep, cs);
        for (auto d : cs)
            exp.add_pair(d, mpq(1));
        return exp;
    }
    
    void monomial_bounds::propagate_fixed_to_zero(monic const& m, lpvar fixed_to_zero) {
        auto* dep = c().lra.get_bound_constraint_witnesses_for_column(fixed_to_zero);
        TRACE(nla_solver, tout << "propagate fixed " << m << " =  0, fixed_to_zero = " << fixed_to_zero << "\n";);
        c().lra.update_column_type_and_bound(m.var(), lp::lconstraint_kind::EQ, rational(0), dep);
        
        // propagate fixed equality
        c().add_fixed_equality(m.var(), rational(0), get_explanation(dep));
    }

    void monomial_bounds::propagate_fixed(monic const& m, rational const& k) {
        auto* dep = explain_fixed(m, k);
        TRACE(nla_solver, tout << "propagate fixed " << m << " = " << k << "\n";);
        c().lra.update_column_type_and_bound(m.var(), lp::lconstraint_kind::EQ, k, dep);
        
        // propagate fixed equality
        c().add_fixed_equality(m.var(), k, get_explanation(dep));
    }

    void monomial_bounds::propagate_nonfixed(monic const& m, rational const& k, lpvar w) {
        vector<std::pair<lp::mpq, unsigned>> coeffs;        
        coeffs.push_back({-k, w});
        coeffs.push_back({rational::one(), m.var()});
        lp::lpvar j = c().lra.add_term(coeffs, UINT_MAX);
        auto* dep = explain_fixed(m, k);
        TRACE(nla_solver, tout << "propagate nonfixed " << m << " = " << k << " " << w << "\n";);
        c().lra.update_column_type_and_bound(j, lp::lconstraint_kind::EQ, mpq(0), dep);

        if (k == 1) {
            c().add_equality(m.var(), w, get_explanation(dep));
        }
    }

    u_dependency* monomial_bounds::explain_fixed(monic const& m, rational const& k) {
        u_dependency* dep = nullptr;
        auto update_dep = [&](unsigned j) {
            dep = c().lra.dep_manager().mk_join(dep, c().lra.get_column_lower_bound_witness(j));
            dep = c().lra.dep_manager().mk_join(dep, c().lra.get_column_upper_bound_witness(j));
            return dep;
        };

        if (k == 0) {
            for (auto j : m.vars()) 
                if (c().var_is_fixed_to_zero(j)) 
                    return update_dep(j);
        }
        else {
            for (auto j : m.vars()) 
                if (c().var_is_fixed(j))
                    update_dep(j);
        }
        return dep;
    }

    
    bool monomial_bounds::is_linear(monic const& m, lpvar& w, lpvar & fixed_to_zero) {
        w = fixed_to_zero = null_lpvar;
        for (lpvar v : m) {
            if (!c().var_is_fixed(v)) {
                if (w != null_lpvar)
                    return false;
                w = v;
            }
            else if (c().get_lower_bound(v).is_zero()) {
                fixed_to_zero = v;
                return true;
            }
        }
        return true;
    }
    
    
    rational monomial_bounds::fixed_var_product(monic const& m, lpvar w) {
        rational r(1);
        for (lpvar v : m) {
            //  we have to use the column bounds here, because the column value may be outside the bounds
            if (v != w ){
                SASSERT(c().var_is_fixed(v));
                r *= c().lra.get_lower_bound(v).x;
            }
        }
        return r;
    }
    
    lpvar monomial_bounds::non_fixed_var(monic const& m) {
        for (lpvar v : m)
            if (!c().var_is_fixed(v))
                return v;
        return null_lpvar;
    }

    /**
     * Dual-row shared-factor sandwich. For a binary monomial m = u*v, find LP
     * term columns whose term has shape  a_m * m + a_v * v  (exactly two
     * variables, both factors of m). The term column's bound is a sound
     * interval for (a_m * m + a_v * v). Substituting m = u*v yields
     * v * (a_m * u + a_v); dividing by the interval on v (sign-determined)
     * gives an interval on (a_m * u + a_v), and an affine shift gives an
     * interval on u. The derived interval is fed to the existing
     * propagate_value path so the lemma channel and integer rounding are
     * shared with the rest of the propagation pipeline.
     */
    bool monomial_bounds::propagate_shared_factor(monic const& m) {
        if (m.size() != 2)
            return false;
        lpvar f0 = m.vars()[0], f1 = m.vars()[1];
        if (f0 == f1)
            return false;

        unsigned const fanout_limit = c().params().arith_nl_monomial_sandwich_max_fanout();

        auto try_pair = [&](lpvar u, lpvar v) -> bool {
            // Skip if u participates in too many monomials: tightening such a
            // factor cascades through ord-binom / monotonicity on every monic
            // that contains it.
            if (fanout_limit > 0) {
                unsigned fanout = 0;
                for (auto const& m1 : c().emons().get_use_list(u)) {
                    (void)m1;
                    if (++fanout > fanout_limit)
                        return false;
                }
            }
            scoped_dep_interval vi(dep);
            var2interval(v, vi);
            if (!dep.separated_from_zero(vi))
                return false;

            auto& lra = c().lra;
            unsigned const ROW_CAP = 16;
            unsigned scanned = 0;

            for (auto const& cell : lra.A_r().m_columns[m.var()]) {
                if (++scanned > ROW_CAP)
                    break;
                unsigned basic = lra.get_base_column_in_row(cell.var());
                if (basic == m.var() || basic == v || basic == u)
                    continue;
                if (!lra.column_has_term(basic))
                    continue;
                auto const& term = lra.get_term(basic);
                if (term.size() != 2 ||
                    !term.contains(m.var()) || !term.contains(v))
                    continue;

                rational const& a_m = term.get_coeff(m.var());
                rational const& a_v = term.get_coeff(v);
                if (a_m.is_zero())
                    continue;

                // Term value = a_m*m + a_v*v; bound on basic bounds the term.
                // Substituting m = u*v: term = v * (a_m*u + a_v).
                scoped_dep_interval bi(dep);
                var2interval(basic, bi);

                scoped_dep_interval inner(dep);
                dep.div<dep_intervals::with_deps>(bi, vi, inner);

                scoped_dep_interval shift(dep);
                dep.set_value(shift, -a_v);
                scoped_dep_interval scaled(dep);
                dep.add<dep_intervals::with_deps>(inner, shift, scaled);

                scoped_dep_interval u_int(dep);
                dep.mul<dep_intervals::with_deps>(rational::one() / a_m, scaled, u_int);

                TRACE(nla_solver, tout << "sandwich shared-factor basic=" << basic
                      << " m=" << m.var() << " v=" << v << " u=" << u
                      << " a_m=" << a_m << " a_v=" << a_v << "\n";);

                if (propagate_value(u_int, u))
                    return true;  // one lemma per call to keep the channel quiet
            }
            return false;
        };

        return try_pair(f1, f0) || try_pair(f0, f1);
    }

    /**
     * Sign-pinned binomial bound. For a binary monomial m = u*v in m_to_refine,
     * use the current LP value mv = val(m.var()) as a one-sided anchor on the
     * monomial value variable, and derive a deterministic interval for u via
     * sign-aware division by v.
     *
     * Direction is chosen by the disagreement: if val(m.var()) > val(u)*val(v)
     * the LP placed the monomial above the factor product, so we condition on
     * "m.var() >= mv"; otherwise on "m.var() <= mv". The resulting clause is
     * structurally analogous to a propagate_value lemma plus one extra
     * snapshot literal on m.var(): under the asserted bounds on v, the clause
     * reduces to a 2-disjunct (snapshot literal | factor bound).
     *
     * Targets the case ord-binom currently handles: factors have determined
     * signs, m.var() may have no LP bound at all. The clause is sound modulo
     * the monomial definition (the same condition propagate_down,
     * propagate_shared_factor and ord-binom rely on).
     */
    bool monomial_bounds::propagate_binomial_sign(monic const& m) {
        if (m.size() != 2)
            return false;
        lpvar f0 = m.vars()[0], f1 = m.vars()[1];
        if (f0 == f1)
            return false;

        rational const mv = c().val(m.var());
        rational const fp = c().val(f0) * c().val(f1);
        if (mv == fp)
            return false;
        bool const below = mv > fp;            // LP placed m.var() too high
        llc const anchor_cmp = below ? llc::LT : llc::GT;

        auto try_anchor = [&](lpvar u, lpvar v) -> bool {
            // Throttle once per (m.var(), u, v, direction) tuple. Without it
            // each new val(m.var()) snapshot would re-emit and the search
            // would cascade across model changes the same way ord-binom does.
            if (c().throttle().insert_new(
                    nla_throttle::MONOMIAL_BINOMIAL_SIGN,
                    m.var(), u, v, below))
                return false;

            scoped_dep_interval vi(dep);
            var2interval(v, vi);
            if (!dep.separated_from_zero(vi))
                return false;

            // Synthesize a one-sided interval for m.var() at mv. No deps;
            // the snapshot literal goes into the lemma body directly.
            scoped_dep_interval mi_anchor(dep);
            if (below) {
                dep.set_lower(mi_anchor, mv);
                dep.set_lower_is_inf(mi_anchor, false);
                dep.set_lower_is_open(mi_anchor, false);
                dep.set_upper_is_inf(mi_anchor, true);
            } else {
                dep.set_upper(mi_anchor, mv);
                dep.set_upper_is_inf(mi_anchor, false);
                dep.set_upper_is_open(mi_anchor, false);
                dep.set_lower_is_inf(mi_anchor, true);
            }

            scoped_dep_interval u_int(dep);
            dep.div<dep_intervals::with_deps>(mi_anchor, vi, u_int);

            bool emitted = false;
            if (should_propagate_lower(u_int, u, 1)) {
                auto const& lower = dep.lower(u_int);
                if (!is_too_big(lower)) {
                    auto cmp = dep.lower_is_open(u_int) ? llc::GT : llc::GE;
                    lp::explanation ex;
                    dep.get_lower_dep(u_int, ex);
                    lemma_builder lemma(c(), "binomial sign anchor");
                    lemma &= ex;
                    lemma |= ineq(m.var(), anchor_cmp, mv);
                    lemma |= ineq(u, cmp, lower);
                    emitted = true;
                }
            }
            if (should_propagate_upper(u_int, u, 1)) {
                auto const& upper = dep.upper(u_int);
                if (!is_too_big(upper)) {
                    auto cmp = dep.upper_is_open(u_int) ? llc::LT : llc::LE;
                    lp::explanation ex;
                    dep.get_upper_dep(u_int, ex);
                    lemma_builder lemma(c(), "binomial sign anchor");
                    lemma &= ex;
                    lemma |= ineq(m.var(), anchor_cmp, mv);
                    lemma |= ineq(u, cmp, upper);
                    emitted = true;
                }
            }
            return emitted;
        };

        return try_anchor(f1, f0) || try_anchor(f0, f1);
    }

}

