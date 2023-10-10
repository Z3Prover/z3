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

#define UNIT_PROPAGATE_BOUNDS 0

namespace nla {

    monomial_bounds::monomial_bounds(core* c):
        common(c), 
        dep(c->m_intervals.get_dep_intervals()) {}

    void monomial_bounds::propagate() {
        for (lpvar v : c().m_to_refine) 
            propagate(c().emon(v));
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
        auto val = c().val(v);
        if (dep.is_below(range, val)) {
            auto const& upper = dep.upper(range);
            auto cmp = dep.upper_is_open(range) ? llc::LT : llc::LE;
            ++c().lra.settings().stats().m_nla_propagate_bounds;
#if UNIT_PROPAGATE_BOUNDS
            auto* d = dep.get_upper_dep(range);
            c().lra.update_column_type_and_bound(v, cmp, upper, d);
#else
            lp::explanation ex;
            dep.get_upper_dep(range, ex);
            if (is_too_big(upper))
                return false;
            new_lemma lemma(c(), "propagate value - upper bound of range is below value");
            lemma &= ex;
            lemma |= ineq(v, cmp, upper); 
            TRACE("nla_solver", dep.display(tout << c().val(v) << " > ", range) << "\n" << lemma << "\n";);
#endif
            return true;
        }
        else if (dep.is_above(range, val)) {
            auto const& lower = dep.lower(range);
            auto cmp = dep.lower_is_open(range) ? llc::GT : llc::GE;
            ++c().lra.settings().stats().m_nla_propagate_bounds;
#if UNIT_PROPAGATE_BOUNDS
            auto* d = dep.get_lower_dep(range);
            c().lra.update_column_type_and_bound(v, cmp, lower, d);            
#else
            lp::explanation ex;
            dep.get_lower_dep(range, ex);
            if (is_too_big(lower))
                return false;
            new_lemma lemma(c(), "propagate value - lower bound of range is above value");
            lemma &= ex;
            lemma |= ineq(v, cmp, lower); 
            TRACE("nla_solver", dep.display(tout << c().val(v) << " < ", range) << "\n" << lemma << "\n";);
#endif
            return true;
        }
        else {
            return false;
        }
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
        auto val_v = c().val(v);
        auto val = power(val_v, p);
        rational r;
        if (dep.is_below(range, val)) {
            lp::explanation ex;
            dep.get_upper_dep(range, ex);
            if (p % 2 == 0 && rational(dep.upper(range)).is_neg()) {
                ++c().lra.settings().stats().m_nla_propagate_bounds;
                new_lemma lemma(c(), "range requires a non-negative upper bound");
                lemma &= ex;
                return true;
            }
            else if (rational(dep.upper(range)).root(p, r)) {
                // v = -2, [-4,-3]^3 < v^3 -> add bound v <= -3
                // v = -2, [-1,+1]^2 < v^2 -> add bound v >= -1                
                if ((p % 2 == 1) || val_v.is_pos()) {
                    ++c().lra.settings().stats().m_nla_propagate_bounds;
                    auto le = dep.upper_is_open(range) ? llc::LT : llc::LE;
#if UNIT_PROPAGATE_BOUNDS
                    auto* d = dep.get_upper_dep();
                    c().lra.update_column_type_and_bound(v, le, r, d);
#else
                    new_lemma lemma(c(), "propagate value - root case - upper bound of range is below value");
                    lemma &= ex;
                    lemma |= ineq(v, le, r);
#endif
                    return true;
                }
                if (p % 2 == 0 && val_v.is_neg()) {
                    ++c().lra.settings().stats().m_nla_propagate_bounds;
                    SASSERT(!r.is_neg());
                    auto ge = dep.upper_is_open(range) ? llc::GT : llc::GE;
#if UNIT_PROPAGATE_BOUNDS
                    auto* d = dep.get_upper_dep();
                    c().lra.update_column_type_and_bound(v, ge, -r, d);
#else
                    new_lemma lemma(c(), "propagate value - root case - upper bound of range is below negative value");
                    lemma &= ex;
                    lemma |= ineq(v, ge, -r);
#endif
                    return true;
                }
            }
            // TBD: add bounds as long as difference to val is above some epsilon.
        }
        else if (dep.is_above(range, val)) {
            if (rational(dep.lower(range)).root(p, r)) {
                ++c().lra.settings().stats().m_nla_propagate_bounds;
                lp::explanation ex;
                dep.get_lower_dep(range, ex);
                auto ge = dep.lower_is_open(range) ? llc::GT : llc::GE;
                auto le = dep.lower_is_open(range) ? llc::LT : llc::LE;
                new_lemma lemma(c(), "propagate value - root case - lower bound of range is above value");
                lemma &= ex;
                lemma |= ineq(v, ge, r); 
                if (p % 2 == 0) 
                    lemma |= ineq(v, le, -r);                 
                return true;
            }
            // TBD: add bounds as long as difference to val is above some epsilon.
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
            if (c().lra.get_status() == lp::lp_status::INFEASIBLE) {
                lp::explanation exp;
                c().lra.get_infeasibility_explanation(exp);
                new_lemma lemma(c(), "propagate fixed - infeasible lra");
                lemma &= exp;
                break;
            }
            if (c().m_conflicts > 0) 
                break;
        }   
    }

    void monomial_bounds::unit_propagate(monic & m) {
        lpvar w, fixed_to_zero;
        if (!is_linear(m, w, fixed_to_zero)) {
#if UNIT_PROPAGATE_BOUNDS
            propagate(m);
#endif            
            return;
        }

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
        if (c().var_is_fixed_to_zero(m.var())) return;
        
        auto* dep = c().lra.get_bound_constraint_witnesses_for_column(fixed_to_zero);
        TRACE("nla_solver", tout << "propagate fixed " << m << " =  0, fixed_to_zero = " << fixed_to_zero << "\n";);
        c().lra.update_column_type_and_bound(m.var(), lp::lconstraint_kind::EQ, rational(0), dep);
        
        // propagate fixed equality
        auto exp = get_explanation(dep);        
        c().add_fixed_equality(c().lra.column_to_reported_index(m.var()), rational(0), exp);
    }

    void monomial_bounds::propagate_fixed(monic const& m, rational const& k) {
        if (c().var_is_fixed_to_val(m.var(), k)) return;
        
        auto* dep = explain_fixed(m, k);
        TRACE("nla_solver", tout << "propagate fixed " << m << " = " << k << "\n";);
        c().lra.update_column_type_and_bound(m.var(), lp::lconstraint_kind::EQ, k, dep);
        
        // propagate fixed equality
        auto exp = get_explanation(dep);        
        c().add_fixed_equality(c().lra.column_to_reported_index(m.var()), k, exp);
    }

    void monomial_bounds::propagate_nonfixed(monic const& m, rational const& k, lpvar w) {
        vector<std::pair<lp::mpq, unsigned>> coeffs;        
        coeffs.push_back(std::make_pair(-k, w));
        coeffs.push_back(std::make_pair(rational::one(), m.var()));
        lp::lpvar term_index = c().lra.add_term(coeffs, UINT_MAX);
        auto* dep = explain_fixed(m, k);
        term_index = c().lra.map_term_index_to_column_index(term_index);
        TRACE("nla_solver", tout << "propagate nonfixed " << m << " = " << k << " " << w << "\n";);
        c().lra.update_column_type_and_bound(term_index, lp::lconstraint_kind::EQ, mpq(0), dep);

        if (k == 1) {
            lp::explanation exp = get_explanation(dep);
            c().add_equality(c().lra.column_to_reported_index(m.var()), c().lra.column_to_reported_index(w), exp);
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

}

