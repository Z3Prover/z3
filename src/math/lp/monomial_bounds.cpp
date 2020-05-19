/*++
  Copyright (c) 2020 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/

#include "math/lp/monomial_bounds.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_intervals.h"

namespace nla {

    monomial_bounds::monomial_bounds(core* c):
        common(c), 
        dep(c->m_intervals.get_dep_intervals()) {}

    void monomial_bounds::operator()() {
        for (lpvar v : c().m_to_refine) {
            monic const& m = c().emons()[v];
            propagate(m);
        }
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
            lp::explanation ex;
            dep.get_upper_dep(range, ex);
            auto const& upper = dep.upper(range);
            auto cmp = dep.upper_is_open(range) ? llc::LT : llc::LE;
            new_lemma lemma(c(), "propagate value - upper bound of range is below value");
            lemma &= ex;
            lemma |= ineq(v, cmp, upper); 
            TRACE("nla_solver", dep.display(tout << val << " > ", range) << "\n" << lemma << "\n";);
            return true;
        }
        else if (dep.is_above(range, val)) {
            lp::explanation ex;
            dep.get_lower_dep(range, ex);
            auto const& lower = dep.lower(range);
            auto cmp = dep.lower_is_open(range) ? llc::GT : llc::GE;
            new_lemma lemma(c(), "propagate value - lower bound of range is above value");
            lemma &= ex;
            lemma |= ineq(v, cmp, lower); 
            TRACE("nla_solver", dep.display(tout << val << " < ", range) << "\n" << lemma << "\n";);
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
                new_lemma lemma(c(), "range requires a non-negative upper bound");
                lemma &= ex;
                return true;
            }
            else if (rational(dep.upper(range)).root(p, r)) {
                // v = -2, [-4,-3]^3 < v^3 -> add bound v <= -3
                // v = -2, [-1,+1]^2 < v^2 -> add bound v >= -1                
                if ((p % 2 == 1) || val_v.is_pos()) {
                    auto le = dep.upper_is_open(range) ? llc::LT : llc::LE;
                    new_lemma lemma(c(), "propagate value - root case - upper bound of range is below value");
                    lemma &= ex;
                    lemma |= ineq(v, le, r); 
                    return true;
                }
                if (p % 2 == 0 && val_v.is_neg()) {
                    SASSERT(!r.is_neg());
                    auto ge = dep.upper_is_open(range) ? llc::GT : llc::GE;
                    new_lemma lemma(c(), "propagate value - root case - upper bound of range is below negative value");
                    lemma &= ex;
                    lemma |= ineq(v, ge, -r); 
                    return true;
                }
            }
            // TBD: add bounds as long as difference to val is above some epsilon.
        }
        else if (dep.is_above(range, val)) {
            if (rational(dep.lower(range)).root(p, r)) {
                lp::explanation ex;
                dep.get_lower_dep(range, ex);
                auto ge = dep.lower_is_open(range) ? llc::GT : llc::GE;
                auto le = dep.lower_is_open(range) ? llc::LT : llc::LE;
                new_lemma lemma(c(), "propagate value - root case - lower bound of range is above value");
                lemma &= ex;
                lemma |= ineq(v, ge, r); 
                if (p % 2 == 0) {
                    lemma |= ineq(v, le, -r);                 
                }
                return true;
            }
            // TBD: add bounds as long as difference to val is above some epsilon.
        }
        return false;
    }

    void monomial_bounds::var2interval(lpvar v, scoped_dep_interval& i) {
        lp::constraint_index ci;
        rational bound;
        bool is_strict;
        if (c().has_lower_bound(v, ci, bound, is_strict)) {
            dep.set_lower_is_open(i, is_strict);
            dep.set_lower(i, bound);
            dep.set_lower_dep(i, dep.mk_leaf(ci));
            dep.set_lower_is_inf(i, false);
        }
        else {
            dep.set_lower_is_inf(i, true);
        }
        if (c().has_upper_bound(v, ci, bound, is_strict)) {
            dep.set_upper_is_open(i, is_strict);
            dep.set_upper(i, bound);
            dep.set_upper_dep(i, dep.mk_leaf(ci));            
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

}

