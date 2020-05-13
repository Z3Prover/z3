/*++
  Copyright (c) 2020 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/
#pragma once

#include "math/lp/monomial_bounds.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_intervals.h"

namespace nla {

    monomial_bounds::monomial_bounds(core* c):common(c) {}

    bool monomial_bounds::operator()() {
        bool propagated = false;
        for (lpvar v : c().m_to_refine) {
            monic const& m = c().emons()[v];
            if (propagate(m))
                propagated = true;
        }
        return propagated;
    }

    /**
     * Accumulate product of variables in monomial starting at position 'start'
     */
    void monomial_bounds::compute_product(unsigned start, monic const& m, scoped_dep_interval& product) {
        auto & intervals = c().m_intervals;
        auto & dep_intervals = intervals.get_dep_intervals();
        scoped_dep_interval vi(dep_intervals);
        for (unsigned i = start; i < m.size(); ) {
            lpvar v = m.vars()[i];
            unsigned power = 1;
            var2interval(v, vi);
            ++i;
            for (; i < m.size() && m.vars()[i] == v; ++i) {
                ++power;
            }
            dep_intervals.power<dep_intervals::with_deps>(vi, power, vi);            
            dep_intervals.mul<dep_intervals::with_deps>(product, vi, product);
        }
    }

    /**
     * Monomial definition implies that a variable v is within 'range'
     * If the current value of v is outside of the range, we add
     * a bounds axiom.
     */
    bool monomial_bounds::propagate_value(dep_interval& range, lpvar v) {
        auto & intervals = c().m_intervals;
        auto & dep_intervals = intervals.get_dep_intervals();
        if (dep_intervals.is_below(range, c().val(v))) {
            lp::explanation ex;
            dep_intervals.get_upper_dep(range, ex);
            auto const& upper = dep_intervals.upper(range);
            auto cmp = dep_intervals.upper_is_open(range) ? llc::LT : llc::LE;
            new_lemma lemma(c(), "propagate value - upper bound of range is below value");
            lemma &= ex;
            lemma |= ineq(v, cmp, upper); 
            return true;
        }
        else if (dep_intervals.is_above(range, c().val(v))) {
            lp::explanation ex;
            dep_intervals.get_lower_dep(range, ex);
            auto const& lower = dep_intervals.lower(range);
            auto cmp = dep_intervals.lower_is_open(range) ? llc::GT : llc::GE;
            new_lemma lemma(c(), "propagate value - lower bound of range is above value");
            lemma &= ex;
            lemma |= ineq(v, cmp, lower); 
            return true;
        }
        else {
            return false;
        }
    }

    void monomial_bounds::var2interval(lpvar v, scoped_dep_interval& i) {
        auto & intervals = c().m_intervals;
        auto & dep_intervals = intervals.get_dep_intervals();
        lp::constraint_index ci;
        rational bound;
        bool is_strict;
        if (c().has_lower_bound(v, ci, bound, is_strict)) {
            dep_intervals.set_lower_is_open(i, is_strict);
            dep_intervals.set_lower(i, bound);
            dep_intervals.set_lower_dep(i, dep_intervals.mk_leaf(ci));
        }
        else {
            dep_intervals.set_lower_is_inf(i, true);
        }
        if (c().has_upper_bound(v, ci, bound, is_strict)) {
            dep_intervals.set_upper_is_open(i, is_strict);
            dep_intervals.set_upper(i, bound);
            dep_intervals.set_upper_dep(i, dep_intervals.mk_leaf(ci));            
        }
        else {
            dep_intervals.set_upper_is_inf(i, true);
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
        auto & intervals = c().m_intervals;
        auto & dep_intervals = intervals.get_dep_intervals();
        scoped_dep_interval product(dep_intervals);
        scoped_dep_interval vi(dep_intervals), mi(dep_intervals);
        scoped_dep_interval other_product(dep_intervals);
        var2interval(m.var(), mi);
        if (dep_intervals.lower_is_inf(mi) && dep_intervals.upper_is_inf(mi))
            return false;
        dep_intervals.set_value(product, rational::one());
        for (unsigned i = 0; i < m.size(); ) {
            lpvar v = m.vars()[i];
            ++i;
            unsigned power = 1;
            for (; i < m.size() && v == m.vars()[i]; ++i) 
                ++power;
            var2interval(v, vi);
            dep_intervals.power<dep_intervals::with_deps>(vi, power, vi);            
            if (power == 1) {
                dep_intervals.set<dep_intervals::with_deps>(other_product, product);
                compute_product(i, m, other_product);
                if (propagate_down(m, mi, v, other_product))
                    return true;
            }
            dep_intervals.mul<dep_intervals::with_deps>(product, vi, product);
        }
        return propagate_value(product, m.var());
    }

    bool monomial_bounds::propagate_down(monic const& m, dep_interval& mi, lpvar v, dep_interval& product) {
        auto & intervals = c().m_intervals;
        auto & dep_intervals = intervals.get_dep_intervals();
        if (!dep_intervals.separated_from_zero(product)) 
            return false;
        scoped_dep_interval range(dep_intervals);
        dep_intervals.set<dep_intervals::with_deps>(range, mi);
        dep_intervals.div<dep_intervals::with_deps>(range, product, range);
        return propagate_value(range, v);
    }

}

