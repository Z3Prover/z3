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
            if (propagate_up(m))
                propagated = true;
        }
        return propagated;
    }

    bool monomial_bounds::propagate_up(monic const& m) {
        auto & intervals = c().m_intervals;
        auto & dep_intervals = intervals.get_dep_intervals();
        scoped_dep_interval product(dep_intervals), di(dep_intervals);
        lpvar v = m.vars()[0];
        var2interval(v, product);
        for (unsigned i = 1; i < m.size(); ++i) {
            var2interval(m.vars()[i], di);
            dep_intervals.mul(product, di, product);
        }
        if (dep_intervals.is_below(product, c().val(m.var()))) {
            lp::explanation ex;
            dep_intervals.get_upper_dep(product, ex);
            new_lemma lemma(c(), "propagate up - upper bound of product is below value");
            lemma &= ex;
            auto const& upper = dep_intervals.upper(product);
            auto cmp = dep_intervals.upper_is_open(product) ? llc::LT : llc::LE;
            lemma |= ineq(m.var(), cmp, upper); 
            return true;
        }
        else if (dep_intervals.is_above(product, c().val(m.var()))) {
            lp::explanation ex;
            dep_intervals.get_lower_dep(product, ex);
            new_lemma lemma(c(), "propagate up - lower bound of product is above value");
            lemma &= ex;
            auto const& lower = dep_intervals.upper(product);
            auto cmp = dep_intervals.lower_is_open(product) ? llc::GT : llc::GE;
            lemma |= ineq(m.var(), cmp, lower); 
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
        if (c().has_upper_bound(v, ci, bound, is_strict)) {
            dep_intervals.set_upper_is_open(i, is_strict);
            dep_intervals.set_upper(i, bound);
            dep_intervals.set_upper_dep(i, dep_intervals.mk_leaf(ci));            
        }
    }
}

