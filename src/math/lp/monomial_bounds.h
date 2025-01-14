/*++
  Copyright (c) 2020 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/
#pragma once

#include "math/lp/nla_common.h"
#include "math/lp/nla_intervals.h"
#include "util/uint_set.h"

namespace nla {
    class core;
    class monomial_bounds : common {
        dep_intervals& dep;

        bool should_propagate_lower(dep_interval const& range, lpvar v, unsigned p);
        bool should_propagate_upper(dep_interval const& range, lpvar v, unsigned p);
        void propagate_bound(lpvar v, lp::lconstraint_kind cmp, rational const& q, u_dependency* d);
        void var2interval(lpvar v, scoped_dep_interval& i);
        bool is_too_big(mpq const& q) const;
        bool propagate_down(monic const& m, lpvar u);
        bool propagate_value(dep_interval& range, lpvar v);
        bool propagate_value(dep_interval& range, lpvar v, unsigned power);
        void compute_product(unsigned start, monic const& m, scoped_dep_interval& i);
        bool propagate(monic const& m);
        void propagate_fixed_to_zero(monic const& m, lpvar fixed_to_zero);
        void propagate_fixed(monic const& m, rational const& k);
        void propagate_nonfixed(monic const& m, rational const& k, lpvar w);
        u_dependency* explain_fixed(monic const& m, rational const& k);
        lp::explanation get_explanation(u_dependency* dep);
        bool propagate_down(monic const& m, dep_interval& mi, lpvar v, unsigned power, dep_interval& product);
        void analyze_monomial(monic const& m, unsigned& num_free, lpvar& free_v, unsigned& power) const;
        bool is_free(lpvar v) const;
        bool is_zero(lpvar v) const;
        bool add_lemma();

        // monomial propagation
        void unit_propagate(monic & m);
        bool is_linear(monic const& m, lpvar& w, lpvar & fixed_to_zero);
        rational fixed_var_product(monic const& m, lpvar w);
        lpvar non_fixed_var(monic const& m);

        // fixed variable propagation
        unsigned m_fixed_var_qhead = 0;
        unsigned_vector m_fixed_var_trail;
        void propagate_fixed_vars();
        void propagate_fixed_var(lpvar v);
        void propagate_fixed_var(monic const& m, lpvar v);
    public:
        monomial_bounds(core* core);
        void propagate();
        void unit_propagate();
    }; 
}
