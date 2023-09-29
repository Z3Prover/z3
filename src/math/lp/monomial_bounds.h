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

        u_dependency* explain_fixed(const svector<lpvar>& vars, lpvar non_fixed);
        void var2interval(lpvar v, scoped_dep_interval& i);
        bool is_too_big(mpq const& q) const;
        bool propagate_value(dep_interval& range, lpvar v);
        bool propagate_value(dep_interval& range, lpvar v, unsigned power);
        void compute_product(unsigned start, monic const& m, scoped_dep_interval& i);
        bool propagate(monic const& m);
        bool propagate_down(monic const& m, dep_interval& mi, lpvar v, unsigned power, dep_interval& product);
        void analyze_monomial(monic const& m, unsigned& num_free, lpvar& free_v, unsigned& power) const;
        bool is_free(lpvar v) const;
        bool is_zero(lpvar v) const;

        // monomial propagation
        bool_vector m_propagated;
        bool is_linear(monic const& m, lpvar& zero_var, lpvar& non_fixed);
    public:
        monomial_bounds(core* core);
        void propagate();
        void propagate_nonfixed(lpvar monic_var, const svector<lpvar>& vars, lpvar non_fixed, const rational& k);    
    }; 
}
