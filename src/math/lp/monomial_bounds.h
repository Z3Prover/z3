/*++
  Copyright (c) 2020 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/
#pragma once

#include "math/lp/nla_common.h"
#include "math/lp/nla_intervals.h"
#include "math/lp/u_set.h"

namespace nla {
    class core;
    class monomial_bounds : common {
        dep_intervals& dep;
        void var2interval(lpvar v, scoped_dep_interval& i);
        bool propagate_down(monic const& m, lpvar u);
        bool propagate_value(dep_interval& range, lpvar v);
        bool propagate_value(dep_interval& range, lpvar v, unsigned power);
        void compute_product(unsigned start, monic const& m, scoped_dep_interval& i);
        bool propagate(monic const& m);
        bool propagate_down(monic const& m, dep_interval& mi, lpvar v, unsigned power, dep_interval& product);
        void analyze_monomial(monic const& m, unsigned& num_free, lpvar& free_v, unsigned& power) const;
        bool is_free(lpvar v) const;
        bool is_zero(lpvar v) const;
    public:
        monomial_bounds(core* core);
        void operator()();
    }; 
}
