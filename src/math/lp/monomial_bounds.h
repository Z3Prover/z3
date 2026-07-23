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

        bool tighten_lp_bound(dep_interval const &range, lpvar v, unsigned p);
        bool tighten_lp_upper_bound(dep_interval const& range, lpvar v, unsigned p);
        bool tighten_lp_lower_bound(dep_interval const& range, lpvar v, unsigned p);
        bool tighten_lp_bound(dep_interval &mi, lpvar v, unsigned power, dep_interval &product);
 
        void propagate_lp_bound(lpvar v, lp::lconstraint_kind cmp, rational const &q, u_dependency *d);


        bool should_propagate_lower(dep_interval const& range, lpvar v, unsigned p);
        bool should_propagate_upper(dep_interval const& range, lpvar v, unsigned p);

        void var2interval(lpvar v, scoped_dep_interval& i);
        bool is_too_big(mpq const& q) const;
        void compute_product(unsigned start, monic const& m, scoped_dep_interval& i);
        bool generate_lemma(monic const& m);
        bool tighten_lp(monic const& m);
        bool propagate_fixed_to_zero(monic const& m, lpvar fixed_to_zero);
        bool propagate_fixed(monic const& m, rational const& k);
        bool propagate_nonfixed(monic const& m, rational const& k, lpvar w);
        u_dependency* explain_fixed(monic const& m, rational const& k);
        lp::explanation get_explanation(u_dependency* dep);
        bool propagate_shared_factor(monic const& m);
        bool propagate_binomial_sign(monic const& m);
        void analyze_monomial(monic const& m, unsigned& num_free, lpvar& free_v, unsigned& power) const;
        bool is_free(lpvar v) const;
        bool is_zero(lpvar v) const;
        bool add_lemma();

        // linear-monomial equality propagation:
        // when all but one variable of a monomial are fixed, the monomial is
        // linear and its value/equality can be propagated into the LP solver.
        bool propagate_linear_monomial(monic & m);
        bool propagate_linear_monomials();
        bool is_linear(monic const& m, lpvar& w, lpvar & fixed_to_zero);
        rational fixed_var_product(monic const& m, lpvar w);
    public:
        monomial_bounds(core* core);
        void generate_lemmas();
        bool tighten_lp_bounds();
    }; 
}
