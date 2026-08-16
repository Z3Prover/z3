/*++
  Copyright (c) 2026 Microsoft Corporation

  Module Name:

  nla_explanations.h

  Abstract:

  Explains inequalities by the bounds of the variables of their terms,
  collects the equivalences x = +-y implied by octagon terms +-x +- y
  fixed to zero, and explains by these equivalences.

  Author:
    Lev Nachmanson (levnach)

  --*/
#pragma once
#include "math/lp/nla_common.h"

namespace nla {
    class core;
    class lemma_builder;
    class explanations : common {
    public:
        explanations(core* c): common(c) {}

        // return true iff the negation of the ineq can be derived from the constraints
        bool explain_ineq(lemma_builder& lemma, const lp::lar_term& t, llc cmp, const rational& rs);
        bool explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;
        bool explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const;
        bool explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;
        bool explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const;
        bool explain_by_equiv(const lp::lar_term& t, lp::explanation& e) const;

        // x is equivalent to y if x = +-y
        void init_vars_equivalence();
        void collect_equivs();
        bool is_octagon_term(const lp::lar_term& t, bool& sign, lpvar& i, lpvar& j) const;
        void add_equivalence_maybe(const lp::lar_term* t, u_dependency* c0, u_dependency* c1);
    };
}
