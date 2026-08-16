/*++
  Copyright (c) 2026 Microsoft Corporation

  Module Name:

  nla_patcher.h

  Abstract:

  Patches the values of monic variables to agree with the products of
  their factor values, shrinking the set of monomials to refine.

  Author:
    Lev Nachmanson (levnach)

  --*/
#pragma once
#include "math/lp/nla_common.h"

namespace nla {
    class core;
    class patcher : common {
        bool         m_cautious_patching = true;
        lpvar        m_patched_var = 0;
        monic const* m_patched_monic = nullptr;

        bool var_breaks_correct_monic(lpvar j) const;
        bool var_breaks_correct_monic_as_factor(lpvar j, monic const& m) const;
        void update_to_refine_of_var(lpvar j);
        bool try_to_patch(const rational& v);
        bool is_patch_blocked(lpvar u, const lp::impq& ival) const;
        bool to_refine_is_correct() const;
        void patch_monomial(lpvar j);
        void patch_monomials_on_to_refine();
    public:
        patcher(core* c): common(c) {}
        void patch_monomials();
    };
}
