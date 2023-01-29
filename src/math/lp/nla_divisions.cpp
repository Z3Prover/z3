/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

  nla_divisions.cpp

Author:
  Lev Nachmanson (levnach)
  Nikolaj Bjorner (nbjorner)

Description:

  Check divisions

--*/
#include "math/lp/nla_core.h"

namespace nla {

    void divisions::add_idivision(lpvar r, lpvar x, lpvar y) {
        m_idivisions.push_back({r, x, y});
        m_core.trail().push(push_back_vector(m_idivisions));
    }

    typedef lp::lar_term term;
    
    // y1 >= y2 > 0 & x1 <= x2 => x1/y1 <= x2/y2
    // y2 <= y1 < 0 & x1 >= x2 => x1/y1 <= x2/y2
    void divisions::check(vector<lemma>& lemmas) {
        core& c = m_core;        
        if (c.use_nra_model()) 
            return;

        for (auto const & [r, x, y] : m_idivisions) {
            auto xval = c.val(x);
            auto yval = c.val(y);
            auto rval = c.val(r);
            if (!c.var_is_int(x)) 
                continue;
            if (yval == 0)
                continue;
            // idiv semantics
            if (rval == div(xval, yval))
                continue;
            for (auto const& [r2, x2, y2] : m_idivisions) {
                if (r2 == r)
                    continue;
                auto x2val = c.val(x2);
                auto y2val = c.val(y2);
                auto r2val = c.val(r2);
                if (yval >= y2val && y2val > 0 && xval <= x2val && rval > r2val) {
                    new_lemma lemma(c, "y1 >= y2 > 0 & x1 <= x2 => x1/y1 <= x2/y2");
                    lemma |= ineq(term(y, rational(-1), y2), llc::LT, rational::zero());
                    lemma |= ineq(y2, llc::LE, rational::zero());
                    lemma |= ineq(term(x, rational(-1), x2), llc::GT, rational::zero());
                    lemma |= ineq(term(r, rational(-1), r2), llc::LE, rational::zero());
                    return;
                }
            }
        }
        
    }
    
}
