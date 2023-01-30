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

    void divisions::add_rdivision(lpvar r, lpvar x, lpvar y) {
        m_rdivisions.push_back({ r, x, y });
        m_core.trail().push(push_back_vector(m_rdivisions));
    }

    typedef lp::lar_term term;
    
    // y1 >= y2 > 0 & x1 <= x2 => x1/y1 <= x2/y2
    // y2 <= y1 < 0 & x1 >= x2 >= 0 => x1/y1 <= x2/y2
    // y2 <= y1 < 0 & x1 <= x2 <= 0 => x1/y1 >= x2/y2

    void divisions::check(vector<lemma>& lemmas) {
        core& c = m_core;        
        if (c.use_nra_model()) 
            return;

        auto monotonicity1 = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& r1, auto& r1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& r2, auto& r2val) {
                if (y1val >= y2val && y2val > 0 && x1val <= x2val && r1val > r2val) {
                    new_lemma lemma(c, "y1 >= y2 > 0 & x1 <= x2 => x1/y1 <= x2/y2");
                    lemma |= ineq(term(y1, rational(-1), y2), llc::LT, 0);
                    lemma |= ineq(y2, llc::LE, 0);
                    lemma |= ineq(term(x1, rational(-1), x2), llc::GT, 0);
                    lemma |= ineq(term(r1, rational(-1), r2), llc::LE, 0);
                    return true;
                }
                return false;
        };

        auto monotonicity2 = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& r1, auto& r1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& r2, auto& r2val) {
                if (y2val <= y1val && y1val < 0 && x1val >= x2val && x2val >= 0 && r1val > r2val) {
                    new_lemma lemma(c, "y2 <= y1 < 0 & x1 >= x2 >= 0 => x1/y1 <= x2/y2");
                    lemma |= ineq(term(y1, rational(-1), y2), llc::LT, 0);
                    lemma |= ineq(y1, llc::GE, 0);
                    lemma |= ineq(term(x1, rational(-1), x2), llc::LT, 0);
                    lemma |= ineq(x2, llc::LT, 0);
                    lemma |= ineq(term(r1, rational(-1), r2), llc::LE, 0);
                    return true;
                }
                return false;
        };

        auto monotonicity3 = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& r1, auto& r1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& r2, auto& r2val) {
                if (y2val <= y1val && y1val < 0 && x1val <= x2val && x2val <= 0 && r1val < r2val) {
                    new_lemma lemma(c, "y2 <= y1 < 0 & x1 <= x2 <= 0 => x1/y1 >= x2/y2");
                    lemma |= ineq(term(y1, rational(-1), y2), llc::LT, 0);
                    lemma |= ineq(y1, llc::GE, 0);
                    lemma |= ineq(term(x1, rational(-1), x2), llc::GT, 0);
                    lemma |= ineq(x2, llc::GT, 0);
                    lemma |= ineq(term(r1, rational(-1), r2), llc::GE, 0);
                    return true;
                }
                return false;
        };

        auto monotonicity = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& r1, auto& r1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& r2, auto& r2val) {
                if (monotonicity1(x1, x1val, y1, y1val, r1, r1val, x2, x2val, y2, y2val, r2, r2val))
                    return true;
                if (monotonicity1(x2, x2val, y2, y2val, r2, r2val, x1, x1val, y1, y1val, r1, r1val))
                    return true;
                if (monotonicity2(x1, x1val, y1, y1val, r1, r1val, x2, x2val, y2, y2val, r2, r2val))
                    return true;
                if (monotonicity2(x2, x2val, y2, y2val, r2, r2val, x1, x1val, y1, y1val, r1, r1val))
                    return true;
                if (monotonicity3(x1, x1val, y1, y1val, r1, r1val, x2, x2val, y2, y2val, r2, r2val))
                    return true;
                if (monotonicity3(x2, x2val, y2, y2val, r2, r2val, x1, x1val, y1, y1val, r1, r1val))
                    return true;
                return false;
        };

        for (auto const & [r, x, y] : m_idivisions) {
            if (!c.is_relevant(r))
                continue;
            auto xval = c.val(x);
            auto yval = c.val(y);
            auto rval = c.val(r);
            // idiv semantics
            if (!xval.is_int() || !yval.is_int() || yval == 0 || rval == div(xval, yval))
                continue;
            for (auto const& [r2, x2, y2] : m_idivisions) {
                if (r2 == r)
                    continue;
                if (!c.is_relevant(r2))
                    continue;
                auto x2val = c.val(x2);
                auto y2val = c.val(y2);
                auto r2val = c.val(r2);
                if (monotonicity(x, xval, y, yval, r, rval, x2, x2val, y2, y2val, r2, r2val))
                    return;
            }
        }

        for (auto const& [r, x, y] : m_rdivisions) {
            if (!c.is_relevant(r))
                continue;
            auto xval = c.val(x);
            auto yval = c.val(y);
            auto rval = c.val(r);
            // / semantics
            if (yval == 0 || rval == xval / yval)
                continue;
            for (auto const& [r2, x2, y2] : m_rdivisions) {
                if (r2 == r)
                    continue;
                if (!c.is_relevant(r2))
                    continue;
                auto x2val = c.val(x2);
                auto y2val = c.val(y2);
                auto r2val = c.val(r2);
                if (monotonicity(x, xval, y, yval, r, rval, x2, x2val, y2, y2val, r2, r2val))
                    return;
            }
        }
        
    }

    // if p is bounded, q a value, r = eval(p):
    // p <= q * div(r, q) + q - 1 => div(p, q) <= div(r, q)
    // p >= q * div(r, q)         => div(r, q) <= div(p, q)
    
}
