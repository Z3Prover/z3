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

    void divisions::add_idivision(lpvar q, lpvar x, lpvar y) {
        if (x == null_lpvar || y == null_lpvar || q == null_lpvar)
            return;
        m_idivisions.push_back({q, x, y});
        m_core.trail().push(push_back_vector(m_idivisions));
    }

    void divisions::add_rdivision(lpvar q, lpvar x, lpvar y) {
        if (x == null_lpvar || y == null_lpvar || q == null_lpvar)
            return;
        m_rdivisions.push_back({ q, x, y });
        m_core.trail().push(push_back_vector(m_rdivisions));
    }

    void divisions::add_bounded_division(lpvar q, lpvar x, lpvar y) {
        if (x == null_lpvar || y == null_lpvar || q == null_lpvar)
            return;
        if (m_core.lra.column_has_term(x) || m_core.lra.column_has_term(y) ||  m_core.lra.column_has_term(q))
            return;
        m_bounded_divisions.push_back({ q, x, y });
        m_core.trail().push(push_back_vector(m_bounded_divisions));
    }

    typedef lp::lar_term term;
    
    // y1 >= y2 > 0 & x1 <= x2 => x1/y1 <= x2/y2
    // y2 <= y1 < 0 & x1 >= x2 >= 0 => x1/y1 <= x2/y2
    // y2 <= y1 < 0 & x1 <= x2 <= 0 => x1/y1 >= x2/y2

    void divisions::check() {
        core& c = m_core;
        if (c.use_nra_model()) 
            return;

        auto monotonicity1 = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& q1, auto& q1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& q2, auto& q2val) {
                if (y1val >= y2val && y2val > 0 && 0 <= x1val && x1val <= x2val && q1val > q2val) {
                    new_lemma lemma(c, "y1 >= y2 > 0 & 0 <= x1 <= x2 => x1/y1 <= x2/y2");
                    lemma |= ineq(term(y1, rational(-1), y2), llc::LT, 0);
                    lemma |= ineq(y2, llc::LE, 0);
                    lemma |= ineq(x1, llc::LT, 0);
                    lemma |= ineq(term(x1, rational(-1), x2), llc::GT, 0);
                    lemma |= ineq(term(q1, rational(-1), q2), llc::LE, 0);
                    return true;
                }
                return false;
        };

        auto monotonicity2 = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& q1, auto& q1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& q2, auto& q2val) {
                if (y2val <= y1val && y1val < 0 && x1val >= x2val && x2val >= 0 && q1val > q2val) {
                    new_lemma lemma(c, "y2 <= y1 < 0 & x1 >= x2 >= 0 => x1/y1 <= x2/y2");
                    lemma |= ineq(term(y1, rational(-1), y2), llc::LT, 0);
                    lemma |= ineq(y1, llc::GE, 0);
                    lemma |= ineq(term(x1, rational(-1), x2), llc::LT, 0);
                    lemma |= ineq(x2, llc::LT, 0);
                    lemma |= ineq(term(q1, rational(-1), q2), llc::LE, 0);
                    return true;
                }
                return false;
        };

        auto monotonicity3 = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& q1, auto& q1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& q2, auto& q2val) {
                if (y2val <= y1val && y1val < 0 && x1val <= x2val && x2val <= 0 && q1val < q2val) {
                    new_lemma lemma(c, "y2 <= y1 < 0 & x1 <= x2 <= 0 => x1/y1 >= x2/y2");
                    lemma |= ineq(term(y1, rational(-1), y2), llc::LT, 0);
                    lemma |= ineq(y1, llc::GE, 0);
                    lemma |= ineq(term(x1, rational(-1), x2), llc::GT, 0);
                    lemma |= ineq(x2, llc::GT, 0);
                    lemma |= ineq(term(q1, rational(-1), q2), llc::GE, 0);
                    return true;
                }
                return false;
        };

        auto monotonicity = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& q1, auto& q1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& q2, auto& q2val) {
                if (monotonicity1(x1, x1val, y1, y1val, q1, q1val, x2, x2val, y2, y2val, q2, q2val))
                    return true;
                if (monotonicity1(x2, x2val, y2, y2val, q2, q2val, x1, x1val, y1, y1val, q1, q1val))
                    return true;
                if (monotonicity2(x1, x1val, y1, y1val, q1, q1val, x2, x2val, y2, y2val, q2, q2val))
                    return true;
                if (monotonicity2(x2, x2val, y2, y2val, q2, q2val, x1, x1val, y1, y1val, q1, q1val))
                    return true;
                if (monotonicity3(x1, x1val, y1, y1val, q1, q1val, x2, x2val, y2, y2val, q2, q2val))
                    return true;
                if (monotonicity3(x2, x2val, y2, y2val, q2, q2val, x1, x1val, y1, y1val, q1, q1val))
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
            for (auto const& [q2, x2, y2] : m_idivisions) {
                if (q2 == r)
                    continue;
                if (!c.is_relevant(q2))
                    continue;
                auto x2val = c.val(x2);
                auto y2val = c.val(y2);
                auto q2val = c.val(q2);
                if (monotonicity(x, xval, y, yval, r, rval, x2, x2val, y2, y2val, q2, q2val)) 
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
            for (auto const& [q2, x2, y2] : m_rdivisions) {
                if (q2 == r)
                    continue;
                if (!c.is_relevant(q2))
                    continue;
                auto x2val = c.val(x2);
                auto y2val = c.val(y2);
                auto q2val = c.val(q2);
                if (monotonicity(x, xval, y, yval, r, rval, x2, x2val, y2, y2val, q2, q2val))
                    return;
            }
        }
        
    }

    // if p is bounded, q a value, r = eval(p):
    // p <= q * div(r, q) + q - 1 => div(p, q) <= div(r, q)
    // p >= q * div(r, q)         => div(r, q) <= div(p, q)

    void divisions::check_bounded_divisions() {
        core& c = m_core;
        unsigned offset = c.random(), sz = m_bounded_divisions.size();        

        for (unsigned j = 0; j < sz; ++j) {
            unsigned i = (offset + j) % sz;
            auto [q, x, y] = m_bounded_divisions[i];
            if (!c.is_relevant(q))
                continue;
            auto xv = c.val(x);
            auto yv = c.val(y);
            auto qv = c.val(q);
            if (xv < 0 || !xv.is_int())
                continue;
            if (yv <= 0 || !yv.is_int())
                continue;
            if (qv == div(xv, yv))
                continue;

            rational div_v = div(xv, yv);
            // y = yv & x <= yv * div(xv, yv) + yv - 1 => div(x, y) <= div(xv, yv)
            // y = yv & x >= y * div(xv, yv) => div(xv, yv) <= div(x, y)
            rational mul(1);
            rational hi = yv * div_v + yv - 1;
            rational lo = yv * div_v;
            if (xv > hi) {
                new_lemma lemma(c, "y = yv & x <= yv * div(xv, yv) + yv - 1 => div(p, y) <= div(xv, yv)");
                lemma |= ineq(y, llc::NE, yv); 
                lemma |= ineq(x, llc::GT, hi); 
                lemma |= ineq(q, llc::LE, div_v);  
                return;
            }
            if (xv < lo) {
                new_lemma lemma(c, "y = yv & x >= yv * div(xv, yv) => div(xv, yv) <= div(x, y)");
                lemma |= ineq(y, llc::NE, yv);
                lemma |= ineq(x, llc::LT, lo);
                lemma |= ineq(q, llc::GE, div_v);
                return;
            }
        }
    }    
}
