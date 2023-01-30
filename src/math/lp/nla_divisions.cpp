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
        if (lp::tv::is_term(x) || lp::tv::is_term(y) || lp::tv::is_term(q))
            return;
        m_idivisions.push_back({q, x, y});
        m_core.trail().push(push_back_vector(m_idivisions));
    }

    void divisions::add_rdivision(lpvar q, lpvar x, lpvar y) {
        if (x == null_lpvar || y == null_lpvar || q == null_lpvar)
            return;
        if (lp::tv::is_term(x) || lp::tv::is_term(y) || lp::tv::is_term(q))
            return;
        m_rdivisions.push_back({ q, x, y });
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

        auto monotonicity1 = [&](auto x1, auto& x1val, auto y1, auto& y1val, auto& q1, auto& q1val,
            auto x2, auto& x2val, auto y2, auto& y2val, auto& q2, auto& q2val) {
                if (y1val >= y2val && y2val > 0 && x1val <= x2val && q1val > q2val) {
                    new_lemma lemma(c, "y1 >= y2 > 0 & x1 <= x2 => x1/y1 <= x2/y2");
                    lemma |= ineq(term(y1, rational(-1), y2), llc::LT, 0);
                    lemma |= ineq(y2, llc::LE, 0);
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

#if 0
    bool check_idiv_bounds() {
        if (m_idiv_terms.empty()) {
            return true;
        }
        bool all_divs_valid = true;
        unsigned count = 0;
        unsigned offset = ctx().get_random_value();
        for (unsigned j = 0; j < m_idiv_terms.size(); ++j) {
            unsigned i = (offset + j) % m_idiv_terms.size();
            expr* n = m_idiv_terms[i];
            if (!ctx().is_relevant(n))
                continue;
            expr* p = nullptr, * q = nullptr;
            VERIFY(a.is_idiv(n, p, q));
            theory_var v = internalize_def(to_app(n));
            theory_var v1 = internalize_def(to_app(p));

            if (!is_registered_var(v1))
                continue;
            lp::impq q1 = get_ivalue(v1);
            rational q2;

            if (!q1.x.is_int() || q1.x.is_neg() || !q1.y.is_zero()) {
                // TBD
                // q1 = 223/4, q2 = 2, r = 219/8 
                // take ceil(q1), floor(q1), ceil(q2), floor(q2), for floor(q2) > 0
                // then 
                //      p/q <= ceil(q1)/floor(q2) => n <= div(ceil(q1), floor(q2))
                //      p/q >= floor(q1)/ceil(q2) => n >= div(floor(q1), ceil(q2))
                continue;
            }


            if (a.is_numeral(q, q2) && q2.is_pos()) {
                if (!a.is_bounded(n)) {
                    TRACE("arith", tout << "unbounded " << expr_ref(n, m) << "\n";);
                    continue;
                }
                if (!is_registered_var(v))
                    continue;
                lp::impq val_v = get_ivalue(v);
                if (val_v.y.is_zero() && val_v.x == div(q1.x, q2))
                    continue;

                TRACE("arith", tout << get_value(v) << " != " << q1 << " div " << q2 << "\n";);
                rational div_r = div(q1.x, q2);
                // p <= q * div(q1, q) + q - 1 => div(p, q) <= div(q1, q2)
                // p >= q * div(q1, q) => div(q1, q) <= div(p, q)
                rational mul(1);
                rational hi = q2 * div_r + q2 - 1;
                rational lo = q2 * div_r;

                // used to normalize inequalities so they 
                // don't appear as 8*x >= 15, but x >= 2
                expr* n1 = nullptr, * n2 = nullptr;
                if (a.is_mul(p, n1, n2) && a.is_extended_numeral(n1, mul) && mul.is_pos()) {
                    p = n2;
                    hi = floor(hi / mul);
                    lo = ceil(lo / mul);
                }
                literal p_le_q1 = mk_literal(a.mk_le(p, a.mk_numeral(hi, true)));
                literal p_ge_q1 = mk_literal(a.mk_ge(p, a.mk_numeral(lo, true)));
                literal n_le_div = mk_literal(a.mk_le(n, a.mk_numeral(div_r, true)));
                literal n_ge_div = mk_literal(a.mk_ge(n, a.mk_numeral(div_r, true)));
                {
                    scoped_trace_stream _sts(th, ~p_le_q1, n_le_div);
                    mk_axiom(~p_le_q1, n_le_div);
                }
                {
                    scoped_trace_stream _sts(th, ~p_ge_q1, n_ge_div);
                    mk_axiom(~p_ge_q1, n_ge_div);
                }

                all_divs_valid = false;
                ++count;


                TRACE("arith",
                    tout << q1 << " div " << q2 << "\n";
                literal_vector lits;
                lits.push_back(~p_le_q1);
                lits.push_back(n_le_div);
                ctx().display_literals_verbose(tout, lits) << "\n\n";
                lits[0] = ~p_ge_q1;
                lits[1] = n_ge_div;
                ctx().display_literals_verbose(tout, lits) << "\n";);
                continue;
            }
        }

        return all_divs_valid;
    }
#endif
    
}
