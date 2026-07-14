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

    void divisions::add_idivision(lpvar q, lpvar x, lpvar y, lpvar r) {
        if (x == null_lpvar || y == null_lpvar || q == null_lpvar || r == null_lpvar)
            return;
        m_idivisions.push_back({q, x, y, r});
        m_core.trail().push(push_back_vector(m_idivisions));
    }

    void divisions::add_rdivision(lpvar q, lpvar x, lpvar y, lpvar r) {
        if (x == null_lpvar || y == null_lpvar || q == null_lpvar || r == null_lpvar)
            return;
        m_rdivisions.push_back({ q, x, y, r });
        m_core.trail().push(push_back_vector(m_rdivisions));
    }

    void divisions::add_bounded_division(lpvar q, lpvar x, lpvar y, lpvar r) {
        if (x == null_lpvar || y == null_lpvar || q == null_lpvar || r == null_lpvar)
            return;
        if (m_core.lra.column_has_term(x) || m_core.lra.column_has_term(y) ||  m_core.lra.column_has_term(q))
            return;
        m_bounded_divisions.push_back({ q, x, y, r });
        m_core.trail().push(push_back_vector(m_bounded_divisions));
    }

    void divisions::add_divisibility(lpvar r, lpvar x, lpvar y, lpvar d) {
        if (x == null_lpvar || y == null_lpvar || r == null_lpvar || d == null_lpvar)
            return;
        m_divisibility.push_back({ r, x, y, d });
        m_core.trail().push(push_back_vector(m_divisibility));
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
                    lemma_builder lemma(c, "y1 >= y2 > 0 & 0 <= x1 <= x2 => x1/y1 <= x2/y2");
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
                    lemma_builder lemma(c, "y2 <= y1 < 0 & x1 >= x2 >= 0 => x1/y1 <= x2/y2");
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
                    lemma_builder lemma(c, "y2 <= y1 < 0 & x1 <= x2 <= 0 => x1/y1 >= x2/y2");
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

        for (auto const & [r, x, y, md] : m_idivisions) {
            if (!c.is_relevant(r))
                continue;
            auto xval = c.val(x);
            auto yval = c.val(y);
            auto rval = c.val(r);
            // idiv semantics
            if (!xval.is_int() || !yval.is_int() || yval == 0 || rval == div(xval, yval))
                continue;
            for (auto const& [q2, x2, y2, md2] : m_idivisions) {
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

        for (auto const& [r, x, y, md] : m_rdivisions) {
            if (!c.is_relevant(r))
                continue;
            auto xval = c.val(x);
            auto yval = c.val(y);
            auto rval = c.val(r);
            // / semantics
            if (yval == 0 || rval == xval / yval)
                continue;
            for (auto const& [q2, x2, y2, md2] : m_rdivisions) {
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

        check_mod_mult();
        check_linear_divisibility();
        check_mod_congruence();
    }

    // if p is bounded, q a value, r = eval(p):
    // p <= q * div(r, q) + q - 1 => div(p, q) <= div(r, q)
    // p >= q * div(r, q)         => div(r, q) <= div(p, q)

    void divisions::check_bounded_divisions() {
        core& c = m_core;
        unsigned offset = c.random(), sz = m_bounded_divisions.size();

        for (unsigned j = 0; j < sz; ++j) {
            unsigned i = (offset + j) % sz;
            auto [q, x, y, r] = m_bounded_divisions[i];
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
                lemma_builder lemma(c, "y = yv & x <= yv * div(xv, yv) + yv - 1 => div(p, y) <= div(xv, yv)");
                lemma |= ineq(y, llc::NE, yv);
                lemma |= ineq(x, llc::GT, hi);
                lemma |= ineq(q, llc::LE, div_v);
                return;
            }
            if (xv < lo) {
                lemma_builder lemma(c, "y = yv & x >= yv * div(xv, yv) => div(xv, yv) <= div(x, y)");
                lemma |= ineq(y, llc::NE, yv);
                lemma |= ineq(x, llc::LT, lo);
                lemma |= ineq(q, llc::GE, div_v);
                return;
            }
        }
    }

    // mod(factor, p) = 0 => mod(factor * k, p) = 0
    // For each division (q, x, y, r) where x is a monic m = f1 * f2 * ... * fk,
    // if some factor fi has mod(fi, p) = 0 (fixed), then mod(x, p) = 0.
    void divisions::check_mod_mult() {
        core& c = m_core;
        unsigned offset = c.random(), sz = m_bounded_divisions.size();

        for (unsigned j = 0; j < sz; ++j) {
            unsigned i = (offset + j) % sz;
            auto [q, x, y, r] = m_bounded_divisions[i];
            if (!c.is_relevant(q))
                continue;
            if (c.var_is_fixed_to_zero(r))
                continue;
            if (c.val(r).is_zero())
                continue;
            if (!c.is_monic_var(x))
                continue;
            auto yv = c.val(y);
            if (yv <= 0 || !yv.is_int())
                continue;
            auto const& m = c.emons()[x];
            for (lpvar f : m.vars()) {
                for (auto const& [q2, x2, y2, r2] : m_bounded_divisions) {
                    if (x2 != f)
                        continue;
                    if (c.val(y2) != yv)
                        continue;
                    if (!c.var_is_fixed_to_zero(r2))
                        continue;
                    // mod(factor, p) = 0 => mod(product, p) = 0
                    lemma_builder lemma(c, "mod(factor, p) = 0 => mod(factor * k, p) = 0");
                    lemma |= ineq(r2, llc::NE, 0);
                    lemma |= ineq(r, llc::EQ, 0);
                    return;
                }
            }
        }
    }

    // Linear divisibility closure:
    //   mod(a, y) = 0  &  x = c * a   (c an integer constant)  =>  mod(x, y) = 0.
    // The emitted clause
    //   (x - c*a != 0)  \/  (mod(a, y) != 0)  \/  (mod(x, y) = 0)
    // is a tautology for every integer c (under the Euclidean semantics of mod),
    // so the choice of c/a from the current model can never be unsound. We only
    // emit it when all three literals are false in the current model, which makes
    // the clause a real conflict/propagation and guarantees progress.
    void divisions::check_linear_divisibility() {
        core& c = m_core;
        unsigned sz = m_divisibility.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto const& [rx, x, y, dx] = m_divisibility[i];
            if (!c.is_relevant(rx))
                continue;
            if (c.val(rx).is_zero())   // mod(x, y) already 0 in model: nothing to refute
                continue;
            auto xval = c.val(x);
            if (xval.is_zero())
                continue;
            for (unsigned j = 0; j < sz; ++j) {
                if (i == j)
                    continue;
                auto const& [ra, a, y2, da] = m_divisibility[j];
                if (y2 != y && c.val(y2) != c.val(y)) // same divisor (by column or value)
                    continue;
                if (!c.is_relevant(ra))
                    continue;
                if (!c.val(ra).is_zero())  // need mod(a, y) = 0 in model
                    continue;
                auto aval = c.val(a);
                if (aval.is_zero())
                    continue;
                rational cc = xval / aval;
                if (!cc.is_int() || cc.is_zero())
                    continue;
                if (xval != cc * aval)     // ensure x = c*a holds exactly in the model
                    continue;
                lemma_builder lemma(c, "mod(a,y) = 0 & x = c*a => mod(x,y) = 0");
                lemma |= ineq(term(x, -cc, a), llc::NE, 0); // x - c*a != 0
                lemma |= ineq(ra, llc::NE, 0);              // mod(a, y) != 0
                lemma |= ineq(rx, llc::EQ, 0);              // mod(x, y) = 0
                return;
            }
        }
    }

    // Modular congruence over a shared (possibly symbolic) divisor.
    //
    // For each divisibility fact we have the Euclidean identities (asserted by
    // theory_lra::mk_idiv_mod_axioms):
    //      x = y * div(x,y) + mod(x,y),   0 <= mod(x,y) < |y|.
    // For two facts (rx = mod(x,y), dx = div(x,y)) and (rs = mod(s,y), ds = div(s,y))
    // sharing divisor y, subtracting the identities gives, for every integer delta,
    //      div(x,y) - div(s,y) = delta   =>   mod(x,y) - mod(s,y) = (x - s) - delta*y.
    // This is a tautology (entailed by the two identities) for any fixed integer
    // delta, so choosing delta from the current model can never be unsound. We emit
    // the clause
    //      (div(x,y) - div(s,y) != delta) \/ (mod(x,y) - mod(s,y) - (x - s) + delta*y = 0)
    // only when the equality literal is false in the model (delta taken as the model
    // value of div(x,y) - div(s,y)), which makes the clause a real propagation and
    // guarantees progress. This discharges linear congruences with a symbolic
    // modulus (e.g. mod(i + s, n) = i + mod(s, n)) that the nonlinear core does not
    // otherwise isolate.
    void divisions::check_mod_congruence() {
        core& c = m_core;
        unsigned sz = m_divisibility.size();
        for (unsigned i = 0; i < sz; ++i) {
            auto const& [rx, x, y, dx] = m_divisibility[i];
            if (!c.is_relevant(rx))
                continue;
            auto yval = c.val(y);
            if (yval.is_zero())   // mod/div uninterpreted when the divisor is 0
                continue;
            for (unsigned j = i + 1; j < sz; ++j) {
                auto const& [rs, s, y2, ds] = m_divisibility[j];
                if (!c.is_relevant(rs))
                    continue;
                if (y2 != y && c.val(y2) != yval) // same divisor (by column or value)
                    continue;
                rational delta = c.val(dx) - c.val(ds);
                rational lhs = c.val(rx) - c.val(rs);
                rational rhs = (c.val(x) - c.val(s)) - delta * yval;
                if (lhs == rhs)   // residue equation already holds: nothing to propagate
                    continue;
                lemma_builder lemma(c, "div(x,y) - div(s,y) = delta => mod(x,y) - mod(s,y) = (x - s) - delta*y");
                lemma |= ineq(term(dx, rational(-1), ds), llc::NE, delta); // div(x,y) - div(s,y) != delta
                term t;
                t.add_monomial(rational::one(), rx);
                t.add_monomial(rational(-1), rs);
                t.add_monomial(rational(-1), x);
                t.add_monomial(rational::one(), s);
                t.add_monomial(delta, y);
                lemma |= ineq(t, llc::EQ, 0); // mod(x,y) - mod(s,y) - x + s + delta*y = 0
                return;
            }
        }
    }
}
