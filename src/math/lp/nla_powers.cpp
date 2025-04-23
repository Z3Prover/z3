/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

  nla_powers.cpp

Author:
  Lev Nachmanson (levnach)
  Nikolaj Bjorner (nbjorner)

Description:
  Refines bounds on powers.
  
  Reference: TOCL-2018, Cimatti et al.


Special cases:

1. Exponentiation. x is fixed numeral a.

TOCL18 axioms:
   a^y > 0                     (if a > 0)
   y = 0 <=> a^y = 1           (if a != 0)
   y < 0 <=> a^y < 1           (if a > 1)
   y > 0 <=> a^y > 1           (if a > 1)
   y != 0 <=> a^y > y + 1      (if a >= 2)
   y1 < y2 <=> a^y1 < a^y2 (**)

Other special case:

   y = 1 <=> a^y = a

TOCL18 approach: Polynomial abstractions

Taylor: a^y = sum_i ln(a)*y^i/i!

Truncation: P(n, a) = sum_{i=0}^n ln(a)*y^i/i! = 1 + ln(a)*y + ln(a)^2*y^2/2 + 

y = 0: handled by axiom a^y = 1
y < 0: P(2n-1, y) <= a^y <= P(2n, y), n > 0 because Taylor contribution is negative at odd powers.
y > 0: P(n, y) <= a^y <= P(n, y)*(1 - y^{n+1}/(n+1)!)


2. Powers. y is fixed positive integer.

3. Other

General case:

  For now the solver integrates just weak monotonicity lemmas:

  - x >= x0 > 0, y >= y0 => x^y >= x0^y0
  - 0 < x <= x0, y <= y0 => x^y <= x0^y0


TODO:

- Comprehensive integration for truncation polynomial approximation.
- TOCL18 approach includes refinement loop based on precision epsilon.
- accept solvability if r is within a small range of x^y, when x^y is not rational.
- integrate algebraic numbers, or even extension fields (for 'e').
- integrate monotonicy axioms (**) by tracking exponents across instances.

anum isn't initialized unless nra_solver is invoked.
there is no proviso for using algebraic numbers outside of the nra solver.
so either we have a rational refinement version _and_ an algebraic numeral refinement
loop or we introduce algebraic numerals outside of the nra_solver

scoped_anum xval(am()), yval(am()), rval(am());

am().set(xval, am_value(x));
am().set(yval, am_value(y));
am().set(rval, am_value(r));

--*/
#include "math/lp/nla_core.h"

namespace nla {
    
    lbool powers::check(lpvar r, lpvar x, lpvar y, vector<lemma>& lemmas) {
        TRACE("nla", tout << r << " == " << x << "^" << y << "\n");
        core& c = m_core;
        if (x == null_lpvar || y == null_lpvar || r == null_lpvar)
            return l_undef;
        // if (c.lra.column_has_term(x) || c.lra.column_has_term(y) || c.lra.column_has_term(r))
        //     return l_undef;

        lemmas.reset();

        auto x_exp_0 = [&]() {
            new_lemma lemma(c, "x != 0 => x^0 = 1");
            lemma |= ineq(x, llc::EQ, rational::zero());
            lemma |= ineq(y, llc::NE, rational::zero());
            lemma |= ineq(r, llc::EQ, rational::one());
            return l_false;
        };

        auto zero_exp_y = [&]() {
            new_lemma lemma(c, "y != 0 => 0^y = 0");
            lemma |= ineq(x, llc::NE, rational::zero());
            lemma |= ineq(y, llc::EQ, rational::zero());
            lemma |= ineq(r, llc::EQ, rational::zero());
            return l_false;
        };

        auto x_gt_0 = [&]() {
            new_lemma lemma(c, "x > 0 => x^y > 0");
            lemma |= ineq(x, llc::LE, rational::zero());
            lemma |= ineq(r, llc::GT, rational::zero());
            return l_false;
        };

        auto y_lt_1 = [&]() {
            new_lemma lemma(c, "x > 1, y < 0 => x^y < 1");
            lemma |= ineq(x, llc::LE, rational::one());
            lemma |= ineq(y, llc::GE, rational::zero());
            lemma |= ineq(r, llc::LT, rational::one());
            return l_false;
        };

        auto y_gt_1 = [&]() {
            new_lemma lemma(c, "x > 1, y > 0 => x^y > 1");
            lemma |= ineq(x, llc::LE, rational::one());
            lemma |= ineq(y, llc::LE, rational::zero());
            lemma |= ineq(r, llc::GT, rational::one());
            return l_false;
        };

        auto x_ge_3 = [&]() {
            new_lemma lemma(c, "x >= 3, y != 0 => x^y > ln(x)y + 1");
            lemma |= ineq(x, llc::LT, rational(3));
            lemma |= ineq(y, llc::EQ, rational::zero());
            lemma |= ineq(lp::lar_term(r, rational::minus_one(), y), llc::GT, rational::one());
            return l_false;
        };

        bool use_rational = !c.use_nra_model();
        rational xval, yval, rval;
        if (use_rational) {
            xval = c.val(x);
            yval = c.val(y);
            rval = c.val(r);
        } 
        else {
            auto& am = c.m_nra.am();
            if (am.is_rational(c.m_nra.value(x)) &&
                am.is_rational(c.m_nra.value(y)) &&
                am.is_rational(c.m_nra.value(r))) {
                am.to_rational(c.m_nra.value(x), xval);
                am.to_rational(c.m_nra.value(y), yval);
                am.to_rational(c.m_nra.value(r), rval);
                use_rational = true;
            }
        }

        if (use_rational) {
            if (xval != 0 && yval == 0 && rval != 1)
                return x_exp_0();
            else if (xval == 0 && yval != 0 && rval != 0)
                return zero_exp_y();
            else if (xval > 0 && rval <= 0)
                return x_gt_0();
            else if (xval > 1 && yval < 0 && rval >= 1)
                return y_lt_1();
            else if (xval > 1 && yval > 0 && rval <= 1)
                return y_gt_1();
            else if (xval >= 3 && yval != 0 && rval <= yval + 1)
                return x_ge_3();
            else if (xval > 0 && yval.is_unsigned()) {
                auto r2val = power(xval, yval.get_unsigned());
                if (rval == r2val)
                    return l_true;
                if (c.random() % 2 == 0) {
                    new_lemma lemma(c, "x == x0, y == y0 => r = x0^y0");
                    lemma |= ineq(x, llc::NE, xval);
                    lemma |= ineq(y, llc::NE, yval);
                    lemma |= ineq(r, llc::EQ, r2val);
                    return l_false;
                }
                if (yval > 0 && r2val > rval) {
                    new_lemma lemma(c, "x >= x0 > 0, y >= y0 > 0 => r >= x0^y0");
                    lemma |= ineq(x, llc::LT, xval);
                    lemma |= ineq(y, llc::LT, yval);
                    lemma |= ineq(r, llc::GE, r2val);
                    return l_false;
                }
                if (r2val < rval) {
                    new_lemma lemma(c, "0 < x <= x0, y <= y0 => r <= x0^y0");
                    lemma |= ineq(x, llc::LE, rational::zero());
                    lemma |= ineq(x, llc::GT, xval);
                    lemma |= ineq(y, llc::GT, yval);
                    lemma |= ineq(r, llc::LE, r2val);
                    return l_false;
                }
            }
            if (xval > 0 && yval > 0 && !yval.is_int()) {
                auto ynum = numerator(yval);
                auto yden = denominator(yval);
                //   r = x^{yn/yd}
                // <=>
                //   r^yd = x^yn
                if (ynum.is_unsigned() && yden.is_unsigned()) {
                    auto ryd = power(rval, yden.get_unsigned());
                    auto xyn = power(xval, ynum.get_unsigned());
                    if (ryd == xyn)
                        return l_true;
                }
            }
        }

        if (!use_rational) {
            auto& am = c.m_nra.am();
            scoped_anum xval(am), yval(am), rval(am);
            am.set(xval, c.m_nra.value(x));
            am.set(yval, c.m_nra.value(y));
            am.set(rval, c.m_nra.value(r));
            if (xval != 0 && yval == 0 && rval != 1)
                return x_exp_0();
            else if (xval == 0 && yval != 0 && rval != 0)
                return zero_exp_y();
            else if (xval > 0 && rval <= 0)
                return x_gt_0();
            else if (xval > 1 && yval < 0 && rval >= 1)
                return y_lt_1();
            else if (xval > 1 && yval > 0 && rval <= 1)
                return y_gt_1();
            else if (xval >= 3 && yval != 0 && rval <= yval + 1)
                return x_ge_3();
            else if (xval > 0 && yval > 0 && am.is_rational(yval)) {
                rational yr;
                am.to_rational(yval, yr);
                auto ynum = numerator(yr);
                auto yden = denominator(yr);
                //   r = x^{yn/yd}
                // <=>
                //   r^yd = x^yn
                if (ynum.is_unsigned() && yden.is_unsigned()) {
                    am.set(rval, power(rval, yden.get_unsigned()));
                    am.set(xval, power(xval, ynum.get_unsigned()));
                    if (rval == xval)
                        return l_true;
                }
            }
        } 

        return l_undef;
    }

    
}
