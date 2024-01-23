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
        if (c.lra.column_has_term(x) || c.lra.column_has_term(y) || c.lra.column_has_term(r))
            return l_undef;

        if (c.use_nra_model()) 
            return l_undef;

        auto xval = c.val(x);
        auto yval = c.val(y);
        auto rval = c.val(r);

        lemmas.reset();

        if (xval != 0 && yval == 0 && rval != 1) {
            new_lemma lemma(c, "x != 0 => x^0 = 1");
            lemma |= ineq(x, llc::EQ, rational::zero());
            lemma |= ineq(y, llc::NE, rational::zero());
            lemma |= ineq(r, llc::EQ, rational::one());
            return l_false;
        }

        if (xval == 0 && yval != 0 && rval != 0) {
            new_lemma lemma(c, "y != 0 => 0^y = 0");
            lemma |= ineq(x, llc::NE, rational::zero());
            lemma |= ineq(y, llc::EQ, rational::zero());
            lemma |= ineq(r, llc::EQ, rational::zero());
            return l_false;
        }

        if (xval > 0 && rval <= 0) {
            new_lemma lemma(c, "x > 0 => x^y > 0");
            lemma |= ineq(x, llc::LE, rational::zero());
            lemma |= ineq(r, llc::GT, rational::zero());
            return l_false;
        }

        if (xval > 1 && yval < 0 && rval >= 1) {
            new_lemma lemma(c, "x > 1, y < 0 => x^y < 1");
            lemma |= ineq(x, llc::LE, rational::one());
            lemma |= ineq(y, llc::GE, rational::zero());
            lemma |= ineq(r, llc::LT, rational::one());
            return l_false;
        }

        if (xval > 1 && yval > 0 && rval <= 1) {
            new_lemma lemma(c, "x > 1, y > 0 => x^y > 1");
            lemma |= ineq(x, llc::LE, rational::one());
            lemma |= ineq(y, llc::LE, rational::zero());
            lemma |= ineq(r, llc::GT, rational::one());
            return l_false;
        }

        if (xval >= 3 && yval != 0 && rval <= yval + 1) {
            new_lemma lemma(c, "x >= 3, y != 0 => x^y > ln(x)y + 1");
            lemma |= ineq(x, llc::LT, rational(3));
            lemma |= ineq(y, llc::EQ, rational::zero());
            lemma |= ineq(lp::lar_term(r, rational::minus_one(), y), llc::GT, rational::one());
            return l_false;
        }

        if (xval > 0 && yval.is_unsigned()) {
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
            if (!ynum.is_unsigned())
                return l_undef;
            if (!yden.is_unsigned())
                return l_undef;
            //   r = x^{yn/yd}
            // <=>
            //   r^yd = x^yn
            auto ryd = power(rval, yden.get_unsigned());
            auto xyn = power(xval, ynum.get_unsigned());
            if (ryd == xyn)
                return l_true;
        }

        return l_undef;

    }
    
}
