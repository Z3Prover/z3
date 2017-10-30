/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    tst_inf_rational.cpp

Abstract:

    Test for Rational numbers with infinitesimals

Author:

    Leonardo de Moura (leonardo) 2006-09-18.
    Nikolaj Bjorner (nbjorner) 2006-10-24.

Revision History:

--*/

#include "util/inf_rational.h"

static void tst0() {
    inf_rational n(rational(0), false);
    TRACE("inf_rational", tout << n << "\n";);
    ENSURE(n < inf_rational::zero());
    ENSURE(!(n >= inf_rational::zero()));
}

void test_inc_dec(
    inf_rational& r,
    inf_rational const & b_8_5,
    inf_rational const & b_7_5,
    inf_rational const & b_7_10,
    inf_rational const & b_17_10
    )
{
    r += rational(1,5);
    ENSURE (r == b_8_5);
    r -= rational(1,5);
    ENSURE (r == b_7_5);

    r += inf_rational(1,5);
    ENSURE (r == b_8_5);
    r -= inf_rational(1,5);
    ENSURE (r == b_7_5);

    r /= rational(2,1);
    ENSURE (r == b_7_10);
    inf_rational r_pre = r++;
    ENSURE (r_pre == b_7_10);
    ENSURE (r == b_17_10);
    inf_rational r_post = --r;
    ENSURE (r_post == b_7_10);
    ENSURE (r == b_7_10);
    r_post = ++r;
    ENSURE (r_post == b_17_10);
    ENSURE (r == b_17_10);
    r_pre = r--;
    ENSURE (r_pre == b_17_10);
    ENSURE (r == b_7_10);

    r_pre = r;
    r_pre += inf_rational(1,2);
    r_post = r_pre;
    r_post -= inf_rational(1,2);
    ENSURE(r == r_post);
    ENSURE(r + inf_rational(1,2) == r_pre);

    r_pre = r;
    r_pre /= rational(2,1);
    r_post = r_pre;
    r_post /= rational(1,2);
    ENSURE(r == r_post);
    ENSURE(rational(1,2) * r == r_pre);
    ENSURE(r == r_pre / rational(1,2));
       
}

void
tst_inf_rational()
{
    tst0();

    inf_rational r1;
    inf_rational r2(r1);
    ENSURE (r1 == r2);
    inf_rational r3(1);
    inf_rational r4(0);
    ENSURE (r4 == r1);
    ENSURE (r3 != r4);
    inf_rational r5(0,1);
    inf_rational r6(1,1);
    inf_rational r7(2,2);
    inf_rational r8(7,5);
    ENSURE (r1 == r5);
    ENSURE (r6 == r3);
    ENSURE (r7 == r3);
    inf_rational r9(rational(7,5));
    ENSURE (r8 == r9);
    r9.reset();
    ENSURE (r1 == r9);
    ENSURE (r1.is_int());
    ENSURE (!r8.is_int());
    ENSURE (0 == r1.get_int64());
    r9 = r8;
    ENSURE (r8 == r9);
    inf_rational n = numerator(r7);
    inf_rational d = denominator(r7);


    {  
        inf_rational b_8_5  = inf_rational(8,5);
        inf_rational b_7_5  = inf_rational(7,5);
        inf_rational b_7_10 = inf_rational(7,10);
        inf_rational b_17_10  = inf_rational(17,10);
       
        inf_rational r = r9;
        test_inc_dec(r, b_8_5, b_7_5, b_7_10, b_17_10);
    }

    {
        inf_rational b_8_5  = inf_rational(rational(8,5),true);
        inf_rational b_7_5  = inf_rational(rational(7,5),true);
        inf_rational b_7_10 = inf_rational(rational(7,5),true) / rational(2);
        inf_rational b_17_10  = b_7_10 + inf_rational(1);

        inf_rational r (rational(7,5),true);
        test_inc_dec(r, b_8_5, b_7_5, b_7_10, b_17_10);
    }


    ENSURE(inf_rational(rational(1,2),true) > inf_rational(rational(1,2)));
    ENSURE(inf_rational(rational(1,2),false) < inf_rational(rational(1,2)));
    ENSURE(inf_rational(rational(1,2),true) >= inf_rational(rational(1,2)));
    ENSURE(inf_rational(rational(1,2)) >= inf_rational(rational(1,2),false));
    ENSURE(inf_rational(rational(1,2),false) != inf_rational(rational(1,2)));
    ENSURE(inf_rational(rational(1,2),true) != inf_rational(rational(1,2)));
    ENSURE(inf_rational(rational(1,2),false) != inf_rational(rational(1,2),true));
    
    inf_rational h_neg(rational(1,2),false);
    inf_rational h_pos(rational(1,2),true);
    
    h_neg.neg();
    ENSURE(h_neg == -inf_rational(rational(1,2),false));
    h_neg.neg();
    ENSURE(h_neg == inf_rational(rational(1,2),false));
    
    ENSURE(r1.is_zero() && !r1.is_one() && !r1.is_neg() && r1.is_nonneg() && r1.is_nonpos() && !r1.is_pos());
    ENSURE(!r3.is_zero() && r3.is_one() && !r3.is_neg() && r3.is_nonneg() && !r3.is_nonpos() && r3.is_pos());
    
    ENSURE(floor(inf_rational(rational(1,2),false)) == rational());
    ENSURE(floor(inf_rational(rational(1,2))) == rational());
    ENSURE(floor(inf_rational(rational(),false)) == rational(-1));
    ENSURE(floor(inf_rational(rational())) == rational());
    ENSURE(floor(inf_rational(rational(),true)) == rational());
    ENSURE(floor(inf_rational(rational(1),false)) == rational());
    ENSURE(floor(inf_rational(rational(1))) == rational(1));
    ENSURE(floor(inf_rational(rational(1),true)) == rational(1));

    ENSURE(ceil(inf_rational(rational(1,2),false)) == rational(1));
    ENSURE(ceil(inf_rational(rational(1,2))) == rational(1));
    ENSURE(ceil(inf_rational(rational(),false)) == rational());
    ENSURE(ceil(inf_rational(rational())) == rational());
    ENSURE(ceil(inf_rational(rational(),true)) == rational(1));
    ENSURE(ceil(inf_rational(rational(1),false)) == rational(1));
    ENSURE(ceil(inf_rational(rational(1))) == rational(1));
    ENSURE(ceil(inf_rational(rational(1),true)) == rational(2));

    inf_rational x(rational(1,2),true);
    inf_rational y(1,2);
    x.swap(y);
    ENSURE (x == inf_rational(1,2));
    ENSURE (y == inf_rational(rational(1,2),true));

    ENSURE(inf_rational(1,2) == abs(-inf_rational(1,2)));
    
}



