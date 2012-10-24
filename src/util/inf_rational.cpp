/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    inf_rational.cpp

Abstract:

    Rational numbers with infenitesimals

Author:

    Nikolaj Bjorner (nbjorner) 2006-12-05.

Revision History:

--*/
#include"inf_rational.h"

inf_rational inf_rational::m_zero(0);
inf_rational inf_rational::m_one(1);
inf_rational inf_rational::m_minus_one(-1);

inf_rational inf_mult(inf_rational const& r1, inf_rational const& r2) 
{
    inf_rational result;
    result.m_first = r1.m_first * r2.m_first;
    result.m_second = (r1.m_first * r2.m_second) + (r1.m_second * r2.m_first);

    if (r1.m_second.is_pos() && r2.m_second.is_neg()) {
        --result.m_second;
    }
    else if (r1.m_second.is_neg() && r2.m_second.is_pos()) {
        --result.m_second;
    }
    return result;
}

inf_rational sup_mult(inf_rational const& r1, inf_rational const& r2) 
{
    inf_rational result;
    result.m_first = r1.m_first * r2.m_first;
    result.m_second = (r1.m_first * r2.m_second) + (r1.m_second * r2.m_first);

    if (r1.m_second.is_pos() && r2.m_second.is_pos()) {
        ++result.m_second;
    }
    else if (r1.m_second.is_neg() && r2.m_second.is_neg()) {
        ++result.m_second;
    }
    return result;
}

//
// Find rationals c, x, such that c + epsilon*x <= r1/r2
// 
// let r1 = a + d_1
// let r2 = b + d_2
// 
// suppose b != 0:
//
//      r1/b <= r1/r2 
// <=> { if b > 0, then r2 > 0, and cross multiplication does not change the sign }
//     { if b < 0, then r2 < 0, and cross multiplication changes sign twice }
//      r1 * r2 <= b * r1 
// <=>
//      r1 * (b + d_2) <= r1 * b
// <=>
//      r1 * d_2 <= 0
// 
// if r1 * d_2 > 0, then r1/(b + sign_of(r1)*1/2*|b|) <= r1/r2
// 
// Not handled here:
// if b = 0, then d_2 != 0
//   if r1 * d_2 = 0 then it's 0.
//   if r1 * d_2 > 0, then result is +oo
//   if r1 * d_2 < 0, then result is -oo
// 
inf_rational inf_div(inf_rational const& r1, inf_rational const& r2) 
{
    SASSERT(!r2.m_first.is_zero());
    inf_rational result;

    if (r2.m_second.is_neg() && r1.is_neg()) {
        result = r1 / (r2.m_first - (abs(r2.m_first)/rational(2)));
    }
    else if (r2.m_second.is_pos() && r1.is_pos()) {
        result = r1 / (r2.m_first + (abs(r2.m_first)/rational(2)));
    }
    else {
        result = r1 / r2.m_first;
    }    
    return result;
}

inf_rational sup_div(inf_rational const& r1, inf_rational const& r2) 
{
    SASSERT(!r2.m_first.is_zero());
    inf_rational result;

    if (r2.m_second.is_pos() && r1.is_neg()) {
        result = r1 / (r2.m_first + (abs(r2.m_first)/rational(2)));
    }
    else if (r2.m_second.is_neg() && r1.is_pos()) {
        result = r1 / (r2.m_first - (abs(r2.m_first)/rational(2)));
    }
    else {
        result = r1 / r2.m_first;
    }    
    return result;

}

inf_rational inf_power(inf_rational const& r, unsigned n) 
{
    bool is_even = (0 == (n & 0x1));
    inf_rational result;
    if (n == 1) {
        result = r;
    }
    else if ((r.m_second.is_zero()) ||
        (r.m_first.is_pos() && r.m_second.is_pos()) ||
        (r.m_first.is_neg() && r.m_second.is_neg() && is_even)) {
        result.m_first = r.m_first.expt(n);
    }
    else if (is_even) {
        // 0 will work.
    }
    else if (r.m_first.is_zero()) {
        result.m_first = rational(-1);        
    }
    else if (r.m_first.is_pos()) {
        result.m_first = rational(r.m_first - r.m_first/rational(2)).expt(n);
    }
    else {
        result.m_first = rational(r.m_first + r.m_first/rational(2)).expt(n);
    }
    return result;
}

inf_rational sup_power(inf_rational const& r, unsigned n) 
{
    bool is_even = (0 == (n & 0x1));
    inf_rational result;
    if (n == 1) {
        result = r;
    }
    else if (r.m_second.is_zero() ||
        (r.m_first.is_pos() && r.m_second.is_neg()) ||
        (r.m_first.is_neg() && r.m_second.is_pos() && is_even)) {
        result.m_first = r.m_first.expt(n);
    }
    else if (r.m_first.is_zero() || (n == 0)) {
        result.m_first = rational(1);        
    }
    else if (r.m_first.is_pos() || is_even) {
        result.m_first = rational(r.m_first + r.m_first/rational(2)).expt(n);
    }
    else {
        // r (r.m_first) is negative, n is odd.
        result.m_first = rational(r.m_first - r.m_first/rational(2)).expt(n);
    }
    return result;
}

inf_rational inf_root(inf_rational const& r, unsigned n) 
{
    SASSERT(!r.is_neg());
    // use 0
    return inf_rational();
}

inf_rational sup_root(inf_rational const& r, unsigned n) 
{
    SASSERT(!r.is_neg());
    // use r.
    return r;
}
