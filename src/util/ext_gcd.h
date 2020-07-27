/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ext_gcd.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-09.

Revision History:

--*/
#pragma once

template<typename numeral>
void extended_gcd(const numeral & in_a, const numeral & in_b, numeral & gcd, numeral & x, numeral & y) {
    numeral a = in_a;
    numeral b = in_b;
    x = numeral(0);
    y = numeral(1);
    numeral lastx(1);
    numeral lasty(0);
    numeral tmp;
    numeral quotient;
    while (!b.is_zero()) {
        tmp       = b;
        quotient  = div(a, b);
        b         = mod(a, b);
        a         = tmp;
        
        tmp       = x;
        x         = lastx - (quotient * x);
        lastx     = tmp;

        tmp       = y;
        y         = lasty - (quotient * y);
        lasty     = tmp;
    }
    gcd = a;
    x   = lastx;
    y   = lasty;
}


