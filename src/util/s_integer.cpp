/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    s_integer.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-10.

Revision History:

--*/

#include"s_integer.h"

s_integer s_integer::m_zero(0);
s_integer s_integer::m_one(1);
s_integer s_integer::m_minus_one(-1);

s_integer::s_integer(const char * str) {
    m_val = static_cast<int>(strtol(str, 0, 10));
}

s_integer power(const s_integer & r, unsigned p) {
    unsigned mask = 1;
    s_integer result = s_integer(1);
    s_integer power = r;
    while (mask <= p) {
        if (mask & p) {
            result *= power;
        }
        power *= power;
        mask = mask << 1;
    }
    return result;
}

s_integer gcd(const s_integer & r1, const s_integer & r2) {
    SASSERT(r1.is_int() && r2.is_int());
    s_integer tmp1(r1);
    s_integer tmp2(r2);
    if (tmp1.is_neg()) {
        tmp1.neg();
    }
    if (tmp2.is_neg()) {
        tmp2.neg();
    }
    if (tmp1 < tmp2) {
        tmp1.swap(tmp2);
    }
    for(;;) {
        s_integer aux = tmp1 % tmp2;
        if (aux.is_zero()) {
            return tmp2;
        }
        tmp1 = tmp2;
        tmp2 = aux;
    }
}

s_integer lcm(const s_integer & r1, const s_integer & r2) {
    s_integer g = gcd(r1, r2);
    return (r1 / g) * r2;
}
