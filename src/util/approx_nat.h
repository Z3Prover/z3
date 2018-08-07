/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    approx_nat.h

Abstract:

    Approximated natural numbers. It performs operations on the set [0, ..., 2^{n-2}, huge].
    Where huge represents all numbers greater than 2^{n-2}. 

Author:

    Leonardo (leonardo) 2008-01-11

Notes:

--*/
#ifndef APPROX_NAT_H_
#define APPROX_NAT_H_

#include<iostream>
#include<climits>

class approx_nat {
    unsigned m_value;
    static const unsigned m_limit = UINT_MAX >> 2;
public:
    approx_nat():m_value(0) {}
    explicit approx_nat(unsigned val);
    bool is_huge() const { return m_value == UINT_MAX; }
    unsigned get_value() const { return m_value; }
    approx_nat & operator=(unsigned w);
    approx_nat & operator+=(unsigned w);
    approx_nat & operator+=(approx_nat const & w) { return operator+=(w.m_value); }
    approx_nat & operator*=(unsigned w);
    approx_nat & operator*=(approx_nat const & w) { return operator*=(w.m_value); }
    bool operator<(unsigned w) const { return !is_huge() && m_value < w; }
    bool operator<(approx_nat const & w) const { return !is_huge() && !w.is_huge() && m_value < w.m_value; }
};

std::ostream & operator<<(std::ostream & target, approx_nat const & w);

#endif /* APPROX_NAT_H_ */
