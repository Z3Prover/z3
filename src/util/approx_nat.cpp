/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    approx_nat.cpp

Abstract:

    Approximated natural numbers. It performs operations on the set [0, ..., 2^{n-2}, huge].
    Where huge represents all numbers greater than 2^{n-2}. 

Author:

    Leonardo (leonardo) 2008-01-11

Notes:

--*/
#include "util/approx_nat.h"

approx_nat::approx_nat(unsigned val) {
    m_value = val > m_limit ? UINT_MAX : val;
}

approx_nat & approx_nat::operator=(unsigned val) {
    m_value = val > m_limit ? UINT_MAX : val;
    return *this;
}

approx_nat & approx_nat::operator+=(unsigned w) {
    if (is_huge()) 
        return *this;
    if (w > m_limit) {
        m_value = UINT_MAX;
        return *this;
    }
    m_value += w;
    if (m_value > m_limit)
        m_value = UINT_MAX;
    return *this;
}

approx_nat & approx_nat::operator*=(unsigned w) {
    if (is_huge()) 
        return *this;
    unsigned long long r = static_cast<unsigned long long>(m_value) * static_cast<unsigned long long>(w);
    if (r > m_limit)
        m_value = UINT_MAX;
    else
        m_value = static_cast<unsigned>(r);
    return *this;
}

std::ostream & operator<<(std::ostream & target, approx_nat const & w) {
    if (w.is_huge()) 
        target << "[huge]";
    else
        target << w.get_value();
    return target;
}
