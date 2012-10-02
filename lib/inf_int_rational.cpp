/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    inf_int_rational.cpp

Abstract:

    Rational numbers with infenitesimals

Author:

    Nikolaj Bjorner (nbjorner) 2006-12-05.

Revision History:

--*/
#include<sstream>
#include"inf_int_rational.h"

inf_int_rational inf_int_rational::m_zero(0);
inf_int_rational inf_int_rational::m_one(1);
inf_int_rational inf_int_rational::m_minus_one(-1);

std::string inf_int_rational::to_string() const {
    if (m_second == 0) {
        return m_first.to_string();
    }
    std::ostringstream s;
    
    s << "(" << m_first.to_string();
    if (m_second < 0) {
        s << " -e*" << (-m_second) << ")";
    }
    else {
        s << " +e*" << m_second << ")";
    }
    return s.str();
}

