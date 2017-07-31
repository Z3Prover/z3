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
#include "util/inf_int_rational.h"

inf_int_rational inf_int_rational::m_zero;
inf_int_rational inf_int_rational::m_one;
inf_int_rational inf_int_rational::m_minus_one;

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

void initialize_inf_int_rational() {
  inf_int_rational::init();
}

void inf_int_rational::init() {
  m_zero.m_first = rational::zero();
  m_one.m_first = rational::one();
  m_minus_one.m_first = rational::minus_one();
}

void finalize_inf_int_rational() {
  inf_int_rational::finalize();
}

void inf_int_rational::finalize() {
  m_zero.~inf_int_rational();
  m_one.~inf_int_rational();
  m_minus_one.~inf_int_rational();
}
