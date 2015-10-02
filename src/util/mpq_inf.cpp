/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpq_inf.cpp

Abstract:

    MPQ numbers with infinitesimals

Author:

    Leonardo de Moura (leonardo) 2011-06-28

Revision History:

--*/
#include"mpq_inf.h"

template<bool SYNCH>
std::string mpq_inf_manager<SYNCH>::to_string(mpq_inf const & a) {
    if (m.is_zero(a.second))
        return m.to_string(a.first);
    
    std::string s = "(";
    s += m.to_string(a.first);
    if (m.is_neg(a.second))
        s += " -e*";
    else
        s += " +e*";
    mpq tmp;
    m.set(tmp, a.second);
    m.abs(tmp);
    s += m.to_string(tmp);
    m.del(tmp);
    s += ")";
    return s;
}


template class mpq_inf_manager<true>;
template class mpq_inf_manager<false>;
