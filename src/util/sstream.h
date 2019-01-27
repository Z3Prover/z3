/*
Copyright (c) 2018 Microsoft Corporation

Module Name:

    nat_set.h

Abstract:

    Wrapper for sstream.

Author:

    Leonardo de Moura (leonardo) 2013

Revision History:

*/
#pragma once
#include <sstream>
#include <string>

namespace lean {
/** \brief Wrapper for std::ostringstream */
class sstream {
    std::ostringstream m_strm;
public:
    std::string str() const { return m_strm.str(); }
    template<typename T> sstream & operator<<(T const & t) { m_strm << t; return *this; }
};
}
