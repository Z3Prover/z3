

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
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
