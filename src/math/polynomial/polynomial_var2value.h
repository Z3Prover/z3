/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    polynomial_var2value.h

Abstract:

    Simple implementations of the var2value interface.

Author:

    Leonardo (leonardo) 2012-01-05

Notes:

--*/
#ifndef POLYNOMIAL_VAR2VALUE_H_
#define POLYNOMIAL_VAR2VALUE_H_

#include"polynomial.h"
#include"scoped_numeral_vector.h"

namespace polynomial {

    // default implementation used for debugging purposes
    template<typename ValManager>
    class simple_var2value : public var2value<ValManager, typename ValManager::numeral> {
        var_vector                         m_xs;
        _scoped_numeral_vector<ValManager> m_vs;
    public:
        simple_var2value(ValManager & m):m_vs(m) {}
        void push_back(var x, typename ValManager::numeral const & v) { m_xs.push_back(x); m_vs.push_back(v); }
        virtual ValManager & m() const { return m_vs.m(); }
        virtual bool contains(var x) const { return std::find(m_xs.begin(), m_xs.end(), x) != m_xs.end(); }
        virtual typename ValManager::numeral const & operator()(var x) const {
            for (unsigned i = 0; i < m_xs.size(); i++)
                if (m_xs[i] == x)
                    return m_vs[i];
            UNREACHABLE();
            static typename ValManager::numeral zero;
            return zero;
        }
    };
    
};


#endif
