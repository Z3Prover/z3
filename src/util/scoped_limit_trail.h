
#include "util/vector.h"

#pragma once

class scoped_limit_trail {
    unsigned_vector m_lim;
    unsigned m_scopes{ 0 };
    unsigned m_last{ 0 };
 public:
    
    void push(unsigned n) { 
        if (m_last == n)
            m_scopes++; 
        else {
            for (; m_scopes > 0; --m_scopes)
                m_lim.push_back(m_last);
            m_lim.push_back(n);
            m_last = n;
        }
    }
    unsigned pop(unsigned n) {
        SASSERT(n > 0);
        SASSERT(m_scopes + m_lim.size() >= n);
        if (n <= m_scopes) {
            m_scopes -= n;
            return m_last;
        }
        else {
            n -= m_scopes;
            m_scopes = 0;
            m_last = m_lim[m_lim.size() - n];
            m_lim.shrink(m_lim.size() - n);
            return m_last;
        }
    }
};
