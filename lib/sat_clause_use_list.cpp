/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_clause_use_list.cpp

Abstract:

    Clause use list

Author:

    Leonardo de Moura (leonardo) 2011-05-31.

Revision History:

--*/
#include"sat_clause.h"
#include"sat_clause_use_list.h"

namespace sat {

    bool clause_use_list::check_invariant() const {
#ifdef LAZY_USE_LIST
        unsigned sz = 0;
        for (unsigned i = 0; i < m_clauses.size(); i++) 
            if (!m_clauses[i]->was_removed())
                sz++;
        SASSERT(sz == m_size);
#endif
        return true;
    }

#ifdef LAZY_USE_LIST
    void clause_use_list::iterator::consume() {
        while (true) {
            if (m_i == m_size)
                return;
            if (!m_clauses[m_i]->was_removed()) {
                m_clauses[m_j] = m_clauses[m_i];
                return;
            }
            m_i++;
        }
    }
#endif

    clause_use_list::iterator::~iterator() {
#ifdef LAZY_USE_LIST
        while (m_i < m_size)
            next();
        m_clauses.shrink(m_j);
#endif
    }

};
