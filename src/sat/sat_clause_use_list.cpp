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
#include "sat/sat_clause.h"
#include "sat/sat_clause_use_list.h"

namespace sat {

    bool clause_use_list::check_invariant() const {
        unsigned sz = 0;
        for (clause* c : m_clauses) 
            if (!c->was_removed())
                sz++;
        SASSERT(sz == m_size);
        unsigned redundant = 0;
        for (clause* c : m_clauses) 
            if (c->is_learned())
                redundant++;
        SASSERT(redundant == m_num_redundant);

        return true;
    }

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

    clause_use_list::iterator::~iterator() {
        while (m_i < m_size)
            next();
        m_clauses.shrink(m_j);
    }

};
