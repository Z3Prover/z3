/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_clause_set.cpp

Abstract:

    Set of clauses

Author:

    Leonardo de Moura (leonardo) 2011-05-25.

Revision History:

--*/
#include "sat/sat_clause_set.h"

namespace sat {

    void clause_set::insert(clause & c) {
        unsigned id  = c.id();
        m_id2pos.reserve(id+1, UINT_MAX);
        if (m_id2pos[id] != UINT_MAX)
            return; // already in the set
        unsigned pos = m_set.size();
        m_id2pos[id] = pos;
        m_set.push_back(&c);
        CASSERT("clause_set", check_invariant());
    }

    void clause_set::erase(clause & c) { 
        unsigned id = c.id();
        if (id >= m_id2pos.size())
            return;
        if (empty()) 
            return;
        unsigned pos = m_id2pos[id];
        if (pos == UINT_MAX)
            return;
        m_id2pos[id] = UINT_MAX;
        unsigned last_pos = m_set.size() - 1;
        if (pos != last_pos) {
            clause * last_c = m_set[last_pos];
            m_set[pos] = last_c; 
            m_id2pos[last_c->id()] = pos;
        }
        m_set.pop_back();
        CASSERT("clause_set", check_invariant());
    }

    clause & clause_set::erase() {
        SASSERT(!empty());
        clause & c = *m_set.back(); 
        SASSERT(c.id() < m_id2pos.size());
        SASSERT(m_id2pos[c.id()] == m_set.size()-1);
        if (c.id() < m_id2pos.size()) {
            m_id2pos[c.id()] = UINT_MAX;
        }
        m_set.pop_back();
        return c;
    }

    bool clause_set::check_invariant() const {
        DEBUG_CODE(
        {
            clause_vector::const_iterator it  = m_set.begin();
            clause_vector::const_iterator end = m_set.end();
            for (unsigned pos = 0; it != end; ++it, ++pos) {
                clause & c = *(*it);
                SASSERT(c.id() < m_id2pos.size());
                SASSERT(m_id2pos[c.id()] == pos);
            }
        }
        {
            unsigned_vector::const_iterator it  = m_id2pos.begin();
            unsigned_vector::const_iterator end = m_id2pos.end();
            for (unsigned id = 0; it != end; ++it, ++id) {
                unsigned pos = *it;
                if (pos == UINT_MAX)
                    continue;
                SASSERT(pos < m_set.size());
                SASSERT(m_set[pos]->id() == id);
            }
        });
        return true;
    }

};
