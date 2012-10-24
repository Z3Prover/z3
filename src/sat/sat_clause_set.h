/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_clause_set.h

Abstract:

    Set of clauses

Author:

    Leonardo de Moura (leonardo) 2011-05-25.

Revision History:

--*/
#ifndef _SAT_CLAUSE_SET_H_
#define _SAT_CLAUSE_SET_H_

#include"sat_clause.h"

namespace sat {

    class clause_set {
        unsigned_vector m_id2pos; 
        clause_vector   m_set;
    public:
        typedef clause_vector::const_iterator iterator;

        bool contains(clause const & cls) const { 
            if (cls.id() >= m_id2pos.size()) 
                return false; 
            return m_id2pos[cls.id()] != UINT_MAX; 
        }
        bool empty() const { return m_set.empty(); }
        unsigned size() const { return m_set.size(); }
        void insert(clause & c);
        void erase(clause & c);

        // erase some clause from the set
        clause & erase();

        void reset() { m_id2pos.reset(); m_set.reset(); }
        void finalize() { m_id2pos.finalize(); m_set.finalize(); }

        iterator begin() const { return m_set.begin(); }
        iterator end() const { return m_set.end(); }

        bool check_invariant() const;
    };
    
};

#endif
