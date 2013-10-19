/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_clause_use_list.h

Abstract:

    Clause use list

Author:

    Leonardo de Moura (leonardo) 2011-05-31.

Revision History:

--*/
#ifndef _SAT_CLAUSE_USE_LIST_H_
#define _SAT_CLAUSE_USE_LIST_H_

#include"sat_types.h"
#include"trace.h"

namespace sat {

#define LAZY_USE_LIST

    /**
       \brief Clause use list with delayed deletion.
    */
    class clause_use_list {
        clause_vector   m_clauses;
#ifdef LAZY_USE_LIST
        unsigned        m_size;
#endif
    public:
        clause_use_list() {
            STRACE("clause_use_list_bug", tout << "[cul_created] " << this << "\n";);
#ifdef LAZY_USE_LIST
            m_size = 0; 
#endif
        }
        
        unsigned size() const { 
#ifdef LAZY_USE_LIST
            return m_size; 
#else
            return m_clauses.size();
#endif
        }

        bool empty() const { return size() == 0; }
        
        void insert(clause & c) { 
            STRACE("clause_use_list_bug", tout << "[cul_insert] " << this << " " << &c << "\n";);
            SASSERT(!m_clauses.contains(&c)); 
            SASSERT(!c.was_removed()); 
            m_clauses.push_back(&c); 
#ifdef LAZY_USE_LIST
            m_size++; 
#endif
        }

        void erase_not_removed(clause & c) { 
            STRACE("clause_use_list_bug", tout << "[cul_erase_not_removed] " << this << " " << &c << "\n";);
#ifdef LAZY_USE_LIST
            SASSERT(m_clauses.contains(&c)); 
            SASSERT(!c.was_removed()); 
            m_clauses.erase(&c); 
            m_size--; 
#else
            m_clauses.erase(&c);
#endif
        }

        void erase(clause & c) { 
            STRACE("clause_use_list_bug", tout << "[cul_erase] " << this << " " << &c << "\n";);
#ifdef LAZY_USE_LIST
            SASSERT(m_clauses.contains(&c)); 
            SASSERT(c.was_removed()); 
            m_size--; 
#else
            m_clauses.erase(&c);
#endif
        }
        
        void reset() { 
            m_clauses.finalize(); 
#ifdef LAZY_USE_LIST
            m_size = 0; 
#endif
        }
        
        bool check_invariant() const;

        // iterate & compress
        class iterator {
            clause_vector & m_clauses;
            unsigned        m_size;
            unsigned        m_i;
#ifdef LAZY_USE_LIST
            unsigned        m_j;
            void consume();
#endif
        public:
            iterator(clause_vector & v):m_clauses(v), m_size(v.size()), m_i(0) {
#ifdef LAZY_USE_LIST
                m_j = 0;
                consume(); 
#endif
            }
            ~iterator();
            bool at_end() const { return m_i == m_size; }
            clause & curr() const { SASSERT(!at_end()); return *(m_clauses[m_i]); }
            void next() { 
                SASSERT(!at_end()); 
                SASSERT(!m_clauses[m_i]->was_removed()); 
                m_i++; 
#ifdef LAZY_USE_LIST
                m_j++; 
                consume(); 
#endif
            }
        };
        
        iterator mk_iterator() const { return iterator(const_cast<clause_use_list*>(this)->m_clauses); }
    };

};

#endif
