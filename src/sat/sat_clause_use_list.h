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
#ifndef SAT_CLAUSE_USE_LIST_H_
#define SAT_CLAUSE_USE_LIST_H_

#include "sat/sat_types.h"
#include "util/trace.h"

namespace sat {

    /**
       \brief Clause use list with delayed deletion.
    */
    class clause_use_list {
        clause_vector   m_clauses;
        unsigned        m_size;
        unsigned        m_num_redundant;
    public:
        clause_use_list() {
            STRACE("clause_use_list_bug", tout << "[cul_created] " << this << "\n";);
            m_size = 0; 
            m_num_redundant = 0;
        }
        
        unsigned size() const { 
            return m_size; 
        }

        unsigned num_redundant() const {
            return m_num_redundant;
        }
        
        unsigned num_irredundant() const {
            return m_size - m_num_redundant;
        }

        bool empty() const { return size() == 0; }
        
        void insert(clause & c) { 
            STRACE("clause_use_list_bug", tout << "[cul_insert] " << this << " " << &c << "\n";);
            SASSERT(!m_clauses.contains(&c)); 
            SASSERT(!c.was_removed()); 
            m_clauses.push_back(&c); 
            m_size++; 
            if (c.is_learned()) ++m_num_redundant;
        }

        void erase_not_removed(clause & c) { 
            STRACE("clause_use_list_bug", tout << "[cul_erase_not_removed] " << this << " " << &c << "\n";);
            SASSERT(m_clauses.contains(&c)); 
            SASSERT(!c.was_removed()); 
            m_clauses.erase(&c); 
            m_size--; 
            if (c.is_learned()) --m_num_redundant;
        }

        void erase(clause & c) { 
            STRACE("clause_use_list_bug", tout << "[cul_erase] " << this << " " << &c << "\n";);
            SASSERT(m_clauses.contains(&c)); 
            SASSERT(c.was_removed()); 
            m_size--; 
            if (c.is_learned()) --m_num_redundant;
        }

        void block(clause const& c) {
            SASSERT(c.is_learned());
            ++m_num_redundant;
            SASSERT(check_invariant());
        }

        void unblock(clause const& c) {
            SASSERT(!c.is_learned());
            --m_num_redundant;
            SASSERT(check_invariant());
        }
        
        void reset() { 
            m_clauses.finalize(); 
            m_size = 0; 
            m_num_redundant = 0;
        }
        
        bool check_invariant() const;

        // iterate & compress
        class iterator {            
            clause_vector & m_clauses;
            unsigned        m_size;
            unsigned        m_i;
            unsigned        m_j;
            void consume();

        public:
            iterator(clause_vector & v):m_clauses(v), m_size(v.size()), m_i(0) {
                m_j = 0;
                consume(); 
            }
            ~iterator();
            bool at_end() const { return m_i == m_size; }
            clause & curr() const { SASSERT(!at_end()); return *(m_clauses[m_i]); }
            void next() { 
                SASSERT(!at_end()); 
                SASSERT(!m_clauses[m_i]->was_removed()); 
                m_i++; 
                m_j++; 
                consume(); 
            }
        };
        
        iterator mk_iterator() const { return iterator(const_cast<clause_use_list*>(this)->m_clauses); }

        std::ostream& display(std::ostream& out) const {
            iterator it = mk_iterator();
            while (!it.at_end()) {
                out << it.curr() << "\n";
                it.next();
            }
            return out;
        }
    };

};

#endif
