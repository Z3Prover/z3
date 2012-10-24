/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    watch_list.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-23.

Revision History:

--*/
#ifndef _WATCH_LIST_H_
#define _WATCH_LIST_H_

#include"smt_clause.h"
#include"memory_manager.h"

namespace smt {

    /**
       \brief List of clauses and literals watching a given literal.

       -------------------------------------------------------------------------------------------
       | end_nbegin | begin_lits | end |   regular clauses  | ->              <- | literals       |                              
       -------------------------------------------------------------------------------------------
       ^                    ^                    ^                ^ 
       |                    |                    |                |
       m_data              end_cls            begin_lits       end_lits
       
       When this class is used to implement unit propagation, a literal l1 in m_watch_list[l2] 
       represents the binary clause (or l1 (not l2))
    */
    class watch_list {
        char *    m_data;
        
        void expand();
        
        unsigned & end_cls_core() { 
            SASSERT(m_data);
            return reinterpret_cast<unsigned *>(m_data)[-3]; 
        }
        
        unsigned end_cls() {
            return m_data ? end_cls_core() : 0;
        }
        
        unsigned & begin_lits_core() { 
            SASSERT(m_data);
            return reinterpret_cast<unsigned *>(m_data)[-2]; 
        }

        unsigned begin_lits_core() const { 
            SASSERT(m_data);
            return reinterpret_cast<unsigned *>(m_data)[-2]; 
        }
        
        unsigned begin_lits() const { 
            return m_data ? begin_lits_core() : 0;
        }
        
        unsigned & end_lits_core() { 
            SASSERT(m_data);
            return reinterpret_cast<unsigned *>(m_data)[-1]; 
        }

        unsigned end_lits_core() const { 
            SASSERT(m_data);
            return reinterpret_cast<unsigned *>(m_data)[-1]; 
        }
        
        unsigned end_lits() const { 
            return m_data ? end_lits_core() : 0;
        }
        
        void destroy();
        
    public:
        watch_list():
            m_data(0) {
        }
        
        ~watch_list() {
            destroy();
        }
        
        unsigned size() const {
            if (m_data) {
                return 
                    reinterpret_cast<unsigned *>(m_data)[-3] + 
                    reinterpret_cast<unsigned *>(m_data)[-1] -
                    reinterpret_cast<unsigned *>(m_data)[-2];
            }
            return 0;
        }
        
        typedef clause ** clause_iterator;
        
        void reset() {
            if (m_data) {
                end_cls_core()   = 0;
                begin_lits_core() = end_lits_core();
            }
        }
        
        void reset_and_release_memory() {
            destroy();
            m_data = 0;
        }
        
        clause_iterator begin_clause() {
            return reinterpret_cast<clause **>(m_data);
        }
        
        clause_iterator end_clause() {
            return reinterpret_cast<clause **>(m_data + end_cls());
        }
        
        clause_iterator find_clause(clause const * c) {
            return std::find(begin_clause(), end_clause(), c);
        }
        
        literal * begin_literals() {
            return reinterpret_cast<literal *>(m_data + begin_lits());
        }
        
        literal * end_literals() {
            return reinterpret_cast<literal *>(m_data + end_lits());
        }

        literal const * begin_literals() const {
            return reinterpret_cast<literal const *>(m_data + begin_lits());
        }
        
        literal const * end_literals() const {
            return reinterpret_cast<literal const *>(m_data + end_lits());
        }
        
        literal * find_literal(literal const & l) {
            return std::find(begin_literals(), end_literals(), l);
        }

        literal const * find_literal(literal const & l) const {
            return std::find(begin_literals(), end_literals(), l);
        }
        
        void insert_clause(clause * c) {
            if (m_data == 0 || end_cls_core() + sizeof(clause *) >= begin_lits_core()) {
                expand();
            }
            *(reinterpret_cast<clause **>(m_data + end_cls_core()))  = c;
            end_cls_core() += sizeof(clause *);
        }
        
        void insert_literal(literal const & l) {
            if (m_data == 0 || begin_lits_core() <= end_cls_core() + sizeof(literal)) {
                expand();
            }
            SASSERT(begin_lits_core() >= sizeof(literal));
            begin_lits_core() -= sizeof(literal);
            *(reinterpret_cast<literal *>(m_data + begin_lits_core()))  = l;
        }
        
        void remove_clause(clause * c);
        
        void remove_literal(literal l);
        
        void set_end_clause(clause_iterator new_end) {
            SASSERT(new_end <= end_clause());
            if (m_data) {
                end_cls_core() = static_cast<unsigned>(reinterpret_cast<char *>(new_end) - m_data);
            }
        }
        
    };

};

#endif /* _WATCH_LIST_H_ */

