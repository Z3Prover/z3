/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_clause_pos_set.h

Abstract:

    A set of pairs (clause, index).

Author:

    Leonardo de Moura (leonardo) 2008-02-16.

Revision History:

--*/
#ifndef _SPC_CLAUSE_POS_SET_H_
#define _SPC_CLAUSE_POS_SET_H_

#include"hashtable.h"

namespace spc {

    typedef std::pair<clause *, unsigned> clause_pos_pair;

    class clause_pos_entry {
        clause_pos_pair m_data;
    public:
        typedef clause_pos_pair data;
        clause_pos_entry() { m_data.first = 0; }
        unsigned get_hash() const { return m_data.first->get_id(); }
        bool is_free() const { return m_data.first == 0; }
        bool is_deleted() const { return m_data.first == reinterpret_cast<clause *>(1); }
        bool is_used() const { 
            return m_data.first != reinterpret_cast<clause *>(0) && m_data.first != reinterpret_cast<clause *>(1);
        }
        clause_pos_pair const & get_data() const { return m_data; }
        clause_pos_pair & get_data() { return m_data; }
        void set_data(clause_pos_pair const & d) { 
            SASSERT(d.first != 0 && d.first != reinterpret_cast<clause*>(1));
            m_data = d; 
        }
        void set_hash(unsigned h) { SASSERT(m_data.first->get_id() == h); }
        void mark_as_deleted() { m_data.first = reinterpret_cast<clause *>(1); }
        void mark_as_free() { m_data.first = 0; }
    };
    
    struct clause_pos_pair_hash {
        unsigned operator()(clause_pos_pair const & p) const { return p.first->get_id(); }
    };

    typedef core_hashtable<clause_pos_entry, clause_pos_pair_hash, default_eq<clause_pos_pair> > clause_pos_set;
};

#endif /* _SPC_CLAUSE_POS_SET_H_ */

