/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_clause_selection.h

Abstract:

    Superposition Calculus Clause Selection

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#ifndef _SPC_CLAUSE_SELECTION_H_
#define _SPC_CLAUSE_SELECTION_H_

#include"spc_clause.h"
#include"heap.h"

namespace spc {
    
    /**
       \brief Abstract functor for evaluating how 'good' a clause is.
       Smaller values mean better clauses.
    */
    struct clause_eval {
        virtual ~clause_eval() {}
        virtual unsigned operator()(clause * c) const = 0;
    };

    /**
       \brief Clause selection heuristic. It supports different priority queues.
    */
    class clause_selection {
        class lt {
            id2clause &   m_id2clause;
            clause_eval & m_func;
        public:
            lt(id2clause & m, clause_eval & f):
                m_id2clause(m), m_func(f) {}
            bool operator()(int cidx1, int cidx2) const {
                return m_func(m_id2clause(cidx1)) < m_func(m_id2clause(cidx2));
            }
        };

        id2clause                m_id2clause;
        ptr_vector<heap<lt> >    m_heaps;
        unsigned_vector          m_slot_size;
        unsigned                 m_curr_slot;
        unsigned                 m_counter;
        ptr_vector<clause_eval>  m_fs;
        void reserve(unsigned cid);
    public:
        clause_selection(unsigned num_heaps, clause_eval * const * fs, unsigned * slots);
        ~clause_selection();
        void insert(clause * c);
        void erase(clause * c);
        bool empty() const;
        void reset();
        clause * get_best();
    };

    struct symbol_count_clause_eval : public clause_eval {
        virtual ~symbol_count_clause_eval() {}
        virtual unsigned operator()(clause * c) const { return c->get_symbol_count(); }
    };
     
    struct time_clause_eval : public clause_eval {
        virtual ~time_clause_eval() {}
        virtual unsigned operator()(clause * c) const { return c->get_time(); }
    };
    
    struct proof_depth_clause_eval : public clause_eval {
        virtual ~proof_depth_clause_eval() {}
        virtual unsigned operator()(clause * c) const { return c->get_proof_depth(); }
    };
};

#endif /* _SPC_CLAUSE_SELECTION_H_ */

