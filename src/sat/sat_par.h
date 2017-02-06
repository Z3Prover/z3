/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_par.h

Abstract:

    Utilities for parallel SAT solving.

Author:

    Nikolaj Bjorner (nbjorner) 2017-1-29.

Revision History:

--*/
#ifndef SAT_PAR_H_
#define SAT_PAR_H_

#include"sat_types.h"
#include"hashtable.h"
#include"map.h"

namespace sat {

    class par {

        // shared pool of learned clauses.
        class vector_pool {
            unsigned_vector m_vectors;
            unsigned        m_size;
            unsigned        m_tail;
            unsigned_vector m_heads;
            void next(unsigned& index);
            unsigned get_owner(unsigned index) const { return m_vectors[index]; }
            unsigned get_length(unsigned index) const { return m_vectors[index+1]; }
            unsigned const* get_ptr(unsigned index) const { return m_vectors.c_ptr() + index + 2; }
        public:
            vector_pool() {}
            void reserve(unsigned num_owners, unsigned sz);
            void begin_add_vector(unsigned owner, unsigned n);
            void add_vector_elem(unsigned e);
            bool get_vector(unsigned owner, unsigned& n, unsigned const*& ptr);
        };

        bool enable_add(clause const& c) const;
        void _get_clauses(solver& s);

        typedef hashtable<unsigned, u_hash, u_eq> index_set;
        literal_vector m_units;
        index_set      m_unit_set;
        literal_vector m_lits;
        vector_pool    m_pool;
    public:

        par();

        // reserve space
        void reserve(unsigned num_owners, unsigned sz) { m_pool.reserve(num_owners, sz); }

        // exchange unit literals
        void exchange(solver& s, literal_vector const& in, unsigned& limit, literal_vector& out);

        // add clause to shared clause pool
        void share_clause(solver& s, clause const& c);

        void share_clause(solver& s, literal l1, literal l2);
        
        // receive clauses from shared clause pool
        void get_clauses(solver& s);
    };

};

#endif
