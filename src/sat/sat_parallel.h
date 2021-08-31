/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_parallel.h

Abstract:

    Utilities for parallel SAT solving.

Author:

    Nikolaj Bjorner (nbjorner) 2017-1-29.

Revision History:

--*/
#pragma once

#include "sat/sat_types.h"
#include "util/hashtable.h"
#include "util/map.h"
#include "util/rlimit.h"
#include "util/scoped_ptr_vector.h"
#include "util/mutex.h"

namespace sat {

    class parallel {

        // shared pool of learned clauses.
        class vector_pool {
            unsigned_vector m_vectors;
            unsigned        m_size{ 0 };
            unsigned        m_tail{ 0 };
            unsigned_vector m_heads;
            bool_vector   m_at_end;
            void next(unsigned& index);
            unsigned get_owner(unsigned index) const { return m_vectors[index]; }
            unsigned get_length(unsigned index) const { return m_vectors[index+1]; }
            unsigned const* get_ptr(unsigned index) const { return m_vectors.data() + index + 2; }
        public:
            void reserve(unsigned num_owners, unsigned sz);
            void begin_add_vector(unsigned owner, unsigned n);
            void end_add_vector();
            void add_vector_elem(unsigned e);
            bool get_vector(unsigned owner, unsigned& n, unsigned const*& ptr);
        };

        bool enable_add(clause const& c) const;
        void _get_clauses(solver& s);
        void _from_solver(solver& s);
        bool _to_solver(solver& s);
        bool _from_solver(i_local_search& s);
        void _to_solver(i_local_search& s);

        typedef hashtable<unsigned, u_hash, u_eq> index_set;
        literal_vector m_units;
        index_set      m_unit_set;
        literal_vector m_lits;
        vector_pool    m_pool;
        mutex          m_mux;

        // for exchange with local search:
        unsigned           m_num_clauses;
        scoped_ptr<solver> m_solver_copy;
        bool               m_consumer_ready;
        svector<double>    m_priorities;

        scoped_limits      m_scoped_rlimit;
        vector<reslimit>   m_limits;
        ptr_vector<solver> m_solvers;
        
    public:

        parallel(solver& s);

        ~parallel();

        void init_solvers(solver& s, unsigned num_extra_solvers);

        void push_child(reslimit& rl);

        // reserve space
        void reserve(unsigned num_owners, unsigned sz) { m_pool.reserve(num_owners, sz); }

        solver& get_solver(unsigned i) { return *m_solvers[i]; }

        void cancel_solver(unsigned i) { m_limits[i].cancel(); }

        // exchange unit literals
        void exchange(solver& s, literal_vector const& in, unsigned& limit, literal_vector& out);

        // add clause to shared clause pool
        void share_clause(solver& s, clause const& c);

        void share_clause(solver& s, literal l1, literal l2);
        
        // receive clauses from shared clause pool
        void get_clauses(solver& s);

        // exchange from solver state to local search and back.
        void from_solver(solver& s);
        bool to_solver(solver& s);
        
        bool from_solver(i_local_search& s);
        void to_solver(i_local_search& s);
        
        bool copy_solver(solver& s);
    };

};

