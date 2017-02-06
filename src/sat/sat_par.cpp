/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_par.cpp

Abstract:

    Utilities for parallel SAT solving.

Author:

    Nikolaj Bjorner (nbjorner) 2017-1-29.

Revision History:

--*/
#include "sat_par.h"
#include "sat_clause.h"
#include "sat_solver.h"


namespace sat {

    void par::vector_pool::next(unsigned& index) {
        SASSERT(index < m_size);
        unsigned n = index + 2 + get_length(index);
        if (n >= m_size) {
            index = 0;
        }
        else {
            index = n;
        }
    }

    void par::vector_pool::reserve(unsigned num_threads, unsigned sz) {
        m_vectors.reset();
        m_vectors.resize(sz, 0);
        m_heads.reset();
        m_heads.resize(num_threads, 0);
        m_tail = 0;
        m_size = sz;
    }
    
    void par::vector_pool::begin_add_vector(unsigned owner, unsigned n) {
        unsigned capacity = n + 2;
        m_vectors.reserve(m_size + capacity, 0);
        IF_VERBOSE(3, verbose_stream() << owner << ": begin-add " << n << " tail: " << m_tail << " size: " << m_size << "\n";);
        if (m_tail >= m_size) {
            // move tail to the front.
            for (unsigned i = 0; i < m_heads.size(); ++i) {
                while (m_heads[i] < capacity) {
                    next(m_heads[i]);
                }
                IF_VERBOSE(3, verbose_stream() << owner << ": head: " << m_heads[i] << "\n";);
            }
            m_tail = 0;            
        }
        else {
            for (unsigned i = 0; i < m_heads.size(); ++i) {
                while (m_tail < m_heads[i] && m_heads[i] < m_tail + capacity) {
                    next(m_heads[i]);
                }
                IF_VERBOSE(3, verbose_stream() << owner << ": head: " << m_heads[i] << "\n";);
            }
        }
        m_vectors[m_tail++] = owner;
        m_vectors[m_tail++] = n;    
    }

    void par::vector_pool::add_vector_elem(unsigned e) {
        m_vectors[m_tail++] = e;
    }

    bool par::vector_pool::get_vector(unsigned owner, unsigned& n, unsigned const*& ptr) {
        unsigned head = m_heads[owner];      
        SASSERT(head < m_size);
        while (head != m_tail) {
            IF_VERBOSE(3, verbose_stream() << owner << ": head: " << head << " tail: " << m_tail << "\n";);
            bool is_self = owner == get_owner(head);
            next(m_heads[owner]);
            if (!is_self) {
                n = get_length(head);
                ptr = get_ptr(head);
                return true;
            }
            head = m_heads[owner];
        }
        return false;
    }

    par::par() {}

    void par::exchange(solver& s, literal_vector const& in, unsigned& limit, literal_vector& out) {
        if (s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        #pragma omp critical (par_solver)
        {
            if (limit < m_units.size()) {
                // this might repeat some literals.
                out.append(m_units.size() - limit, m_units.c_ptr() + limit);
            }
            for (unsigned i = 0; i < in.size(); ++i) {
                literal lit = in[i];
                if (!m_unit_set.contains(lit.index())) {
                    m_unit_set.insert(lit.index());
                    m_units.push_back(lit);
                }
            }
            limit = m_units.size();
        }
    }

    void par::share_clause(solver& s, literal l1, literal l2) {        
        if (s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        #pragma omp critical (par_solver)
        {
            IF_VERBOSE(3, verbose_stream() << s.m_par_id << ": share " <<  l1 << " " << l2 << "\n";);
            m_pool.begin_add_vector(s.m_par_id, 2);
            m_pool.add_vector_elem(l1.index());
            m_pool.add_vector_elem(l2.index());            
        }        
    }

    void par::share_clause(solver& s, clause const& c) {        
        if (s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        unsigned n = c.size();
        unsigned owner = s.m_par_id;
        #pragma omp critical (par_solver)
        {
            if (enable_add(c)) {
                IF_VERBOSE(3, verbose_stream() << owner << ": share " <<  c << "\n";);
                m_pool.begin_add_vector(owner, n);                
                for (unsigned i = 0; i < n; ++i) {
                    m_pool.add_vector_elem(c[i].index());
                }
            }
        }
    }

    void par::get_clauses(solver& s) {
        if (s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        #pragma omp critical (par_solver)
        {
            _get_clauses(s);
        }
    }

    void par::_get_clauses(solver& s) {
        unsigned n;
        unsigned const* ptr;
        unsigned owner = s.m_par_id;
        while (m_pool.get_vector(owner, n, ptr)) {
            m_lits.reset();
            for (unsigned i = 0; i < n; ++i) {
                m_lits.push_back(to_literal(ptr[i]));
            }
            IF_VERBOSE(3, verbose_stream() << s.m_par_id << ": retrieve " << m_lits << "\n";);
            SASSERT(n >= 2);
            s.mk_clause_core(m_lits.size(), m_lits.c_ptr(), true);
        }        
    }

    bool par::enable_add(clause const& c) const {
        // plingeling, glucose heuristic:
        return (c.size() <= 40 && c.glue() <= 8) || c.glue() <= 2;
    }

};

