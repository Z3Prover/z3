/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_parallel.cpp

Abstract:

    Utilities for parallel SAT solving.

Author:

    Nikolaj Bjorner (nbjorner) 2017-1-29.

Revision History:

--*/
#include "sat/sat_parallel.h"
#include "sat/sat_clause.h"
#include "sat/sat_solver.h"

namespace sat {

    void parallel::vector_pool::next(unsigned& index) {
        SASSERT(index < m_size);
        unsigned n = index + 2 + get_length(index);
        index = (n >= m_size) ? 0 : n;
    }

    void parallel::vector_pool::reserve(unsigned num_threads, unsigned sz) {
        m_vectors.reset();
        m_vectors.resize(sz, 0);
        m_heads.reset();
        m_heads.resize(num_threads, 0);
        m_at_end.reset();
        m_at_end.resize(num_threads, true);
        m_tail = 0;
        m_size = sz;
    }
    
    void parallel::vector_pool::begin_add_vector(unsigned owner, unsigned n) {
        SASSERT(m_tail < m_size);
        unsigned capacity = n + 2;
        m_vectors.reserve(m_size + capacity, 0);
        IF_VERBOSE(3, verbose_stream() << owner << ": begin-add " << n << " tail: " << m_tail << " size: " << m_size << "\n";);
        for (unsigned i = 0; i < m_heads.size(); ++i) {
            while (m_tail < m_heads[i] && m_heads[i] < m_tail + capacity) {
                next(m_heads[i]);
            }
            m_at_end[i] = false;
        }
        m_vectors[m_tail++] = owner;
        m_vectors[m_tail++] = n;    
    }

    void parallel::vector_pool::add_vector_elem(unsigned e) {
        m_vectors[m_tail++] = e;
    }

    void parallel::vector_pool::end_add_vector() {
        if (m_tail >= m_size) 
            m_tail = 0;
    }


    bool parallel::vector_pool::get_vector(unsigned owner, unsigned& n, unsigned const*& ptr) {
        unsigned head = m_heads[owner];      
        unsigned iterations = 0;
        while (head != m_tail || !m_at_end[owner]) {
            ++iterations;
            SASSERT(head < m_size && m_tail < m_size);            
            bool is_self = owner == get_owner(head);
            next(m_heads[owner]);
            IF_VERBOSE(static_cast<unsigned>(iterations > m_size ? 0 : 3), verbose_stream() << owner << ": [" << head << ":" << m_heads[owner] << "] tail: " << m_tail << "\n";);
            m_at_end[owner] = (m_heads[owner] == m_tail);
            if (!is_self) {
                n = get_length(head);
                ptr = get_ptr(head);
                return true;
            }
            head = m_heads[owner];
        }
        return false;
    }

    parallel::parallel(solver& s): m_num_clauses(0), m_consumer_ready(false), m_scoped_rlimit(s.rlimit()) {}

    parallel::~parallel() {
        reset();
    }

    void parallel::reset() {
        m_limits.reset();
        m_scoped_rlimit.reset();
        for (auto* s : m_solvers)
            dealloc(s);
        m_solvers.reset();
    }

    void parallel::init_solvers(solver& s, unsigned num_extra_solvers) {
        unsigned num_threads = num_extra_solvers + 1;
        m_solvers.init(num_extra_solvers);
        m_limits.init(num_extra_solvers);
        symbol saved_phase = s.m_params.get_sym("phase", symbol("caching"));
        
        for (unsigned i = 0; i < num_extra_solvers; ++i) {
            s.m_params.set_uint("random_seed", s.m_rand());
            if (i == 1 + num_threads/2) 
                s.m_params.set_sym("phase", symbol("random"));
            m_solvers[i] = alloc(sat::solver, s.m_params, m_limits[i]);
            m_solvers[i]->copy(s, true);
            m_solvers[i]->set_par(this, i);
            push_child(m_solvers[i]->rlimit());            
        }
        s.set_par(this, num_extra_solvers);
        s.m_params.set_sym("phase", saved_phase);        
    }

    void parallel::push_child(reslimit& rl) {
        m_scoped_rlimit.push_child(&rl);            
    }


    void parallel::exchange(solver& s, literal_vector const& in, unsigned& limit, literal_vector& out) {
        if (s.get_config().m_num_threads == 1 || s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        {
            lock_guard lock(m_mux);
            if (limit < m_units.size()) {
                // this might repeat some literals.
                out.append(m_units.size() - limit, m_units.data() + limit);
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

    void parallel::share_clause(solver& s, literal l1, literal l2) {        
        if (s.get_config().m_num_threads == 1 || s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        IF_VERBOSE(3, verbose_stream() << s.m_par_id << ": share " <<  l1 << " " << l2 << "\n";);
        {
            lock_guard lock(m_mux);
            m_pool.begin_add_vector(s.m_par_id, 2);
            m_pool.add_vector_elem(l1.index());
            m_pool.add_vector_elem(l2.index());            
            m_pool.end_add_vector();
        }        
    }

    void parallel::share_clause(solver& s, clause const& c) {        
        if (s.get_config().m_num_threads == 1 || !enable_add(c) || s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        unsigned n = c.size();
        unsigned owner = s.m_par_id;
        IF_VERBOSE(3, verbose_stream() << owner << ": share " <<  c << "\n";);
        lock_guard lock(m_mux);
        m_pool.begin_add_vector(owner, n);                
        for (unsigned i = 0; i < n; ++i) 
            m_pool.add_vector_elem(c[i].index());
        m_pool.end_add_vector();        
    }

    void parallel::get_clauses(solver& s) {
        if (s.m_par_syncing_clauses) return;
        flet<bool> _disable_sync_clause(s.m_par_syncing_clauses, true);
        lock_guard lock(m_mux);
        _get_clauses(s);        
    }

    void parallel::_get_clauses(solver& s) {
        unsigned n;
        unsigned const* ptr;
        unsigned owner = s.m_par_id;
        while (m_pool.get_vector(owner, n, ptr)) {
            m_lits.reset();
            bool usable_clause = true;
            for (unsigned i = 0; usable_clause && i < n; ++i) {
                literal lit(to_literal(ptr[i]));                
                m_lits.push_back(lit);
                usable_clause = lit.var() <= s.m_par_num_vars && !s.was_eliminated(lit.var());
            }
            IF_VERBOSE(3, verbose_stream() << s.m_par_id << ": retrieve " << m_lits << "\n";);
            SASSERT(n >= 2);
            if (usable_clause) {
                s.mk_clause_core(m_lits.size(), m_lits.data(), sat::status::redundant());
            }
        }        
    }

    bool parallel::enable_add(clause const& c) const {
        // plingeling, glucose heuristic:
        return (c.size() <= 40 && c.glue() <= 8) || c.glue() <= 2;
    }

    void parallel::_from_solver(solver& s) {
        if (m_consumer_ready && (m_num_clauses == 0 || (m_num_clauses > s.m_clauses.size()))) {
            // time to update local search with new clauses.
            // there could be multiple local search engines running at the same time.
            IF_VERBOSE(1, verbose_stream() << "(sat-parallel refresh :from " << m_num_clauses << " :to " << s.m_clauses.size() << ")\n";);
            m_solver_copy = alloc(solver, s.m_params, s.rlimit());
            m_solver_copy->copy(s, true);
            m_num_clauses = s.m_clauses.size();
        }
    }


    void parallel::_to_solver(solver& s) {
        return;
#if 0
        if (m_priorities.empty())
            return;
        
        for (bool_var v = 0; v < m_priorities.size(); ++v) 
            s.update_activity(v, m_priorities[v]);
        s.m_activity_inc = 128;
#endif
    }

    void parallel::from_solver(solver& s) {
        lock_guard lock(m_mux);
        _from_solver(s);        
    }

    void parallel::to_solver(solver& s) {
        lock_guard lock(m_mux);
        _to_solver(s);
    }

    void parallel::_to_solver(i_local_search& s) {        
        return;
#if 0
        m_priorities.reset();
        for (bool_var v = 0; m_solver_copy && v < m_solver_copy->num_vars(); ++v) {
            m_priorities.push_back(s.get_priority(v));
        }
#endif
    }

    bool parallel::_from_solver(i_local_search& s) {
        bool copied = false;
        m_consumer_ready = true;
        if (m_solver_copy) {
            copied = true;
            s.reinit(*m_solver_copy.get(), m_solver_copy->m_best_phase);
        }
        return copied;
    }

    bool parallel::from_solver(i_local_search& s) {
        lock_guard lock(m_mux);
        return _from_solver(s);
    }

    void parallel::to_solver(i_local_search& s) {
        lock_guard lock(m_mux);
        _to_solver(s);               
    }

    bool parallel::copy_solver(solver& s) {
        bool copied = false;
        lock_guard lock(m_mux);
        m_consumer_ready = true;
        if (m_solver_copy && s.m_clauses.size() > m_solver_copy->m_clauses.size()) {
            s.copy(*m_solver_copy, true);
            copied = true;
            m_num_clauses = s.m_clauses.size();
        }
        return copied;
    }
    
};

