/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_anf_simplifier.h

  Abstract:
   
    Simplification based on ANF format.

  Author:

    Nikolaj Bjorner 2020-01-02

  Notes:
  

  --*/
#pragma once;

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"

namespace sat {

    class pdd_solver;

    class anf_simplifier {
    public:
        struct config {
            unsigned m_max_clause_size;
            unsigned m_max_clauses;
            config():
                m_max_clause_size(10),
                m_max_clauses(10000)
            {}
        };
    private:
        solver& s;
        config  m_config;
        svector<bool> m_relevant;

        void collect_clauses(clause_vector & clauses, svector<solver::bin_clause>& bins);
        void collect_xors(vector<literal_vector>& xors);
        void configure_solver(pdd_solver& ps);
        void add_clause(clause const& c, pdd_solver& ps);
        void add_bin(solver::bin_clause const& b, pdd_solver& ps);
        void add_xor(literal_vector const& x, pdd_solver& ps);

        bool is_pre_satisfied(clause const& c);
        bool is_pre_satisfied(solver::bin_clause const& b);
        bool is_too_large(clause const& c) { return c.size() > m_config.m_max_clause_size; }
        bool has_relevant_var(clause const& c);
        bool has_relevant_var(solver::bin_clause const& b);
        bool is_relevant(literal l) { return is_relevant(l.var()); }
        bool is_relevant(bool_var v) { return m_relevant[v]; }
        bool phase_is_true(literal l);

        void set_relevant(solver::bin_clause const& b);
        void set_relevant(clause const& c);
        void set_relevant(literal l) { set_relevant(l.var()); }
        void set_relevant(bool_var v) { m_relevant[v] = true; }

    public:
        anf_simplifier(solver& s) : s(s) {}
        ~anf_simplifier() {}
        
        void operator()();
        void set(config const& cfg) { m_config = cfg; }
    };
}
