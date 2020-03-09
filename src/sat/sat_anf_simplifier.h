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
#pragma once

#include "util/params.h"
#include "util/statistics.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"
#include "sat/sat_solver.h"

namespace dd {
    class pdd;
    class solver;
};

namespace sat {

    typedef dd::solver pdd_solver;

    class anf_simplifier {
    public:
        struct config {
            unsigned m_max_clause_size;
            unsigned m_max_clauses;
            bool     m_compile_xor;
            bool     m_compile_aig;
            bool     m_anf2phase;
            bool     m_enable_exlin;
            config():
                m_max_clause_size(3),
                m_max_clauses(10000),
                m_compile_xor(true),
                m_compile_aig(true),
                m_anf2phase(false),
                m_enable_exlin(false)
            {}
        };

    private:
        struct report;

        struct stats {
            unsigned m_num_units, m_num_eqs;
            unsigned m_num_aigs, m_num_xors, m_num_ifs;
            unsigned m_num_phase_flips;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        solver&        s;
        config         m_config;
        svector<bool>  m_relevant;
        stats          m_stats;
        statistics     m_st;
        unsigned_vector m_eval_cache;
        unsigned        m_eval_ts;
        svector<bool>   m_used_for_evaluation;

        void clauses2anf(pdd_solver& solver);
        void anf2clauses(pdd_solver& solver);
        void anf2phase(pdd_solver& solver);

        void collect_clauses(clause_vector & clauses, svector<solver::bin_clause>& bins);

        void compile_xors(clause_vector& clauses, pdd_solver& ps);
        void compile_aigs(clause_vector& clauses, svector<solver::bin_clause>& bins, pdd_solver& ps);

        void collect_xors(vector<literal_vector>& xors);
        void configure_solver(pdd_solver& ps);
        void add_clause(clause const& c, pdd_solver& ps);
        void add_bin(solver::bin_clause const& b, pdd_solver& ps);
        void add_xor(literal_vector const& x, pdd_solver& ps);
        void add_if(literal head, literal c, literal t, literal e, pdd_solver& ps);
        void add_aig(literal head, literal_vector const& ands, pdd_solver& ps);        
        void save_statistics(pdd_solver& ps);

        bool eval(dd::pdd const& p);
        void reset_eval();

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
        anf_simplifier(solver& s) : s(s), m_eval_ts(0) {}
        ~anf_simplifier() {}
        
        void operator()();
        void set(config const& cfg) { m_config = cfg; }
        void collect_statistics(statistics& st) const { st.copy(m_st); }
    };
}
