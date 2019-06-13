/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_prob.h

  Abstract:
   
    PROB Local search module for clauses

  Author:

  Nikolaj Bjorner 2019-4-23

  Notes:
  
     http://www.ict.griffith.edu.au/~johnt/publications/CP2006raouf.pdf

  --*/
#ifndef _SAT_PROB_
#define _SAT_PROB_

#include "util/uint_set.h"
#include "util/rlimit.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"

namespace sat {
    class solver;

    class prob : public i_local_search {

        struct clause_info {
            clause_info(): m_trues(0), m_num_trues(0) {}
            unsigned m_trues;        // set of literals that are true
            unsigned m_num_trues;    // size of true set
            bool is_true() const { return m_num_trues > 0; }
            void add(literal lit) { ++m_num_trues; m_trues += lit.index(); }
            void del(literal lit) { SASSERT(m_num_trues > 0); --m_num_trues; m_trues -= lit.index(); }
        };

        struct config {
            unsigned m_prob_random_init;
            unsigned m_restart_offset;
            double   m_cb;
            double   m_eps;
            config() { reset(); }
            void reset() {
                m_prob_random_init = 4;
                m_restart_offset = 1000000;
                m_cb = 2.85;
                m_eps = 0.9;
            }
        };
        
        config           m_config;
        reslimit         m_limit;
        clause_allocator m_alloc;
        clause_vector    m_clause_db;     
        svector<clause_info> m_clauses;
        svector<bool>    m_values, m_best_values;
        unsigned         m_best_min_unsat;
        vector<unsigned_vector> m_use_list;
        unsigned_vector  m_flat_use_list;
        unsigned_vector  m_use_list_index;
        svector<double>  m_prob_break;
        svector<double>  m_probs;
        indexed_uint_set m_unsat;
        random_gen       m_rand;
        unsigned_vector  m_breaks;
        uint64_t         m_flips;
        uint64_t         m_next_restart;
        unsigned         m_restart_count;
        stopwatch        m_stopwatch;
        model            m_model;

        class use_list {
            prob& p;
            unsigned i;
        public:
            use_list(prob& p, literal lit):
                p(p), i(lit.index()) {}
            unsigned const* begin() { return p.m_flat_use_list.c_ptr() + p.m_use_list_index[i]; }
            unsigned const* end() { return p.m_flat_use_list.c_ptr() + p.m_use_list_index[i+1]; }
        };

        void flatten_use_list(); 

        bool is_true(literal lit) const { return m_values[lit.var()] != lit.sign(); }

        inline clause const& get_clause(unsigned idx) const { return *m_clause_db[idx]; }

        inline bool is_true(unsigned idx) const { return m_clauses[idx].is_true(); }

        inline void inc_break(literal lit) { m_breaks[lit.var()]++; }

        inline void dec_break(literal lit) { m_breaks[lit.var()]--; }

        void flip();

        bool_var pick_var();

        void flip(bool_var v);

        void reinit_values();

        void save_best_values();

        void init();

        void init_random_values();

        void init_best_values();

        void init_near_best_values();

        void init_clauses();

        void auto_config();

        bool should_restart();

        void do_restart();

        void invariant();

        void log();

        void add(unsigned sz, literal const* c);

    public:
        prob() {}

        ~prob() override;

        lbool check(unsigned sz, literal const* assumptions, parallel* p) override;

        void set_seed(unsigned n) override { m_rand.set_seed(n); }

        reslimit& rlimit() override { return m_limit; }

        void add(solver const& s) override;

        model const& get_model() const override { return m_model; }
       
        std::ostream& display(std::ostream& out) const;

        void updt_params(params_ref const& p) override {}

        unsigned num_non_binary_clauses() const override { return 0; }

        void collect_statistics(statistics& st) const override {} 

        void reinit(solver& s) override { UNREACHABLE(); }

    };
}

#endif
