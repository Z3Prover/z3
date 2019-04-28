/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_ddfw.h

  Abstract:
   
    DDFW Local search module for clauses

  Author:

  Nikolaj Bjorner 2019-4-23

  Notes:
  
     http://www.ict.griffith.edu.au/~johnt/publications/CP2006raouf.pdf

  --*/
#ifndef _SAT_DDFW_
#define _SAT_DDFW_

#include "util/uint_set.h"
#include "util/heap.h"
#include "util/rlimit.h"
#include "sat/sat_clause.h"
#include "util/params.h"

namespace sat {
    class solver;

    class ddfw {
        struct lt {
            svector<int>& m_reward;
            lt(svector<int>& b): m_reward(b) {}
            bool operator()(bool_var v1, bool_var v2) const { return m_reward[v1] > m_reward[v2]; }
        };

        struct clause_info {
            clause_info(): m_weight(2), m_trues(0), m_num_trues(0) {}
            unsigned m_weight;       // weight of clause
            unsigned m_trues;        // set of literals that are true
            unsigned m_num_trues;    // size of true set
            bool is_true() const { return m_num_trues > 0; }
            void add(literal lit) { ++m_num_trues; m_trues += lit.index(); }
            void del(literal lit) { SASSERT(m_num_trues > 0); --m_num_trues; m_trues -= lit.index(); }
        };

        struct config {
            config() { reset(); }
            unsigned m_use_reward_zero_pct;
            unsigned m_init_clause_weight;
            bool     m_use_heap;
            unsigned m_max_num_models;
            unsigned m_restart_base;
            unsigned m_reinit_inc;
            void reset() {
                m_init_clause_weight = 8;
                m_use_reward_zero_pct = 15;
                m_use_heap = false;
                m_max_num_models = 64;
                m_restart_base = 100000;
                m_reinit_inc = 10000;
            }
        };
        
        config           m_config;
        reslimit         m_limit;
        clause_allocator m_alloc;
        clause_vector    m_clause_db;     
        svector<clause_info> m_clauses;
        svector<int>     m_reward; // per var break count
        svector<bool>    m_values;
        svector<int>     m_bias;
        heap<lt>         m_heap;
        vector<unsigned_vector> m_use_list;
        indexed_uint_set m_unsat;
        unsigned_vector  m_make_count;  // number of unsat clauses that become true if variable is flipped
        indexed_uint_set m_unsat_vars;  // set of variables that are in unsat clauses
        random_gen       m_rand;
        unsigned         m_reinit_next;
        unsigned         m_reinit_next_reset;
        unsigned         m_reinit_count;

        unsigned         m_restart_count, m_restart_next;
        uint64_t         m_flips, m_last_flips, m_shifts;
        unsigned         m_min_sz;
        u_map<svector<bool>> m_models;
        stopwatch        m_stopwatch;
        model            m_model;

        unsigned model_hash(svector<bool> const& m) const;

        bool is_true(literal lit) const { return m_values[lit.var()] != lit.sign(); }

        inline clause const& get_clause(unsigned idx) const { return *m_clause_db[idx]; }

        inline unsigned get_weight(unsigned idx) const { return m_clauses[idx].m_weight; }

        inline bool is_true(unsigned idx) const { return m_clauses[idx].is_true(); }

        unsigned select_max_same_sign(unsigned cf_idx);

        void inc_make(literal lit) { 
            bool_var v = lit.var(); 
            if (m_make_count[v]++ == 0) m_unsat_vars.insert(v); 
        }

        void dec_make(literal lit) { 
            bool_var v = lit.var(); 
            if (--m_make_count[v] == 0) m_unsat_vars.remove(v); 
        }

        void inc_reward(literal lit, int inc);

        void dec_reward(literal lit, int inc);

        // flip activity
        bool do_flip();
        bool_var pick_var();       
        void flip(bool_var v);
        void save_best_values();

        // shift activity
        void shift_weights();

        // reinitialize weights activity
        bool should_reinit_weights();        
        void do_reinit_weights();
        bool select_clause(unsigned max_weight, unsigned max_trues, unsigned weight, unsigned num_trues);

        // restart activity
        bool should_restart();
        void do_restart();
        void reinit_values();

        void log();

        void init();

        void init_clause_data();

        void invariant();

        void add(unsigned sz, literal const* c);

    public:

        ddfw(): m_heap(10, m_reward) {}

        ~ddfw();

        lbool check();

        void updt_params(params_ref const& p);

        model const& get_model() const { return m_model; }

        reslimit& rlimit() { return m_limit; }

        void set_seed(unsigned n) { m_rand.set_seed(n); }

        void add(solver const& s);
       
        std::ostream& display(std::ostream& out) const;
    };
}

#endif
