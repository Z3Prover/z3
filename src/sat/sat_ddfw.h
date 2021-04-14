/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_ddfw.h

  Abstract:
   
    DDFW Local search module for clauses

  Author:

  Nikolaj Bjorner, Marijn Heule 2019-4-23

  Notes:
  
     http://www.ict.griffith.edu.au/~johnt/publications/CP2006raouf.pdf

  --*/
#pragma once

#include "util/uint_set.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "util/ema.h"
#include "sat/sat_clause.h"
#include "sat/sat_types.h"

namespace sat {
    class solver;
    class parallel;

    class ddfw : public i_local_search {

        struct clause_info {
            clause_info(clause* cl, unsigned init_weight): m_weight(init_weight), m_trues(0), m_num_trues(0), m_clause(cl) {}
            unsigned m_weight;       // weight of clause
            unsigned m_trues;        // set of literals that are true
            unsigned m_num_trues;    // size of true set
            clause*  m_clause;
            bool is_true() const { return m_num_trues > 0; }
            void add(literal lit) { ++m_num_trues; m_trues += lit.index(); }
            void del(literal lit) { SASSERT(m_num_trues > 0); --m_num_trues; m_trues -= lit.index(); }
        };

        struct config {
            config() { reset(); }
            unsigned m_use_reward_zero_pct;
            unsigned m_init_clause_weight;
            unsigned m_max_num_models;
            unsigned m_restart_base;
            unsigned m_reinit_base;
            unsigned m_parsync_base;
            double   m_itau;
            void reset() {
                m_init_clause_weight = 8;
                m_use_reward_zero_pct = 15;
                m_max_num_models = (1 << 10);
                m_restart_base = 100333;
                m_reinit_base = 10000;
                m_parsync_base = 333333;
                m_itau = 0.5;
            }
        };

        struct var_info {
            var_info(): m_value(false), m_reward(0), m_make_count(0), m_bias(0), m_reward_avg(1e-5) {}
            bool     m_value;
            int      m_reward;
            unsigned m_make_count;
            int      m_bias;
            ema      m_reward_avg;
        };
        
        config           m_config;
        reslimit         m_limit;
        clause_allocator m_alloc;
        svector<clause_info> m_clauses;
        literal_vector       m_assumptions;        
        svector<var_info>    m_vars;        // var -> info
        svector<double>      m_probs;       // var -> probability of flipping
        svector<double>      m_scores;      // reward -> score
        model                m_model;       // var -> best assignment
        
        vector<unsigned_vector> m_use_list;
        unsigned_vector  m_flat_use_list;
        unsigned_vector  m_use_list_index;

        indexed_uint_set m_unsat;
        indexed_uint_set m_unsat_vars;  // set of variables that are in unsat clauses
        random_gen       m_rand;
        unsigned         m_num_non_binary_clauses{ 0 };
        unsigned         m_restart_count{ 0 }, m_reinit_count{ 0 }, m_parsync_count{ 0 };
        uint64_t         m_restart_next{ 0 }, m_reinit_next{ 0 }, m_parsync_next{ 0 };
        uint64_t         m_flips{ 0 }, m_last_flips{ 0 }, m_shifts{ 0 };
        unsigned         m_min_sz{ 0 };
        hashtable<unsigned, unsigned_hash, default_eq<unsigned>> m_models;
        stopwatch        m_stopwatch;

        parallel*        m_par;

        class use_list {
            ddfw& p;
            unsigned i;
        public:
            use_list(ddfw& p, literal lit):
                p(p), i(lit.index()) {}
            unsigned const* begin() { return p.m_flat_use_list.data() + p.m_use_list_index[i]; }
            unsigned const* end() { return p.m_flat_use_list.data() + p.m_use_list_index[i + 1]; }
        };

        void flatten_use_list(); 

        double mk_score(unsigned r);

        inline double score(unsigned r) { return r; } // TBD: { for (unsigned sz = m_scores.size(); sz <= r; ++sz) m_scores.push_back(mk_score(sz)); return m_scores[r]; }

        inline unsigned num_vars() const { return m_vars.size(); }

        inline unsigned& make_count(bool_var v) { return m_vars[v].m_make_count; }

        inline bool& value(bool_var v) { return m_vars[v].m_value; }

        inline bool value(bool_var v) const { return m_vars[v].m_value; }

        inline int& reward(bool_var v) { return m_vars[v].m_reward; }

        inline int reward(bool_var v) const { return m_vars[v].m_reward; }

        inline int& bias(bool_var v) { return m_vars[v].m_bias; }

        unsigned value_hash() const;

        inline bool is_true(literal lit) const { return value(lit.var()) != lit.sign(); }

        inline clause const& get_clause(unsigned idx) const { return *m_clauses[idx].m_clause; }

        inline unsigned get_weight(unsigned idx) const { return m_clauses[idx].m_weight; }

        inline bool is_true(unsigned idx) const { return m_clauses[idx].is_true(); }

        void update_reward_avg(bool_var v) { m_vars[v].m_reward_avg.update(reward(v)); }

        unsigned select_max_same_sign(unsigned cf_idx);

        inline void inc_make(literal lit) { 
            bool_var v = lit.var(); 
            if (make_count(v)++ == 0) m_unsat_vars.insert(v); 
        }

        inline void dec_make(literal lit) { 
            bool_var v = lit.var(); 
            if (--make_count(v) == 0) m_unsat_vars.remove(v); 
        }

        inline void inc_reward(literal lit, int inc) { reward(lit.var()) += inc; }

        inline void dec_reward(literal lit, int inc) { reward(lit.var()) -= inc; }

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
        inline bool select_clause(unsigned max_weight, unsigned max_trues, clause_info const& cn, unsigned& n);

        // restart activity
        bool should_restart();
        void do_restart();
        void reinit_values();

        // parallel integration
        bool should_parallel_sync();
        void do_parallel_sync();

        void log();

        void init(unsigned sz, literal const* assumptions);

        void init_clause_data();

        void invariant();

        void add(unsigned sz, literal const* c);

        void add_assumptions();

    public:

        ddfw(): m_par(nullptr) {}

        ~ddfw() override;

        lbool check(unsigned sz, literal const* assumptions, parallel* p) override;

        void updt_params(params_ref const& p) override;

        model const& get_model() const override { return m_model; }

        reslimit& rlimit() override { return m_limit; }

        void set_seed(unsigned n) override { m_rand.set_seed(n); }

        void add(solver const& s) override;
       
        std::ostream& display(std::ostream& out) const;

        // for parallel integration
        unsigned num_non_binary_clauses() const override { return m_num_non_binary_clauses; }
        void reinit(solver& s) override;

        void collect_statistics(statistics& st) const override {} 

        double get_priority(bool_var v) const override { return m_probs[v]; }
    };
}

