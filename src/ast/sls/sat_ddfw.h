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
#include "util/sat_sls.h"
#include "util/map.h"
#include "util/sat_literal.h"
#include "util/statistics.h"
#include "util/stopwatch.h"


namespace sat {

    class local_search_plugin {
    public:
        virtual ~local_search_plugin() {}
        virtual void init_search() = 0;
        virtual void finish_search() = 0;
        virtual double reward(bool_var v) = 0;
        virtual void on_rescale() = 0;
        virtual void on_save_model() = 0;
        virtual void on_restart() = 0;
    };
    
    class ddfw {
        friend class ddfw_wrapper;
    protected:

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
            var_info() {}
            bool     m_internal = false;
            bool     m_value = false;
            double   m_reward = 0;
            double   m_last_reward = 0;
            unsigned m_make_count = 0;
            int      m_bias = 0;
            bool     m_external = false;
            ema      m_reward_avg = 1e-5;
        };
        
        config               m_config;
        reslimit             m_limit;
        vector<clause_info>  m_clauses;
        literal_vector       m_assumptions;        
        svector<var_info>    m_vars;        // var -> info
        svector<double>      m_probs;       // var -> probability of flipping
        svector<double>      m_scores;      // reward -> score
        svector<lbool>       m_model;       // var -> best assignment
        unsigned             m_init_weight = 2; 
        
        vector<unsigned_vector> m_use_list;
        unsigned_vector  m_flat_use_list;
        unsigned_vector  m_use_list_index;

        indexed_uint_set m_unsat;
        indexed_uint_set m_unsat_vars;  // set of variables that are in unsat clauses
        random_gen       m_rand;
        unsigned         m_num_non_binary_clauses = 0;
        unsigned         m_restart_count = 0, m_reinit_count = 0;
        uint64_t         m_restart_next = 0, m_reinit_next = 0;
        uint64_t         m_flips = 0, m_last_flips = 0, m_shifts = 0;
        unsigned         m_min_sz = 0, m_steps_since_progress = 0;
        u_map<unsigned>  m_models;
        stopwatch        m_stopwatch;

        scoped_ptr<local_search_plugin> m_plugin = nullptr;
        std::function<bool(void)> m_parallel_sync;

        void flatten_use_list(); 

        /**
         * TBD: map reward value to a score, possibly through an exponential function, such as
         * exp(-tau/r), where tau > 0
         */
        inline double score(double r) { return r; } 

        inline unsigned& make_count(bool_var v) { return m_vars[v].m_make_count; }

        inline bool& value(bool_var v) { return m_vars[v].m_value; }

        inline bool value(bool_var v) const { return m_vars[v].m_value; }

        inline double& reward(bool_var v) { return m_vars[v].m_reward; }        

        inline double plugin_reward(bool_var v) { return is_external(v) ? (m_vars[v].m_last_reward = m_plugin->reward(v)) : reward(v); }

        void set_external(bool_var v) { m_vars[v].m_external = true; }

        inline bool is_external(bool_var v) const { return m_vars[v].m_external; }

        inline int& bias(bool_var v) { return m_vars[v].m_bias; }

        unsigned value_hash() const;

        inline bool is_true(literal lit) const { return value(lit.var()) != lit.sign(); }

        inline sat::literal_vector const& get_clause(unsigned idx) const { return m_clauses[idx].m_clause; }

        inline double get_weight(unsigned idx) const { return m_clauses[idx].m_weight; }

        inline bool is_true(unsigned idx) const { return m_clauses[idx].is_true(); }

        void update_reward_avg(bool_var v) { m_vars[v].m_reward_avg.update(reward(v)); }

        unsigned select_max_same_sign(unsigned cf_idx);

        inline void inc_make(literal lit) { 
            bool_var v = lit.var(); 
            if (make_count(v)++ == 0) m_unsat_vars.insert_fresh(v); 
        }

        inline void dec_make(literal lit) { 
            bool_var v = lit.var(); 
            if (--make_count(v) == 0) m_unsat_vars.remove(v); 
        }

        inline void inc_reward(literal lit, double w) { reward(lit.var()) += w; }

        inline void dec_reward(literal lit, double w) { reward(lit.var()) -= w; }

        void check_with_plugin();
        void check_without_plugin();

        // flip activity
        template<bool uses_plugin>
        bool do_flip();

        template<bool uses_plugin>
        bool_var pick_var(double& reward);     

        template<bool uses_plugin>
        bool apply_flip(bool_var v, double reward);


        void save_best_values();
        void save_model();
        void save_priorities();

        // shift activity
        void shift_weights();
        inline double calculate_transfer_weight(double w);

        // reinitialize weights activity
        bool should_reinit_weights();        
        void do_reinit_weights();
        inline bool select_clause(double max_weight, clause_info const& cn, unsigned& n);

        // restart activity
        bool should_restart();
        void do_restart();
        void reinit_values();

        unsigned select_random_true_clause();        

        void log();

        void init(unsigned sz, literal const* assumptions);

        void init_clause_data();

        void invariant();

        void del();

        void add_assumptions();

        inline void transfer_weight(unsigned from, unsigned to, double w);

        inline bool disregard_neighbor();

    public:

        ddfw() {}

        ~ddfw();

        void set_plugin(local_search_plugin* p) { m_plugin = p; }

        lbool check(unsigned sz, literal const* assumptions);

        void updt_params(params_ref const& p);

        svector<lbool> const& get_model() const { return m_model; }

        reslimit& rlimit() { return m_limit; }

        void set_seed(unsigned n) { m_rand.set_seed(n); }


        bool get_value(bool_var v) const { return value(v); }
       
        std::ostream& display(std::ostream& out) const;

        // for parallel integration
        unsigned num_non_binary_clauses() const { return m_num_non_binary_clauses; }

        void collect_statistics(statistics& st) const {} 

        double get_priority(bool_var v) const { return m_probs[v]; }

        // access clause information and state of Boolean search
        indexed_uint_set& unsat_set() { return m_unsat; }

        indexed_uint_set const& unsat_set() const { return m_unsat; }

        vector<clause_info> const& clauses() const { return m_clauses; }

        clause_info& get_clause_info(unsigned idx) { return m_clauses[idx]; }

        clause_info const& get_clause_info(unsigned idx) const { return m_clauses[idx]; }

        void remove_assumptions();

        void flip(bool_var v);

        inline double get_reward(bool_var v) const { return m_vars[v].m_reward; }

        void add(unsigned sz, literal const* c);

        sat::bool_var add_var(bool is_internal = true);

        // is this a variable that was added during initialization?
        bool is_initial_var(sat::bool_var v) const {
            return m_vars.size() > v && !m_vars[v].m_internal;
        }

        void reinit();

        inline unsigned num_vars() const { return m_vars.size(); }


        ptr_iterator<unsigned> use_list(literal lit) { 
            unsigned i = lit.index();
            auto const* b = m_flat_use_list.data() + m_use_list_index[i];
            auto const* e = m_flat_use_list.data() + m_use_list_index[i + 1];
            return { b, e };            
        }

    };
}

