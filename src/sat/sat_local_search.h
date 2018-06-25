/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  sat_local_search.h

  Abstract:
   
  Local search module for cardinality clauses.

  Author:

  Sixue Liu 2017-2-21

  Notes:

  --*/
#ifndef _SAT_LOCAL_SEARCH_H_
#define _SAT_LOCAL_SEARCH_H_

#include "util/vector.h"
#include "sat/sat_types.h"
#include "sat/sat_config.h"
#include "util/rlimit.h"

namespace sat {

    class parallel;

    class local_search_config {
        unsigned          m_random_seed;
        int               m_best_known_value;
        local_search_mode m_mode;
        bool              m_phase_sticky;
    public:
        local_search_config() {
            m_random_seed = 0;
            m_best_known_value = INT_MAX;
            m_mode = local_search_mode::wsat;
            m_phase_sticky = false;
        }

        unsigned random_seed() const { return m_random_seed; }
        unsigned best_known_value() const { return m_best_known_value;  }
        local_search_mode mode() const { return m_mode; }
        bool phase_sticky() const { return m_phase_sticky; }
        
        void set_random_seed(unsigned s) { m_random_seed = s;  }
        void set_best_known_value(unsigned v) { m_best_known_value = v; }

        void set_config(config const& cfg) {
            m_mode         = cfg.m_local_search_mode;
            m_random_seed  = cfg.m_random_seed;
            m_phase_sticky = cfg.m_phase_sticky;
        }
    };


    class local_search {
		
        struct pbcoeff {
            unsigned m_constraint_id;
            unsigned m_coeff;
            pbcoeff(unsigned id, unsigned coeff):
                m_constraint_id(id), m_coeff(coeff) {}
        };
        typedef svector<bool> bool_vector;
        typedef svector<pbcoeff> coeff_vector;

        // data structure for a term in objective function
        struct ob_term {
            bool_var var_id;                     // variable id, begin with 1
            int coefficient;                     // non-zero integer
            ob_term(bool_var v, int c): var_id(v), coefficient(c) {}
        };
        
        struct var_info {
            bool m_value;                        // current solution
            unsigned m_bias;                     // bias for current solution in percentage.
                                                 // if bias is 0, then value is always false, if 100, then always true
            bool m_unit;                         // is this a unit literal
            bool m_conf_change;                  // whether its configure changes since its last flip
            bool m_in_goodvar_stack;
            int  m_score;
            int  m_slack_score;
            int  m_time_stamp;                   // the flip time stamp                 
            int  m_cscc;                         // how many times its constraint state configure changes since its last flip
            bool_var_vector m_neighbors;         // neighborhood variables
            coeff_vector m_watch[2];
            literal_vector m_bin[2];
            var_info():
                m_value(true),
                m_bias(50), 
                m_unit(false),
                m_conf_change(true),
                m_in_goodvar_stack(false),
                m_score(0),
                m_slack_score(0),
                m_cscc(0)
            {}
        };

        struct constraint {
            unsigned        m_id;
            unsigned        m_k;
            int             m_slack;
            unsigned        m_size;
            literal_vector  m_literals;
            constraint(unsigned k, unsigned id) : m_id(id), m_k(k), m_slack(0), m_size(0) {}
            void push(literal l) { m_literals.push_back(l); ++m_size; }
            unsigned size() const { return m_size; }
            literal const& operator[](unsigned idx) const { return m_literals[idx]; }
            literal const* begin() const { return m_literals.begin(); }
            literal const* end() const { return m_literals.end(); }
        };

        local_search_config m_config;

        // objective function: maximize
        svector<ob_term>   ob_constraint;        // the objective function *constraint*, sorted in decending order
                        
        // information about the variable
        int_vector             coefficient_in_ob_constraint; // var! initialized to be 0
        

        vector<var_info>       m_vars;
        svector<bool_var>      m_units;

        inline int score(bool_var v) const { return m_vars[v].m_score; }
        inline void inc_score(bool_var v) { m_vars[v].m_score++; }
        inline void dec_score(bool_var v) { m_vars[v].m_score--; }

        inline int slack_score(bool_var v) const { return m_vars[v].m_slack_score; }
        inline void inc_slack_score(bool_var v) { m_vars[v].m_slack_score++; }
        inline void dec_slack_score(bool_var v) { m_vars[v].m_slack_score--; }
        
        inline bool already_in_goodvar_stack(bool_var v) const { return m_vars[v].m_in_goodvar_stack; }
        inline bool conf_change(bool_var v) const { return m_vars[v].m_conf_change; }
        inline int  time_stamp(bool_var v) const { return m_vars[v].m_time_stamp; }
        inline int  cscc(bool_var v) const { return m_vars[v].m_cscc; }
        inline void inc_cscc(bool_var v) { m_vars[v].m_cscc++; }

        inline bool cur_solution(bool_var v) const { return m_vars[v].m_value; }
        
        inline void set_best_unsat();
        /* TBD: other scores */
        

        vector<constraint> m_constraints;

        literal_vector m_assumptions;
        literal_vector m_prop_queue;

        unsigned m_num_non_binary_clauses;
        bool     m_is_pb; 

        inline bool is_pos(literal t) const { return !t.sign(); }
        inline bool is_true(bool_var v) const { return cur_solution(v); }
        inline bool is_true(literal l) const { return cur_solution(l.var()) != l.sign(); }
        inline bool is_false(literal l) const { return cur_solution(l.var()) == l.sign(); }
        inline bool is_unit(bool_var v) const { return m_vars[v].m_unit; }
        inline bool is_unit(literal l) const { return m_vars[l.var()].m_unit; }

        unsigned num_constraints() const { return m_constraints.size(); } // constraint index from 1 to num_constraint


        unsigned constraint_slack(unsigned ci) const { return m_constraints[ci].m_slack; }
        
        // unsat constraint stack
        bool            m_is_unsat;
        unsigned_vector m_unsat_stack;               // store all the unsat constraits
        unsigned_vector m_index_in_unsat_stack;      // which position is a contraint in the unsat_stack
        
        // configuration changed decreasing variables (score>0 and conf_change==true)
        bool_var_vector m_goodvar_stack;


        // information about solution
        unsigned         m_best_unsat;
        double           m_best_unsat_rate;
        double           m_last_best_unsat_rate;
        int              m_objective_value;                 // the objective function value corresponds to the current solution
        bool_vector      m_best_solution;                   // !var: the best solution so far
        int              m_best_objective_value = -1;       // the objective value corresponds to the best solution so far
                                                            // for non-known instance, set as maximal
        int              m_best_known_value = INT_MAX;      // best known value for this instance
        
        unsigned         m_max_steps = (1 << 30);
        
        // dynamic noise
        double m_noise = 9800; // normalized by 10000
        double m_noise_delta = 0.05;

        reslimit    m_limit;
        random_gen  m_rand;
        parallel*   m_par;
        model       m_model;

        void init();
        void reinit();
        void reinit_orig();
        void init_cur_solution();
        void init_slack();
        void init_scores();
        void init_goodvars();
        
        bool_var pick_var_gsat();

        void flip_gsat(bool_var v);

        void pick_flip_walksat();

        void flip_walksat(bool_var v);

        bool propagate(literal lit);

        void add_propagation(literal lit);

        void walksat();

        void gsat();

        void unsat(unsigned c);

        void sat(unsigned c);

        bool tie_breaker_sat(bool_var v1, bool_var v2);

        bool tie_breaker_ccd(bool_var v1, bool_var v2);

        void set_parameters();

        void calculate_and_update_ob();

        bool all_objectives_are_met() const;

        void verify_solution() const;

        void verify_unsat_stack() const;

        void verify_constraint(constraint const& c) const;

        unsigned constraint_value(constraint const& c) const;

        unsigned constraint_coeff(constraint const& c, literal l) const;

        void print_info(std::ostream& out);

        void extract_model();

        bool check_goodvar();

        void add_clause(unsigned sz, literal const* c);

        void add_unit(literal lit);

        std::ostream& display(std::ostream& out) const;

        std::ostream& display(std::ostream& out, constraint const& c) const;

        std::ostream& display(std::ostream& out, unsigned v, var_info const& vi) const;

    public:

        local_search();

        reslimit& rlimit() { return m_limit; }

        ~local_search();

        void add_soft(bool_var v, int weight);

        void add_cardinality(unsigned sz, literal const* c, unsigned k);

        void add_pb(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k);
        
        lbool check();

        lbool check(unsigned sz, literal const* assumptions, parallel* p = 0);

        local_search_config& config() { return m_config;  }

        unsigned num_vars() const { return m_vars.size() - 1; }     // var index from 1 to num_vars

        unsigned num_non_binary_clauses() const { return m_num_non_binary_clauses; }

        void import(solver& s, bool init);        

        void set_phase(bool_var v, lbool f);

        bool get_phase(bool_var v) const { return is_true(v); }

        model& get_model() { return m_model; }

    };
}

#endif
