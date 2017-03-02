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

#include "vector.h"
#include "sat_types.h"
#include "rlimit.h"

namespace sat {

    class parallel;

    class local_search_config {
        unsigned m_seed;
        unsigned m_strategy_id;
        int      m_best_known_value;
    public:
        local_search_config()
        {
            m_seed = 0;
            m_strategy_id = 0;
            m_best_known_value = INT_MAX;
        }

        unsigned seed() const { return m_seed; }
        unsigned strategy_id() const { return m_strategy_id;  }
        unsigned best_known_value() const { return m_best_known_value;  }

        void set_seed(unsigned s) { m_seed = s;  }
        void set_strategy_id(unsigned i) { m_strategy_id = i; }
        void set_best_known_value(unsigned v) { m_best_known_value = v; }
    };


    class local_search {
		
        typedef svector<bool> bool_vector;

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
            bool m_conf_change;                  // whether its configure changes since its last flip
            bool m_in_goodvar_stack;
            int  m_score;
            int  m_slack_score;
            int  m_time_stamp;                   // the flip time stamp                 
            int  m_cscc;                         // how many times its constraint state configure changes since its last flip
            bool_var_vector m_neighbors;         // neighborhood variables
            int_vector m_watch[2];
            var_info():
                m_value(true),
                m_bias(50), 
                m_conf_change(true),
                m_in_goodvar_stack(false),
                m_score(0),
                m_slack_score(0),
                m_cscc(0)
            {}
        };

        struct constraint {
            unsigned        m_k;
            int             m_slack;
            literal_vector  m_literals;
            constraint(unsigned k) : m_k(k), m_slack(0) {}
            unsigned size() const { return m_literals.size(); }
            literal const& operator[](unsigned idx) const { return m_literals[idx]; }
        };

        local_search_config m_config;

        // objective function: maximize
        svector<ob_term>   ob_constraint;        // the objective function *constraint*, sorted in decending order
                        
        // information about the variable
        int_vector             coefficient_in_ob_constraint; // var! initialized to be 0
        

        vector<var_info>       m_vars;

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
        
        /* TBD: other scores */
        

        vector<constraint> m_constraints;

        inline bool is_pos(literal t) const { return !t.sign(); }
        inline bool is_true(bool_var v) const { return cur_solution(v); }
        inline bool is_true(literal l) const { return cur_solution(l.var()) != l.sign(); }
        inline bool is_false(literal l) const { return cur_solution(l.var()) == l.sign(); }

        unsigned num_constraints() const { return m_constraints.size(); } // constraint index from 1 to num_constraint

        
        // int_vector nb_slack;                 // constraint_k - ob_var(same in ob) - none_ob_true_terms_count. if < 0: some ob var might be flipped to false, result in an ob decreasing
        // bool_vector has_true_ob_terms; 
        
        // unsat constraint stack
        int_vector m_unsat_stack;               // store all the unsat constraits
        int_vector m_index_in_unsat_stack;      // which position is a contraint in the unsat_stack
        
        // configuration changed decreasing variables (score>0 and conf_change==true)
        int_vector goodvar_stack;

        // information about solution
        int              objective_value;      // the objective function value corresponds to the current solution
        bool_vector      best_solution;        // !var: the best solution so far
        int       best_objective_value = -1;   // the objective value corresponds to the best solution so far
        // for non-known instance, set as maximal
        int   best_known_value = INT_MAX;      // best known value for this instance
        
        unsigned      max_steps = 2000000000;  // < 2147483647
        
        // for tuning
        int   s_id = 0;                        // strategy id

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
        
        bool_var pick_var();

        void flip(bool_var v);

        void unsat(unsigned c);

        void sat(unsigned c);

        bool tie_breaker_sat(bool_var v1, bool_var v2);

        bool tie_breaker_ccd(bool_var v1, bool_var v2);

        void set_parameters();

        void calculate_and_update_ob();

        bool all_objectives_are_met() const;

        void verify_solution() const;

        void verify_constraint(constraint const& c) const;

        unsigned constraint_value(constraint const& c) const;

        void print_info(std::ostream& out);

        void extract_model();

        bool check_goodvar();

        void add_clause(unsigned sz, literal const* c);

        void display(std::ostream& out) const;

        void display(std::ostream& out, constraint const& c) const;

        void display(std::ostream& out, unsigned v, var_info const& vi) const;

    public:

        local_search(solver& s);

        reslimit& rlimit() { return m_limit; }

        ~local_search();

        void add_soft(bool_var v, int weight);

        void add_cardinality(unsigned sz, literal const* c, unsigned k);
        
        lbool check();

        lbool check(unsigned sz, literal const* assumptions, parallel* p = 0);

        local_search_config& config() { return m_config;  }

        unsigned num_vars() const { return m_vars.size() - 1; }     // var index from 1 to num_vars

        void set_phase(bool_var v, lbool f);

        bool get_phase(bool_var v) const { return is_true(v); }

        model& get_model() { return m_model; }
    };
}

#endif
