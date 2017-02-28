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

namespace sat {

    class local_search_config {
        unsigned m_seed;
        unsigned m_cutoff_time;
        unsigned m_strategy_id;
        int      m_best_known_value;
    public:
        local_search_config()
        {
            m_seed = 0;
            m_cutoff_time = 1;
            m_strategy_id = 0;
            m_best_known_value = INT_MAX;
        }

        unsigned seed() const { return m_seed; }
        unsigned cutoff_time() const { return m_cutoff_time;  }
        unsigned strategy_id() const { return m_strategy_id;  }
        unsigned best_known_value() const { return m_best_known_value;  }

        void set_seed(unsigned s) { m_seed = s;  }
        void set_cutoff_time(unsigned t) { m_cutoff_time = t;  }
        void set_strategy_id(unsigned i) { m_strategy_id = i; }
        void set_best_known_value(unsigned v) { m_best_known_value = v; }
    };


    class local_search {
		
        typedef svector<bool> bool_vector;

        // data structure for a term in objective function
        struct ob_term {
            bool_var var_id;                          // variable id, begin with 1
            int coefficient;                     // non-zero integer
        };

        // data structure for a term in constraint
        struct term {
            bool_var var_id;                          // variable id, begin with 1
            bool sense;                          // 1 for positive, 0 for negative
            //int coefficient;                   // all constraints are cardinality: coefficient=1
        };

        
        // objective function: maximize
        svector<ob_term>   ob_constraint;        // the objective function *constraint*, sorted in decending order
        
        
        // terms arrays
        vector<svector<term> > constraint_term;  // constraint_term[i][j] means the j'th term of constraint i

        // parameters of the instance
        unsigned num_vars() const { return m_vars.size() - 1; }     // var index from 1 to num_vars
        unsigned num_constraints() const { return constraint_term.size(); } // constraint index from 1 to num_constraint

        
        // information about the variable
        int_vector             coefficient_in_ob_constraint; // initialized to be 0
        // int_vector             sscore;           // slack score
        
        struct var_info {
            bool m_conf_change;                  // whether its configure changes since its last flip
            bool m_in_goodvar_stack;
            int  m_score;
            int  m_slack_score;
            int_vector m_watch[2];
            var_info():
                m_conf_change(true),
                m_in_goodvar_stack(false),
                m_score(0),
                m_slack_score(0)
            {}
        };
        svector<var_info>       m_vars;

        inline int score(unsigned v) const { return m_vars[v].m_score; }
        inline void inc_score(bool_var v) { m_vars[v].m_score++; }
        inline void dec_score(bool_var v) { m_vars[v].m_score--; }

        inline int slack_score(unsigned v) const { return m_vars[v].m_slack_score; }
        inline void inc_slack_score(bool_var v) { m_vars[v].m_slack_score++; }
        inline void dec_slack_score(bool_var v) { m_vars[v].m_slack_score--; }
        
        inline bool already_in_goodvar_stack(unsigned v) const { return m_vars[v].m_in_goodvar_stack; }
        inline bool conf_change(unsigned v) const { return m_vars[v].m_conf_change; }

        int_vector               time_stamp;       // the flip time stamp
        int_vector               cscc;             // how many times its constraint state configure changes since its last flip
        vector<bool_var_vector>  var_neighbor;     // all of its neighborhoods variable
        /* TBD: other scores */
        
        // information about the constraints
        int_vector constraint_k;                // the right side k of a constraint
        int_vector constraint_slack;            // =constraint_k[i]-true_terms[i], if >=0 then sat
        //int_vector nb_slack;                  // constraint_k - ob_var(same in ob) - none_ob_true_terms_count. if < 0: some ob var might be flipped to false, result in an ob decreasing
        //bool_vector has_true_ob_terms; 
        
        // unsat constraint stack
        int_vector m_unsat_stack;               // store all the unsat constraits
        int_vector m_index_in_unsat_stack;      // which position is a contraint in the unsat_stack
        
        // configuration changed decreasing variables (score>0 and conf_change==true)
        int_vector goodvar_stack;

        // information about solution
        bool_vector      cur_solution;        // the current solution
        int              objective_value;     // the objective function value corresponds to the current solution
        bool_vector      best_solution;       // the best solution so far
        int       best_objective_value = -1;   // the objective value corresponds to the best solution so far
        // for non-known instance, set as maximal
        int   best_known_value = INT_MAX;   // best known value for this instance
        
        // cutoff
        int      cutoff_time = 1;            // seconds
        unsigned      max_steps = 2000000000;     // < 2147483647
        clock_t start, stop;
        double			best_time;
        
        // for tuning
        int   s_id = 0;                      // strategy id


        void init();

        void reinit();
        void reinit_orig();

        void init_cur_solution();
        void init_slack();
        void init_scores();
        void init_goodvars();
        
        bool_var pick_var();

        void flip(bool_var v);

        bool tie_breaker_sat(bool_var v1, bool_var v2);

        bool tie_breaker_ccd(bool_var v1, bool_var v2);

        void set_parameters();

        void calculate_and_update_ob();

        void verify_solution();

        void display(std::ostream& out);

        void print_info();

        bool check_goodvar() {
            unsigned g = 0;
            for (unsigned v = 1; v <= num_vars(); ++v) {
                if (conf_change(v) && score(v) > 0) {
                    ++g;
                    if (!already_in_goodvar_stack(v))
                        std::cout << "3\n";
                }
            }
            if (g == goodvar_stack.size())
                return true;
            else {
                if (g < goodvar_stack.size())
                    std::cout << "1\n";
                else
                    std::cout << "2\n"; // delete too many
                return false;
            }
        }

        void add_clause(unsigned sz, literal const* c);


        void unsat(int c) {
            m_index_in_unsat_stack[c] = m_unsat_stack.size();
            m_unsat_stack.push_back(c);
        }
        // swap the deleted one with the last one and pop
        void sat(int c) {
            int last_unsat_constraint = m_unsat_stack.back();
            int index = m_index_in_unsat_stack[c];
            m_unsat_stack[index] = last_unsat_constraint;
            m_index_in_unsat_stack[last_unsat_constraint] = index;
            m_unsat_stack.pop_back();
        }

    public:
        local_search(solver& s);

        ~local_search();

        void add_soft(int l, int weight);

        void add_cardinality(unsigned sz, literal const* c, unsigned k);
        
        lbool operator()();

        lbool check(unsigned sz, literal const* assumptions) { return l_undef; } // TBD

        void cancel() {} // TBD

        local_search_config& config() { return m_config;  }

        local_search_config m_config;
    };
}

#endif
