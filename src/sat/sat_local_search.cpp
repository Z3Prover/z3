/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  sat_local_search.cpp

  Abstract:
   
  Local search module for cardinality clauses.

  Author:

  Sixue Liu 2017-2-21

  Notes:

  --*/

#include "sat_local_search.h"
#include "sat_solver.h"

namespace sat {

    void local_search::init() {
        constraint_slack.resize(num_constraints + 1);
        cur_solution.resize(num_vars + 1);
        // etc. initialize other vectors.
        init_greedy();
    }

    void local_search::init_cur_solution() {
        for (unsigned v = 1; v <= num_vars; ++v) {
            cur_solution[v] = (rand() % 2 == 1);
        }
    }

    // figure out slack, and init unsat stack
    void local_search::init_slack() {
        for (unsigned c = 1; c <= num_constraints; ++c) {
            for (unsigned i = 0; i < constraint_term[c].size(); ++i) {
                unsigned v = constraint_term[c][i].var_id;
                if (cur_solution[v] == constraint_term[c][i].sense)
                    --constraint_slack[c];
            }
            // constraint_slack[c] = constraint_k[c] - true_terms_count[c];
            // violate the at-most-k constraint
            if (constraint_slack[c] < 0)
                unsat(c);
        }
    }

    // figure out variables scores, pscores and sscores
    void local_search::init_scores() {
        for (unsigned v = 1; v <= num_vars; ++v) {
            for (unsigned i = 0; i < var_term[v].size(); ++i) {
                int c = var_term[v][i].constraint_id;
                if (cur_solution[v] != var_term[v][i].sense) {
                    // will ++true_terms_count[c]
                    // will --slack
                    if (constraint_slack[c] <= 0) {
                        --sscore[v];
                        if (constraint_slack[c] == 0)
                            --score[v];
                    }
                }
                else { // if (cur_solution[v] == var_term[v][i].sense)
                    // will --true_terms_count[c]
                    // will ++slack
                    if (constraint_slack[c] <= -1) {
                        ++sscore[v];
                        if (constraint_slack[c] == -1)
                            ++score[v];
                    }
                }
            }
        }
    }

    // init goodvars and okvars stack    
    void local_search::init_goodvars() {
        goodvar_stack.reset();
        already_in_goodvar_stack.resize(num_vars+1, false);
        for (unsigned v = 1; v <= num_vars; ++v) {
            if (score[v] > 0) { // && conf_change[v] == true
                already_in_goodvar_stack[v] = true;
                goodvar_stack.push_back(v);
            }
        }
    }

    void local_search::init_orig() {
        constraint_slack = constraint_k;
        
        // init unsat stack
        m_unsat_stack.reset();
        
        // init solution: random now
        init_cur_solution();
        
        // init varibale information
        // variable 0 is the virtual variable

        score.resize(num_vars+1, 0);          score[0] = INT_MIN;
        sscore.resize(num_vars+1, 0);         sscore[0] = INT_MIN;
        time_stamp.resize(num_vars+1, 0);     time_stamp[0] = max_steps;
        conf_change.resize(num_vars+1, true); conf_change[0] = false;
        cscc.resize(num_vars+1, 1);           cscc[0] = 0;

        init_slack();
        init_scores();
        init_goodvars();                
    }

    void local_search::init_greedy() {
        constraint_slack = constraint_k;
        
        // init unsat stack
        m_unsat_stack.reset();
        
        // init solution: greedy
        init_cur_solution();
        
        // init varibale information
        // variable 0 is the virtual variable

        score.resize(num_vars+1, 0);          score[0] = INT_MIN;
        sscore.resize(num_vars+1, 0);         sscore[0] = INT_MIN;
        time_stamp.resize(num_vars+1, 0);     time_stamp[0] = max_steps;
        conf_change.resize(num_vars+1, true); conf_change[0] = false;
        cscc.resize(num_vars+1, 1);           cscc[0] = 0;
        for (unsigned v = 1; v <= num_vars; ++v) {
            // greedy here!!
            if (coefficient_in_ob_constraint[v] != 0)
                cur_solution[v] = (coefficient_in_ob_constraint[v] > 0);
        }

        init_slack();
        init_scores();
        init_goodvars();        
    }
    

    void local_search::calculate_and_update_ob() {

    }
    
    void local_search::verify_solution() {

    }
    
    void local_search::display(std::ostream& out) {

    }

    local_search::local_search(solver& s) {

        // TBD: use solver::copy as a guideline for importing state from a solver.

        // TBD initialize variables
        s.num_vars();

        // copy units
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            unsigned id = constraint_term.size();
            term t;
            t.constraint_id = id;
            t.var_id = s.m_trail[i].var();
            t.sense =  s.m_trail[i].sign();
            var_term[t.var_id].push_back(t);
            constraint_term.push_back(svector<term>());
            constraint_term[id].push_back(t);
            constraint_k.push_back(0);
        }

        // TBD copy binary:
        s.m_watches.size();
        {
            unsigned sz = s.m_watches.size();
            for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
                literal l = ~to_literal(l_idx);
                watch_list const & wlist = s.m_watches[l_idx];
                watch_list::const_iterator it  = wlist.begin();
                watch_list::const_iterator end = wlist.end();
                for (; it != end; ++it) {
                    if (!it->is_binary_non_learned_clause())
                        continue;
                    literal l2 = it->get_literal();
                    if (l.index() > l2.index()) 
                        continue;

                    unsigned id = constraint_term.size();
                    constraint_term.push_back(svector<term>());
                    
                    // TBD: add clause l, l2;

                    constraint_k.push_back(1);
                }
            }
        }


        clause_vector::const_iterator it =  s.m_clauses.begin();
        clause_vector::const_iterator end = s.m_clauses.end();
        for (; it != end; ++it) {
            clause const& c = *(*it);
            unsigned sz = c.size();
            unsigned id = constraint_term.size();
            constraint_term.push_back(svector<term>());
            for (unsigned i = 0; i < sz; ++i) {
                term t;
                t.constraint_id = id;
                t.var_id = c[i].var();
                t.sense =  c[i].sign();
                var_term[t.var_id].push_back(t);
                constraint_term[id].push_back(t);
            }
            constraint_k.push_back(sz-1);
        }

        // TBD initialize cardinalities from m_ext, retrieve cardinality constraints.
        // optionally handle xor constraints.

        num_vars = s.num_vars();
        num_constraints = constraint_term.size();
    }
    
    local_search::~local_search() {

    }
    
    void local_search::add_soft(literal l, double weight) {

    }
    
    lbool local_search::operator()() {
        return l_undef;
    }


    void local_search::flip(bool_var flipvar)
    {
        // already changed truth value!!!!
        cur_solution[flipvar] = !cur_solution[flipvar];
        
        unsigned v, c;
        int org_flipvar_score = score[flipvar];
        int org_flipvar_sscore = sscore[flipvar];

        // update related clauses and neighbor vars
        svector<term> const& constraints = var_term[flipvar];
        unsigned num_constraints = constraints.size();
        for (unsigned i = 0; i < num_constraints; ++i) {
            c = constraints[i].constraint_id;
            if (cur_solution[flipvar] == constraints[i].sense) {
                //++true_terms_count[c];
                --constraint_slack[c];
                switch (constraint_slack[c]) {
                case -2:  // from -1 to -2
                    for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                        v = constraint_term[c][j].var_id;
                        // flipping the slack increasing var will no long sat this constraint
                        if (cur_solution[v] == constraint_term[c][j].sense)
                            //score[v] -= constraint_weight[c];
                            --score[v];
                    }
                    break;
                case -1: // from 0 to -1: sat -> unsat
                    for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                        v = constraint_term[c][j].var_id;
                        ++cscc[v];
                        //score[v] += constraint_weight[c];
                        ++score[v];
                        // slack increasing var
                        if (cur_solution[v] == constraint_term[c][j].sense)
                            ++sscore[v];
                    }
                    unsat(c);
                    break;
                case 0: // from 1 to 0
                    for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                        v = constraint_term[c][j].var_id;
                        // flip the slack decreasing var will falsify this constraint
                        if (cur_solution[v] != constraint_term[c][j].sense) {
                            //score[v] -= constraint_weight[c];
                            --score[v];
                            --sscore[v];
                        }
                    }
                    break;
                default:
                    break;
                }
            }
            else { // if (cur_solution[flipvar] != var_term[i].sense)
                //--true_terms_count[c];
                ++constraint_slack[c];
                switch (constraint_slack[c]) {
                case 1: // from 0 to 1
                    for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                        v = constraint_term[c][j].var_id;
                        // flip the slack decreasing var will no long falsify this constraint
                        if (cur_solution[v] != constraint_term[c][j].sense) {
                            //score[v] += constraint_weight[c];
                            ++score[v];
                            ++sscore[v];
                        }
                    }
                    break;
                case 0: // from -1 to 0: unsat -> sat
                    for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                        v = constraint_term[c][j].var_id;
                        ++cscc[v];
                        //score[v] -= constraint_weight[c];
                        --score[v];
                        // slack increasing var no longer sat this var
                        if (cur_solution[v] == constraint_term[c][j].sense)
                            --sscore[v];
                    }
                    sat(c);
                    break;
                case -1: // from -2 to -1
                    for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                        v = constraint_term[c][j].var_id;
                        // flip the slack increasing var will satisfy this constraint
                        if (cur_solution[v] == constraint_term[c][j].sense)
                            //score[v] += constraint_weight[c];
                            ++score[v];
                    }
                    break;
                default:
                    break;
                }
            }
        }

        score[flipvar] = -org_flipvar_score;
        sscore[flipvar] = -org_flipvar_sscore;

        conf_change[flipvar] = false;
        cscc[flipvar] = 0;

        /* update CCD */
        // remove the vars no longer okvar in okvar stack
        // remove the vars no longer goodvar in goodvar stack
        for (unsigned i = goodvar_stack.size(); i > 0;) {
            --i;
            v = goodvar_stack[i];
            if (score[v] <= 0) {
                goodvar_stack[i] = goodvar_stack.back();
                goodvar_stack.pop_back();
                already_in_goodvar_stack[v] = false;
            }
        }
        // update all flipvar's neighbor's conf_change to true, add goodvar/okvar
        for (unsigned i = 0; i < var_neighbor[flipvar].size(); ++i) {
            v = var_neighbor[flipvar][i];
            conf_change[v] = true;
            if (score[v] > 0 && !already_in_goodvar_stack[v]) {
                goodvar_stack.push_back(v);
                already_in_goodvar_stack[v] = true;
            }
        }
    }

    bool local_search::tie_breaker_sat(bool_var v, bool_var best_var)  {
        // most improvement on objective value
        int v_imp = cur_solution[v] ? -coefficient_in_ob_constraint[v] : coefficient_in_ob_constraint[v];
        int b_imp = cur_solution[best_var] ? -coefficient_in_ob_constraint[best_var] : coefficient_in_ob_constraint[best_var];
        // break tie 1: max imp
        // break tie 2: conf_change
        // break tie 3: time_stamp
        
        return 
            (v_imp > b_imp) ||
            ((v_imp == b_imp) && 
             ((conf_change[v] && !conf_change[best_var]) ||
              ((conf_change[v] == conf_change[best_var]) && 
               (time_stamp[v] < time_stamp[best_var]))));
    }

    bool local_search::tie_breaker_ccd(bool_var v, bool_var best_var)  {
        // break tie 1: max score
        // break tie 2: max sscore
        // break tie 3: cscc
        // break tie 4: oldest one
        return 
             (score[v]  > score[best_var]) ||
            ((score[v] == score[best_var]) &&
              (sscore[v]  > sscore[best_var]) ||
             ((sscore[v] == sscore[best_var]) &&
               (cscc[v]  > cscc[best_var]) ||
              ((cscc[v] == cscc[best_var]) && 
               (time_stamp[v] < time_stamp[best_var]))));
    }

    bool_var local_search::pick_var() {
        int c, v;
        bool_var best_var = null_bool_var;

        // SAT Mode
        if (m_unsat_stack.empty()) {
            //++as;
            for (unsigned i = 0; i < ob_constraint.size(); ++i) {
                v = ob_constraint[i].var_id;
                if (tie_breaker_sat(v, best_var))
                    best_var = v;
            }
            return best_var;
        }

        // Unsat Mode: CCD > RD
        // CCD mode
        if (!goodvar_stack.empty()) {
            //++ccd;
            best_var = goodvar_stack[0];
            for (unsigned i = 1; i < goodvar_stack.size(); ++i) {
                v = goodvar_stack[i];
                if (tie_breaker_ccd(v, best_var))
                    best_var = v;
            }
            return best_var;
        }

        // Diversification Mode
        c = m_unsat_stack[rand() % m_unsat_stack.size()]; // a random unsat constraint
        // Within c, from all slack increasing var, choose the oldest one
        for (unsigned i = 0; i < constraint_term[c].size(); ++i) {
            v = constraint_term[c][i].var_id;
            if (cur_solution[v] == constraint_term[c][i].sense && time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }
        //++rd;
        return best_var;
    }

    void local_search::set_parameters()  {
        if (s_id == 0)
            max_steps = num_vars;
        else if (s_id == 1)
            max_steps = (int) (1.5 * num_vars);
        else if (s_id == 1)
            max_steps = 2 * num_vars;
        else if (s_id == 2)
            max_steps = (int) (2.5 * num_vars);
        else if (s_id == 3)
            max_steps = 3 * num_vars;
        else {
            std::cout << "Invalid strategy id!" << std::endl;
            exit(-1);
        }
    }

    

}
