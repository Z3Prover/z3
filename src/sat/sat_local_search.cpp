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
#include "card_extension.h"

namespace sat {

    void local_search::init() {
        constraint_slack.resize(num_constraints(), 0);
        cur_solution.resize(num_vars(), false);
        m_index_in_unsat_stack.resize(num_constraints(), 0);
        coefficient_in_ob_constraint.resize(num_vars(), 0);
        var_neighbor.reset();
	for (bool_var v = 0; v < num_vars(); ++v) {
            bool_vector is_neighbor(num_vars(), false);
            var_neighbor.push_back(bool_var_vector());
            for (unsigned i = 0; i < var_term[v].size(); ++ i) {
                unsigned c = var_term[v][i].constraint_id;
                for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                    bool_var w = constraint_term[c][j].var_id; 
                    if (w == v || is_neighbor[w]) continue;
                    is_neighbor[w] = true;
                    var_neighbor.back().push_back(w);
                }
            }
	}
    }

    void local_search::reinit() {
        reinit_greedy();
    }

    void local_search::init_cur_solution() {
        cur_solution.resize(num_vars() + 1, false);
        for (unsigned v = 0; v < num_vars(); ++v) {
            cur_solution[v] = (rand() % 2 == 1);
        }
    }

    // figure out slack, and init unsat stack
    void local_search::init_slack() {
        for (unsigned c = 0; c < num_constraints(); ++c) {
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
        for (unsigned v = 0; v < num_vars(); ++v) {
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
        already_in_goodvar_stack.resize(num_vars(), false);
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (score[v] > 0) { // && conf_change[v] == true
                already_in_goodvar_stack[v] = true;
                goodvar_stack.push_back(v);
            }
        }
    }

    void local_search::reinit_orig() {
        constraint_slack = constraint_k;
        
        // init unsat stack
        m_unsat_stack.reset();
        
        // init solution: random now
        init_cur_solution();
        
        // init varibale information
        // variable 0 is the virtual variable

        score.reset(); 
        sscore.reset(); 
        time_stamp.reset(); 
        conf_change.reset(); 
        cscc.reset();

        score.resize(num_vars(), 0);          score[0] = INT_MIN;
        sscore.resize(num_vars(), 0);         sscore[0] = INT_MIN;
        time_stamp.resize(num_vars(), 0);     time_stamp[0] = max_steps;
        conf_change.resize(num_vars(), true); conf_change[0] = false;
        cscc.resize(num_vars(), 1);           cscc[0] = 0;

        init_slack();
        init_scores();
        init_goodvars();                
    }

    void local_search::reinit_greedy() {
        constraint_slack = constraint_k;
        
        // init unsat stack
        m_unsat_stack.reset();
        
        // init solution: greedy
        init_cur_solution();
        
        // init varibale information
        // variable 0 is the virtual variable

        score.reset(); 
        sscore.reset(); 
        time_stamp.reset(); 
        conf_change.reset(); 
        cscc.reset();

        score.resize(num_vars(), 0);          score[0] = INT_MIN;
        sscore.resize(num_vars(), 0);         sscore[0] = INT_MIN;
        time_stamp.resize(num_vars(), 0);     time_stamp[0] = max_steps;
        conf_change.resize(num_vars(), true); conf_change[0] = false;
        cscc.resize(num_vars(), 1);           cscc[0] = 0;
        for (unsigned v = 0; v < num_vars(); ++v) {
            // greedy here!!
            if (coefficient_in_ob_constraint.get(v, 0) != 0)
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

    void local_search::add_clause(unsigned sz, literal const* c) {
        add_cardinality(sz, c, sz - 1);
    }

    void local_search::add_cardinality(unsigned sz, literal const* c, unsigned k) {
        unsigned id = constraint_term.size();
        constraint_term.push_back(svector<term>());
        for (unsigned i = 0; i < sz; ++i) {
            var_term.resize(c[i].var() + 1);
            term t;
            t.constraint_id = id;
            t.var_id = c[i].var();
            t.sense =  c[i].sign();
            var_term[t.var_id].push_back(t);
            constraint_term[id].push_back(t);
        }
        constraint_k.push_back(k);                
    }

    local_search::local_search(solver& s) {

        // copy units
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            add_clause(1, s.m_trail.c_ptr() + i);
        }

        // copy binary clauses
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
                    literal ls[2] = { l, l2 };
                    add_clause(2, ls);
                }
            }
        }

        // copy clauses
        clause_vector::const_iterator it =  s.m_clauses.begin();
        clause_vector::const_iterator end = s.m_clauses.end();
        for (; it != end; ++it) {
            clause& c = *(*it);
            add_clause(c.size(), c.begin());
        }

        // copy cardinality clauses
        card_extension* ext = dynamic_cast<card_extension*>(s.get_extension());
        if (ext) {
            literal_vector lits;
            unsigned sz = ext->m_cards.size();
            for (unsigned i = 0; i < sz; ++i) {
                card_extension::card& c = *ext->m_cards[i];
                unsigned n = c.size();
                unsigned k = c.k();

                // c.lit() <=> c.lits() >= k
                // 
                //    (c.lits() < k) or c.lit()
                // =  (c.lits() + (n - k - 1)*~c.lit()) <= n    
                //
                //    ~c.lit() or (c.lits() >= k)
                // =  ~c.lit() or (~c.lits() <= n - k)
                // =  k*c.lit() + ~c.lits() <= n 
                // 

                lits.reset();
                for (unsigned j = 0; j < n; ++j) lits.push_back(c[j]);
                for (unsigned j = 0; j < n - k - 1; ++j) lits.push_back(~c.lit());
                add_cardinality(lits.size(), lits.c_ptr(), n);
                
                lits.reset();
                for (unsigned j = 0; j < n; ++j) lits.push_back(~c[j]);
                for (unsigned j = 0; j < k; ++j) lits.push_back(c.lit());
                add_cardinality(lits.size(), lits.c_ptr(), n);
            }
            //
            // optionally handle xor constraints.
            //
            SASSERT(ext->m_xors.empty());            
        }
    }
    
    local_search::~local_search() {
    }
    
    void local_search::add_soft(literal l, double weight) {

    }
    
    lbool local_search::operator()() {
        init();
        bool reach_cutoff_time = false;
        bool reach_known_best_value = false;
        bool_var flipvar;
        double elapsed_time = 0;
        clock_t start = clock(), stop;  // TBD, use stopwatch facility
        srand(0);                       // TBD, use random facility and parameters to set random seed.
        set_parameters();
        // ################## start ######################
        //cout << "Start initialize and local search, restart in every " << max_steps << " steps" << endl;
        for (unsigned tries = 0; ; ++tries) {
            reinit();
            for (int step = 1; step <= max_steps; ++step) {
                // feasible
                if (m_unsat_stack.empty()) {
                    calculate_and_update_ob();
                    if (best_objective_value >= best_known_value) {
                        reach_known_best_value = true;
                        break;
                    }
                }
                flipvar = pick_var();
                flip(flipvar);
                time_stamp[flipvar] = step;
            }
            // take a look at watch
            stop = clock();
            elapsed_time = (double)(stop - start) / CLOCKS_PER_SEC;
            if (elapsed_time > cutoff_time)
                reach_cutoff_time = true;
            if (reach_known_best_value || reach_cutoff_time)
                break;
        }
        if (reach_known_best_value) {
            std::cout << elapsed_time << "\n";
        }
        else
            std::cout << -1 << "\n";
        //print_solution();

        // TBD: adjust return status
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
        unsigned num_cs = constraints.size();
        for (unsigned i = 0; i < num_cs; ++i) {
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
        int v_imp = cur_solution[v] ? -coefficient_in_ob_constraint.get(v, 0) : coefficient_in_ob_constraint.get(v, 0);
        int b_imp = cur_solution[best_var] ? -coefficient_in_ob_constraint.get(best_var, 0) : coefficient_in_ob_constraint.get(best_var, 0);
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
        bool_var best_var = num_vars()-1;

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
            max_steps = num_vars();
        else if (s_id == 1)
            max_steps = (int) (1.5 * num_vars());
        else if (s_id == 1)
            max_steps = 2 * num_vars();
        else if (s_id == 2)
            max_steps = (int) (2.5 * num_vars());
        else if (s_id == 3)
            max_steps = 3 * num_vars();
        else {
            std::cout << "Invalid strategy id!" << std::endl;
            exit(-1);
        }
    }

    

}
