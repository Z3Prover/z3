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

namespace sat {

    void local_search::init() {
        constraint_slack.resize(num_constraints + 1);
        cur_solution.resize(num_vars + 1);
        // etc. initialize other vectors.
        init_greedy();
    }

    void local_search::init_orig() {
	int	v, c;        

        for (c = 1; c <= num_constraints; ++c) {
            constraint_slack[c] = constraint_k[c];
        }
        
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
        
        // figure out slack, and init unsat stack
        for (c = 1; c <= num_constraints; ++c) {
            for (unsigned i = 0; i < constraint_term[c].size(); ++i) {
                v = constraint_term[c][i].var_id;
                if (cur_solution[v] == constraint_term[c][i].sense)
                    --constraint_slack[c];
            }
            // constraint_slack[c] = constraint_k[c] - true_terms_count[c];
            // violate the at-most-k constraint
            if (constraint_slack[c] < 0)
                unsat(c);
        }
        
        // figure out variables scores, pscores and sscores
        for (v = 1; v <= num_vars; ++v) {
            for (unsigned i = 0; i < var_term[v].size(); ++i) {
                c = var_term[v][i].constraint_id;
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
        
        // TBD: maybe use util\uint_set or tracked_uint_set instead?
        
        // init goodvars and okvars stack
        for (v = 1; v <= num_vars; ++v) {
            if (score[v] > 0) { // && conf_change[v] == true
                already_in_goodvar_stack[v] = true;
                goodvar_stack.push_back(v);
            }
            else
                already_in_goodvar_stack[v] = false;
        }
    }

    void local_search::init_cur_solution() {
        for (int v = 1; v <= num_vars; ++v) {
            cur_solution[v] = (rand() % 2 == 1);
        }
    }

    void local_search::init_greedy() {
	int	v, c;
        for (c = 1; c <= num_constraints; ++c) {
            constraint_slack[c] = constraint_k[c];
        }
        
        // init unsat stack
        m_unsat_stack.reset();
        
        // init solution: greedy
        init_cur_solution();
        
        // init varibale information
        // variable 0 is the virtual variable
        score[0] = INT_MIN;
        sscore[0] = INT_MIN;
        time_stamp[0] = max_steps;
        conf_change[0] = false;
        cscc[0] = 0;
        for (v = 1; v <= num_vars; ++v) {
            score[v] = 0;
            sscore[v] = 0;
            time_stamp[v] = 0;
            conf_change[v] = true;
            cscc[v] = 1;
            // greedy here!!
            if (coefficient_in_ob_constraint[v] > 0) {
                cur_solution[v] = true;
            }
            else if (coefficient_in_ob_constraint[v] < 0) {
                cur_solution[v] = false;
            }
        }
        
        // figure out slack, and init unsat stack
        for (c = 1; c <= num_constraints; ++c) {
            for (unsigned i = 0; i < constraint_term[c].size(); ++i) {
                v = constraint_term[c][i].var_id;
                if (cur_solution[v] == constraint_term[c][i].sense)
                    //++true_terms_count[c];
                    --constraint_slack[c];
            }
            //constraint_slack[c] = constraint_k[c] - true_terms_count[c];
            // violate the at-most-k constraint
            if (constraint_slack[c] < 0)
                unsat(c);
        }
        
        // figure out variables scores, pscores and sscores
        for (v = 1; v <= num_vars; ++v) {
            for (unsigned i = 0; i < var_term[v].size(); ++i) {
                c = var_term[v][i].constraint_id;
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
        
        // init goodvars and okvars stack
        for (v = 1; v <= num_vars; ++v) {
            if (score[v] > 0) { // && conf_change[v] == true
                already_in_goodvar_stack[v] = true;
                goodvar_stack.push_back(v);
            }
            else
                already_in_goodvar_stack[v] = false;
        }
    }
    

    void local_search::calculate_and_update_ob() {

    }
    
    void local_search::verify_solution() {

    }
    
    void local_search::display(std::ostream& out) {

    }

    local_search::local_search(solver& s) {

    }
    
    local_search::~local_search() {

    }
    
    void local_search::add_soft(literal l, double weight) {

    }
    
    lbool local_search::operator()() {
        return l_undef;
    }


    void local_search::flip(int flipvar)
    {
	// already changed truth value!!!!
	cur_solution[flipvar] = !cur_solution[flipvar];
        
	int v, c;
	int org_flipvar_score = score[flipvar];
	int org_flipvar_sscore = sscore[flipvar];

	// update related clauses and neighbor vars
	for (unsigned i = 0; i < var_term[flipvar].size(); ++i) {
		c = var_term[flipvar][i].constraint_id;
		if (cur_solution[flipvar] == var_term[flipvar][i].sense) {
			//++true_terms_count[c];
			--constraint_slack[c];
			if (constraint_slack[c] == -2) { // from -1 to -2
                            for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                                v = constraint_term[c][j].var_id;
                                // flipping the slack increasing var will no long sat this constraint
                                if (cur_solution[v] == constraint_term[c][j].sense)
                                    //score[v] -= constraint_weight[c];
                                    --score[v];
                            }
			}
			else if (constraint_slack[c] == -1) { // from 0 to -1: sat -> unsat
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
			}
			else if (constraint_slack[c] == 0) { // from 1 to 0
                            for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                                v = constraint_term[c][j].var_id;
                                // flip the slack decreasing var will falsify this constraint
                                if (cur_solution[v] != constraint_term[c][j].sense) {
                                    //score[v] -= constraint_weight[c];
                                    --score[v];
                                    --sscore[v];
                                }
                            }
			}
		}
		else { // if (cur_solution[flipvar] != var_term[i].sense)
                    //--true_terms_count[c];
                    ++constraint_slack[c];
                    if (constraint_slack[c] == 1) { // from 0 to 1
                        for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                            v = constraint_term[c][j].var_id;
                            // flip the slack decreasing var will no long falsify this constraint
                            if (cur_solution[v] != constraint_term[c][j].sense) {
                                //score[v] += constraint_weight[c];
                                ++score[v];
                                ++sscore[v];
                            }
                        }
                    }
                    else if (constraint_slack[c] == 0) { // from -1 to 0: unsat -> sat
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
                    }
                    else if (constraint_slack[c] == -1) { // from -2 to -1
                        for (unsigned j = 0; j < constraint_term[c].size(); ++j) {
                            v = constraint_term[c][j].var_id;
                            // flip the slack increasing var will satisfy this constraint
                            if (cur_solution[v] == constraint_term[c][j].sense)
                                //score[v] += constraint_weight[c];
                                ++score[v];
                        }
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

    bool local_search::tie_breaker_sat(int v, int best_var)
    {
	// most improvement on objective value
	int v_imp = cur_solution[v] ? -coefficient_in_ob_constraint[v] : coefficient_in_ob_constraint[v];
	int b_imp = cur_solution[best_var] ? -coefficient_in_ob_constraint[best_var] : coefficient_in_ob_constraint[best_var];
	// break tie 1: max imp
	if (v_imp > b_imp)
		return true;
	else if (v_imp == b_imp) {
		// break tie 2: conf_change
		if (conf_change[v] && !conf_change[best_var])
			return true;
		else if (conf_change[v] == conf_change[best_var]) {
			// break tie 3: time_stamp
			if (time_stamp[v] < time_stamp[best_var])
				return true;
		}
	}
	return false;
    }

    bool local_search::tie_breaker_ccd(int v, int best_var)
    {
	// break tie 1: max score
	if (score[v] > score[best_var])
		return true;
	else if (score[v] == score[best_var]) {
		// break tie 2: max sscore
		if (sscore[v] > sscore[best_var])
			return true;
		else if (sscore[v] == sscore[best_var]) {
			// break tie 3: cscc
			if (cscc[v] > cscc[best_var])
				return true;
			else if (cscc[v] == cscc[best_var]) {
				// break tie 4: oldest one
				if (time_stamp[v] < time_stamp[best_var])
					return true;
			}
		}
	}
	return false;
    }

    int local_search::pick_var()
    {
	int c, v;
	int best_var = 0;

	// SAT Mode
	if (m_unsat_stack.empty()) {
            //++as;
            for (int i = 1; i <= ob_num_terms; ++i) {
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
