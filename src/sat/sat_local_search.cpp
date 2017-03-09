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
#include "sat_params.hpp"
#include "timer.h"

namespace sat {

    void local_search::init() {

        for (unsigned i = 0; i < m_assumptions.size(); ++i) {
            add_clause(1, m_assumptions.c_ptr() + i);
        }

        // add sentinel variable.
        m_vars.push_back(var_info());

        for (unsigned v = 0; v < num_vars(); ++v) {
            m_vars[v].m_value = (0 == (m_rand() % 2));
        }

        m_best_solution.resize(num_vars() + 1, false);
        m_index_in_unsat_stack.resize(num_constraints(), 0);
        coefficient_in_ob_constraint.resize(num_vars() + 1, 0);

        if (m_config.mode() == local_search_mode::gsat) {
            uint_set is_neighbor;
            for (bool_var v = 0; v < num_vars(); ++v) {
                is_neighbor.reset();
                bool pol = true;
                var_info& vi = m_vars[v];
                for (unsigned k = 0; k < 2; pol = !pol, k++) { 
                    for (unsigned i = 0; i < m_vars[v].m_watch[pol].size(); ++i) {
                        constraint const& c = m_constraints[m_vars[v].m_watch[pol][i]];
                        for (unsigned j = 0; j < c.size(); ++j) {
                            bool_var w = c[j].var(); 
                            if (w == v || is_neighbor.contains(w)) continue;
                            is_neighbor.insert(w);
                            vi.m_neighbors.push_back(w);
                        }
                    }
                }
            }
        }

        for (unsigned i = 0; i < ob_constraint.size(); ++i)
            coefficient_in_ob_constraint[ob_constraint[i].var_id] = ob_constraint[i].coefficient;

        set_parameters();
    }

    void local_search::init_cur_solution() {
        for (unsigned v = 0; v < num_vars(); ++v) {
            // use bias half the time.
            if (m_rand() % 100 < 10) {
                m_vars[v].m_value = ((unsigned)(m_rand() % 100) < m_vars[v].m_bias);
            }
        }
    }

    // figure out slack, and init unsat stack
    void local_search::init_slack() {
        for (unsigned c = 0; c < num_constraints(); ++c) {
            constraint & cn = m_constraints[c];
            for (unsigned i = 0; i < cn.size(); ++i) {
                bool_var v = cn[i].var();
                if (is_true(cn[i]))
                    --cn.m_slack;
            }
            // constraint_slack[c] = constraint_k[c] - true_terms_count[c];
            // violate the at-most-k constraint
            if (cn.m_slack < 0)
                unsat(c);
        }
    }

    // figure out variables scores and slack_scores
    void local_search::init_scores() {
        for (unsigned v = 0; v < num_vars(); ++v) {
            bool is_true = cur_solution(v);
            int_vector& truep = m_vars[v].m_watch[is_true];
            int_vector& falsep = m_vars[v].m_watch[!is_true];
            for (unsigned i = 0; i < falsep.size(); ++i) {
                constraint& c = m_constraints[falsep[i]];
                // will --slack
                if (c.m_slack <= 0) {
                    dec_slack_score(v);
                    if (c.m_slack == 0)
                        dec_score(v);
                }
            }
            for (unsigned i = 0; i < truep.size(); ++i) {
                constraint& c = m_constraints[truep[i]];
                // will --true_terms_count[c]
                // will ++slack
                if (c.m_slack <= -1) {
                    inc_slack_score(v);
                    if (c.m_slack == -1)
                        inc_score(v);
                }
            }
        }
    }

    // init goodvars 
    void local_search::init_goodvars() {
        m_goodvar_stack.reset();
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (score(v) > 0) { // && conf_change[v] == true
                m_vars[v].m_in_goodvar_stack = true;
                m_goodvar_stack.push_back(v);
            }
        }
    }

    void local_search::reinit() {
        for (unsigned i = 0; i < m_constraints.size(); ++i) {
            constraint& c = m_constraints[i];
            c.m_slack = c.m_k;
        }
        
        // init unsat stack
        m_unsat_stack.reset();
        
        // init solution using the bias
        init_cur_solution();
        
        // init varibale information
        // the last variable is the virtual variable

        m_vars.back().m_score = INT_MIN;
        m_vars.back().m_conf_change = false;       
        m_vars.back().m_slack_score = INT_MIN;
        m_vars.back().m_cscc = 0;
        m_vars.back().m_time_stamp = m_max_steps + 1;
        for (unsigned i = 0; i < num_vars(); ++i) {
            m_vars[i].m_time_stamp = 0;
            m_vars[i].m_cscc = 1;
            m_vars[i].m_conf_change = true;
            m_vars[i].m_in_goodvar_stack = false;
            m_vars[i].m_score = 0;
            m_vars[i].m_slack_score = 0;
        }         
        init_slack();
        init_scores();
        init_goodvars();
    }
    
    void local_search::calculate_and_update_ob() {
        unsigned i, v;
        int objective_value = 0;
        for (i = 0; i < ob_constraint.size(); ++i) {
            v = ob_constraint[i].var_id;
            if (cur_solution(v))
                objective_value += ob_constraint[i].coefficient;
        }
        if (objective_value > m_best_objective_value) {
            m_best_solution.reset();
            for (unsigned v = 0; v < num_vars(); ++v) {
                m_best_solution.push_back(cur_solution(v));
            }
            m_best_objective_value = objective_value;
        }
    }

    bool local_search::all_objectives_are_met() const {
        for (unsigned i = 0; i < ob_constraint.size(); ++i) {
            bool_var v = ob_constraint[i].var_id;            
            if (!cur_solution(v)) return false;
        }
        return true;
    }
    
    void local_search::verify_solution() const {
        for (unsigned i = 0; i < m_constraints.size(); ++i) {
            verify_constraint(m_constraints[i]);
        }
    }

    void local_search::verify_unsat_stack() const {
        for (unsigned i = 0; i < m_unsat_stack.size(); ++i) {
            constraint const& c = m_constraints[m_unsat_stack[i]];
            SASSERT(c.m_k < constraint_value(c));
        }
    }

    unsigned local_search::constraint_value(constraint const& c) const {
        unsigned value = 0;
        for (unsigned i = 0; i < c.size(); ++i) {
            value += is_true(c[i]) ? 1 : 0;
        }
        return value;
    }

    void local_search::verify_constraint(constraint const& c) const {
        unsigned value = constraint_value(c);
        if (c.m_k < value) {
            IF_VERBOSE(0, display(verbose_stream() << "violated constraint: ", c);
                       verbose_stream() << "value: " << value << "\n";);
            UNREACHABLE();
        }
    }
    
    void local_search::add_clause(unsigned sz, literal const* c) {
        add_cardinality(sz, c, sz - 1);
    }

    // ~c <= k
    void local_search::add_cardinality(unsigned sz, literal const* c, unsigned k) {
        unsigned id = m_constraints.size();
        m_constraints.push_back(constraint(k));
        for (unsigned i = 0; i < sz; ++i) {
            m_vars.reserve(c[i].var() + 1);
            literal t(~c[i]);
            m_vars[t.var()].m_watch[is_pos(t)].push_back(id);
            m_constraints.back().push(t);
        }
        if (sz == 1 && k == 0) {
            m_vars[c[0].var()].m_bias = c[0].sign() ? 0 : 100;
        }
    }

    local_search::local_search() : 
        m_par(0) {
    }

    void local_search::import(solver& s, bool _init) {        
        m_vars.reset();
        m_constraints.reset();

        m_vars.reserve(s.num_vars());

        // copy units
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            add_clause(1, s.m_trail.c_ptr() + i);
        }

        // copy binary clauses
        {
            unsigned sz = s.m_watches.size();
            for (unsigned l_idx = 0; l_idx < sz; ++l_idx) {
                literal l1 = ~to_literal(l_idx);
                watch_list const & wlist = s.m_watches[l_idx];
                watch_list::const_iterator it  = wlist.begin();
                watch_list::const_iterator end = wlist.end();
                for (; it != end; ++it) {
                    if (!it->is_binary_non_learned_clause())
                        continue;
                    literal l2 = it->get_literal();
                    if (l1.index() > l2.index()) 
                        continue;
                    literal ls[2] = { l1, l2 };
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
        m_num_non_binary_clauses = s.m_clauses.size();

        // copy cardinality clauses
        card_extension* ext = dynamic_cast<card_extension*>(s.get_extension());
        if (ext) {
            literal_vector lits;
            unsigned sz = ext->m_cards.size();
            for (unsigned i = 0; i < sz; ++i) {
                card_extension::card& c = *ext->m_cards[i];
                unsigned n = c.size();
                unsigned k = c.k();

                if (c.lit() == null_literal) {
                    //    c.lits() >= k 
                    // <=> 
                    //    ~c.lits() <= n - k
                    lits.reset();
                    for (unsigned j = 0; j < n; ++j) lits.push_back(c[j]);
                    add_cardinality(lits.size(), lits.c_ptr(), n - k);
                }
                else {
                    // TBD: this doesn't really work because scores are not properly updated for general PB constraints.
                    NOT_IMPLEMENTED_YET();
                    //
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
            }
            //
            // xor constraints should be disabled.
            //
            SASSERT(ext->m_xors.empty());            
        }
        if (_init) {
            init();
        }
    }
    
    local_search::~local_search() {
    }
    
    void local_search::add_soft(bool_var v, int weight) {
        ob_constraint.push_back(ob_term(v, weight));
    }

    lbool local_search::check() {
        return check(0, 0);
    }

#define PROGRESS(tries, flips)                                          \
    if (tries % 10 == 0 || m_unsat_stack.empty()) {                     \
        IF_VERBOSE(1, verbose_stream() << "(sat-local-search"           \
                   << " :flips " << flips                               \
                   << " :unsat " << m_unsat_stack.size()                \
                   << " :time " << (timer.get_seconds() < 0.001 ? 0.0 : timer.get_seconds()) << ")\n";); \
    }

    void local_search::walksat() {
        reinit();
        timer timer;
        timer.start();
        unsigned step = 0, total_flips = 0, tries = 0;
        PROGRESS(tries, total_flips);
        
        for (tries = 1; !m_unsat_stack.empty() && m_limit.inc(); ++tries) {
            for (step = 0; step < m_max_steps && !m_unsat_stack.empty(); ++step) {
                pick_flip_walksat();
            }
            total_flips += step;
            PROGRESS(tries, total_flips);
            if (m_par && tries % 30 == 0) {
                m_par->get_phase(*this);
                reinit();
            }
        }
    }

    void local_search::gsat() {
        reinit();
        bool reach_known_best_value = false;
        bool_var flipvar;
        timer timer;
        timer.start();
        unsigned tries, step = 0, total_flips = 0;
        for (tries = 1; m_limit.inc() && !m_unsat_stack.empty(); ++tries) {
            reinit();
            for (step = 1; step <= m_max_steps; ) {
                // feasible
                if (m_unsat_stack.empty()) {
                    calculate_and_update_ob();
                    if (m_best_objective_value >= m_best_known_value) {
                        break;
                    }
                }                
                flipvar = pick_var_gsat();
                flip_gsat(flipvar);
                m_vars[flipvar].m_time_stamp = step++;
            }
            total_flips += step;
            PROGRESS(tries, total_flips);

            // tell the SAT solvers about the phase of variables.
            if (m_par && tries % 10 == 0) {
                m_par->get_phase(*this);
            }
        }
    }
    
    lbool local_search::check(unsigned sz, literal const* assumptions, parallel* p) {
        flet<parallel*> _p(m_par, p);
        m_model.reset();
        m_assumptions.reset();
        m_assumptions.append(sz, assumptions);
        init();

        switch (m_config.mode()) {
        case local_search_mode::gsat:
            gsat();
            break;
        case local_search_mode::wsat:
            walksat();
            break;
        }


        // remove unit clauses from assumptions.
        m_constraints.shrink(num_constraints() - sz);

        TRACE("sat", display(tout););

        lbool result;
        if (m_unsat_stack.empty() && all_objectives_are_met()) {
            verify_solution();
            extract_model();
            result = l_true;
        }
        else {
            result = l_undef;
        }
        IF_VERBOSE(1, verbose_stream() << "(sat-local-search " << result << ")\n";);
        IF_VERBOSE(2, display(verbose_stream()););
        return result;
    }


    void local_search::sat(unsigned c) {
        unsigned last_unsat_constraint = m_unsat_stack.back();
        int index = m_index_in_unsat_stack[c];
        m_unsat_stack[index] = last_unsat_constraint;
        m_index_in_unsat_stack[last_unsat_constraint] = index;
        m_unsat_stack.pop_back();
    }

    // swap the deleted one with the last one and pop
    void local_search::unsat(unsigned c) {
        m_index_in_unsat_stack[c] = m_unsat_stack.size();
        m_unsat_stack.push_back(c);
    }

    void local_search::pick_flip_walksat() {
        bool_var best_var = null_bool_var;
        unsigned n = 1;
        bool_var v = null_bool_var;
        unsigned num_unsat = m_unsat_stack.size();
        constraint const& c = m_constraints[m_unsat_stack[m_rand() % m_unsat_stack.size()]];
        SASSERT(c.m_k < constraint_value(c));
        if (m_rand() % 100 < 98) {
            // take this branch with 98% probability.
            // find the first one, to fast break the rest    
            unsigned best_bsb = 0;
            literal_vector::const_iterator cit = c.m_literals.begin(), cend = c.m_literals.end();
            literal l;
            for (; !is_true(*cit); ++cit) { SASSERT(cit != cend); }
            l = *cit;
            best_var = v = l.var();
            bool tt = cur_solution(v);
            int_vector const& falsep = m_vars[v].m_watch[!tt];
            int_vector::const_iterator it = falsep.begin(), end = falsep.end();
            for (; it != end; ++it) {
                int slack = constraint_slack(*it);
                if (slack < 0)
                    ++best_bsb;
                else if (slack == 0)
                    best_bsb += num_unsat;
            }
            ++cit;
            for (; cit != cend; ++cit) {
                l = *cit;
                if (is_true(l)) {
                    v = l.var();                    
                    unsigned bsb = 0;
                    int_vector const& falsep = m_vars[v].m_watch[!cur_solution(v)];
                    int_vector::const_iterator it = falsep.begin(), end = falsep.end();
                    for (; it != end; ++it) {
                        int slack = constraint_slack(*it);
                        if (slack < 0) {
                            if (bsb == best_bsb) {
                                break;
                            }
                            else {
                                ++bsb;
                            }
                        }
                        else if (slack == 0) {
                            bsb += num_unsat;
                            if (bsb > best_bsb) {
                                break;
                            }
                        }
                    }
                    if (it == end) {
                        if (bsb < best_bsb) {
                            best_bsb = bsb;
                            best_var = v;
                            n = 1;
                        }
                        else {// if (bb == best_bb)
                            ++n;
                            if (m_rand() % n == 0) {
                                best_var = v;
                            }
                        }
                    }
                }
            }
        }
        else {
            for (unsigned i = 0; i < c.size(); ++i) {
                if (is_true(c[i])) {
                    if (m_rand() % n == 0) {
                        best_var = c[i].var();
                    }
                    ++n;
                }
            }
        }
        flip_walksat(best_var);
    }

    void local_search::flip_walksat(bool_var flipvar) {
        m_vars[flipvar].m_value = !cur_solution(flipvar);

        bool flip_is_true = cur_solution(flipvar);
        int_vector const& truep = m_vars[flipvar].m_watch[flip_is_true];
        int_vector const& falsep = m_vars[flipvar].m_watch[!flip_is_true];

        int_vector::const_iterator it = truep.begin(), end = truep.end();
        for (; it != end; ++it) {
            unsigned ci = *it;
            constraint& c = m_constraints[ci];
            --c.m_slack;
            if (c.m_slack == -1) { // from 0 to -1: sat -> unsat
                unsat(ci);
            }
        }
        it = falsep.begin(), end = falsep.end();
        for (; it != end; ++it) {
            unsigned ci = *it;
            constraint& c = m_constraints[ci];
            ++c.m_slack;
            if (c.m_slack == 0) { // from -1 to 0: unsat -> sat
                sat(ci);
            }
        }

        // verify_unsat_stack();
    }

    void local_search::flip_gsat(bool_var flipvar)
    {
        // already changed truth value!!!!
        m_vars[flipvar].m_value = !cur_solution(flipvar);

        unsigned v;
        int org_flipvar_score = score(flipvar);
        int org_flipvar_slack_score = slack_score(flipvar);

        bool flip_is_true = cur_solution(flipvar);
        int_vector& truep = m_vars[flipvar].m_watch[flip_is_true];
        int_vector& falsep = m_vars[flipvar].m_watch[!flip_is_true];

        // update related clauses and neighbor vars
        for (unsigned i = 0; i < truep.size(); ++i) {
            constraint & c = m_constraints[truep[i]];
            //++true_terms_count[c];
            --c.m_slack;
            switch (c.m_slack) {
            case -2:  // from -1 to -2
                for (unsigned j = 0; j < c.size(); ++j) {
                    v = c[j].var();
                    // flipping the slack increasing var will no longer satisfy this constraint
                    if (is_true(c[j])) {
                        //score[v] -= constraint_weight[c];
                        dec_score(v);
                    }
                }
                break;
            case -1: // from 0 to -1: sat -> unsat
                for (unsigned j = 0; j < c.size(); ++j) {
                    v = c[j].var();
                    inc_cscc(v);
                    //score[v] += constraint_weight[c];
                    inc_score(v);
                    // slack increasing var
                    if (is_true(c[j]))
                        inc_slack_score(v);
                }
                unsat(truep[i]);
                break;
            case 0: // from 1 to 0
                for (unsigned j = 0; j < c.size(); ++j) {
                    v = c[j].var();
                    // flip the slack decreasing var will falsify this constraint
                    if (is_false(c[j])) {
                        // score[v] -= constraint_weight[c];
                        dec_score(v);
                        dec_slack_score(v);
                    }
                }
                break;
            default:
                break;
            }
        }
        for (unsigned i = 0; i < falsep.size(); ++i) {
            constraint& c = m_constraints[falsep[i]];
            //--true_terms_count[c];
            ++c.m_slack;
            switch (c.m_slack) {
            case 1: // from 0 to 1
                for (unsigned j = 0; j < c.size(); ++j) {
                    v = c[j].var();
                    // flip the slack decreasing var will no long falsify this constraint
                    if (is_false(c[j])) {
                        //score[v] += constraint_weight[c];
                        inc_score(v);
                        inc_slack_score(v);
                    }
                }
                break;
            case 0: // from -1 to 0: unsat -> sat
                for (unsigned j = 0; j < c.size(); ++j) {
                    v = c[j].var();
                    inc_cscc(v);
                    //score[v] -= constraint_weight[c];
                    dec_score(v);
                    // slack increasing var no longer sat this var
                    if (is_true(c[j]))
                        dec_slack_score(v);
                }
                sat(falsep[i]);
                break;
            case -1: // from -2 to -1
                for (unsigned j = 0; j < c.size(); ++j) {
                    v = c[j].var();
                    // flip the slack increasing var will satisfy this constraint
                    if (is_true(c[j])) {
                        //score[v] += constraint_weight[c];
                        inc_score(v);
                    }
                }
                break;
            default:
                break;
            }
        }
        m_vars[flipvar].m_score = -org_flipvar_score;
        m_vars[flipvar].m_slack_score = -org_flipvar_slack_score;
        m_vars[flipvar].m_conf_change = false;
        m_vars[flipvar].m_cscc = 0;

        /* update CCD */
        // remove the vars no longer goodvar in goodvar stack
        for (unsigned i = m_goodvar_stack.size(); i > 0;) {
            --i;
            v = m_goodvar_stack[i];
            if (score(v) <= 0) {
                m_goodvar_stack[i] = m_goodvar_stack.back();
                m_goodvar_stack.pop_back();
                m_vars[v].m_in_goodvar_stack = false;
            }
        }
        // update all flipvar's neighbor's conf_change to true, add goodvar/okvar

        var_info& vi = m_vars[flipvar];
        unsigned sz = vi.m_neighbors.size();
        for (unsigned i = 0; i < sz; ++i) {
            v = vi.m_neighbors[i];
            m_vars[v].m_conf_change = true;
            if (score(v) > 0 && !already_in_goodvar_stack(v)) {
                m_goodvar_stack.push_back(v);
                m_vars[v].m_in_goodvar_stack = true;
            }
        }
    }

    bool local_search::tie_breaker_sat(bool_var v, bool_var best_var)  {
        // most improvement on objective value
        int v_imp = cur_solution(v) ? -coefficient_in_ob_constraint.get(v, 0) : coefficient_in_ob_constraint.get(v, 0);
        int b_imp = cur_solution(best_var) ? -coefficient_in_ob_constraint.get(best_var, 0) : coefficient_in_ob_constraint.get(best_var, 0);
        // std::cout << v_imp << "\n";
        // break tie 1: max imp
        // break tie 2: conf_change
        // break tie 3: time_stamp
        
        return 
            (v_imp > b_imp) ||
            ((v_imp == b_imp) && 
             ((conf_change(v) && !conf_change(best_var)) ||
              ((conf_change(v) == conf_change(best_var)) && 
               (time_stamp(v) < time_stamp(best_var)))));
    }

    bool local_search::tie_breaker_ccd(bool_var v, bool_var best_var)  {
        // break tie 1: max score
        // break tie 2: max slack_score
        // break tie 3: cscc
        // break tie 4: oldest one
        return 
            ((score(v) > score(best_var)) ||
             ((score(v) == score(best_var)) &&
              ((slack_score(v) > slack_score(best_var)) ||
               ((slack_score(v) == slack_score(best_var)) &&
                ((cscc(v) > cscc(best_var)) ||
                 ((cscc(v) == cscc(best_var)) && 
                  (time_stamp(v) < time_stamp(best_var))))))));
    }

    bool_var local_search::pick_var_gsat() {
        bool_var best_var = m_vars.size()-1;  // sentinel variable
        // SAT Mode
        if (m_unsat_stack.empty()) {
            //std::cout << "as\t";
            for (unsigned i = 0; i < ob_constraint.size(); ++i) {
                bool_var v = ob_constraint[i].var_id;
                if (tie_breaker_sat(v, best_var))
                    best_var = v;
            }
            return best_var;
        }

        // Unsat Mode: CCD > RD
        // CCD mode
        if (!m_goodvar_stack.empty()) {
            //++ccd;
            best_var = m_goodvar_stack[0];
            for (unsigned i = 1; i < m_goodvar_stack.size(); ++i) {
                bool_var v = m_goodvar_stack[i];
                if (tie_breaker_ccd(v, best_var))
                    best_var = v;
            }
            return best_var;
        }

        // Diversification Mode
        constraint const& c = m_constraints[m_unsat_stack[m_rand() % m_unsat_stack.size()]]; // a random unsat constraint
        // Within c, from all slack increasing var, choose the oldest one
        unsigned c_size = c.size();
        //std::cout << "rd\t";
        for (unsigned i = 0; i < c_size; ++i) {
            bool_var v = c[i].var();
            if (is_true(c[i]) && time_stamp(v) < time_stamp(best_var))
                best_var = v;
        }
        return best_var;
    }

    void local_search::set_parameters()  {
        SASSERT(s_id == 0);
        m_rand.set_seed(m_config.seed());
        //srand(m_config.seed());
        s_id = m_config.strategy_id();
        m_best_known_value = m_config.best_known_value();

        switch (m_config.mode()) {
        case local_search_mode::gsat:
            m_max_steps = 2 * num_vars();
            break;
        case local_search_mode::wsat:
            m_max_steps = std::min(static_cast<unsigned>(20 * num_vars()), static_cast<unsigned>(1 << 17)); // cut steps off at 100K
            break;
        }

        TRACE("sat", 
              tout << "seed:\t" << m_config.seed() << '\n';
              tout << "strategy id:\t" << m_config.strategy_id() << '\n';
              tout << "best_known_value:\t" << m_config.best_known_value() << '\n';
              tout << "max_steps:\t" << m_max_steps << '\n';
              );
    }

    void local_search::print_info(std::ostream& out) {
        for (unsigned v = 0; v < num_vars(); ++v) {
            out << "v" << v << "\t" 
                << m_vars[v].m_neighbors.size() << '\t' 
                << cur_solution(v) << '\t' 
                << conf_change(v)  << '\t' 
                << score(v)        << '\t' 
                << slack_score(v)  << '\n';
        }
    }

    void local_search::extract_model() {
        m_model.reset();
        for (unsigned v = 0; v < num_vars(); ++v) {
            m_model.push_back(cur_solution(v) ? l_true : l_false);
        }
    }

    void local_search::display(std::ostream& out) const {
        for (unsigned i = 0; i < m_constraints.size(); ++i) {
            constraint const& c = m_constraints[i];
            display(out, c);
        }        
        for (bool_var v = 0; v < num_vars(); ++v) {
            display(out, v, m_vars[v]);
        }
    }
    
    void local_search::display(std::ostream& out, constraint const& c) const {
        out << c.m_literals << " <= " << c.m_k << " lhs value: " << constraint_value(c) << "\n";
    }
    
    void local_search::display(std::ostream& out, unsigned v, var_info const& vi) const {
        out << "v" << v << " := " << (vi.m_value?"true":"false") << " bias: " << vi.m_bias << "\n";
    }

    bool local_search::check_goodvar() {
        unsigned g = 0;
        for (unsigned v = 0; v < num_vars(); ++v) {
            if (conf_change(v) && score(v) > 0) {
                ++g;
                if (!already_in_goodvar_stack(v))
                    std::cout << "3\n";
            }
        }
        if (g == m_goodvar_stack.size())
            return true;
        else {
            if (g < m_goodvar_stack.size())
                std::cout << "1\n";
            else
                std::cout << "2\n"; // delete too many
            return false;
        }
    }

    void local_search::set_phase(bool_var v, lbool f) {
        unsigned& bias = m_vars[v].m_bias;
        if (f == l_true && bias < 100) bias++;
        if (f == l_false && bias > 0) bias--;
        // f == l_undef ?
    }

}
