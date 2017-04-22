/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_ccc.cpp

Abstract:
   
    A variant of Concurrent Cube and Conquer

Author:

    Nikolaj Bjorner (nbjorner) 2017-4-17

Notes:

--*/

#include "sat_solver.h"
#include "sat_lookahead.h"
#include "sat_ccc.h"

using namespace sat;


std::ostream& ccc::decision::pp(std::ostream& out) const {
    return out << "(" << m_id << " " << m_last << " d:" << m_depth << ") ";
}

std::ostream& ccc::pp(std::ostream& out, svector<decision> const& v) {
    for (unsigned i = 0; i < v.size(); ++i) {
        v[i].pp(out);
    }
    return out;
}

lbool ccc::cube2() {
    unsigned branch_id = 0;
    unsigned_vector id_trail;

    lookahead lh(m_s);
    lh.init_search();
    lh.m_model.reset();

    lookahead::scoped_level _sl(lh, lh.c_fixed_truth);
    literal_vector trail;
    svector<decision> decisions;
    lh.m_search_mode = lookahead_mode::searching;
    lh.m_blocked_literal = null_literal;
    lbool r = cube2(branch_id, decisions, lh);
    if (r == l_true) {
        m_model = lh.get_model();
    }
    return r;
}

lbool ccc::cube2(unsigned& branch_id, svector<decision>& decisions, lookahead& lh) {
    m_s.checkpoint();
    
    if (lh.inconsistent()) {
        return l_false;
    }

    lh.inc_istamp();
    
    // check if CDCL solver got ahead.
    bool repeat = false;
    #pragma omp critical (ccc_solved)
    {
        while (!m_solved.empty()) {
            unsigned solved_id = m_solved.top();
            if (contains_branch(decisions, solved_id)) {
                IF_VERBOSE(1, verbose_stream() << "conquer " << decisions.size() << "\n";);
                repeat = true;
                break;
            }           
            else {
                m_solved.pop();
            }
        }
    }
    if (repeat) return l_false;
 
    literal l = lh.choose();
    if (lh.inconsistent()) {
        return l_false;
    }

    if (l == null_literal) {
        return l_true;
    }

    if (!decisions.empty()) {
        #pragma omp critical (ccc_decisions)
        {
            m_decisions.push(decisions.back());
        }
    }

    // update trail and set of ids
    
    ++branch_id;
    ++lh.m_stats.m_decisions;
    unsigned parent_id = decisions.empty() ? 0 : decisions.back().m_id;
    decision d(branch_id, decisions.size() + 1, l, null_literal, parent_id);
    decisions.push_back(d);
    
    #pragma omp critical (ccc_log)                                  
    {                                                       
        IF_VERBOSE(1, verbose_stream() << "select " << pp_prefix(lh.m_prefix, lh.m_trail_lim.size()) << ": " << l << " " << lh.m_trail.size() << "\n";);
        IF_VERBOSE(2, pp(verbose_stream(), decisions) << "\n"; );
    }
    TRACE("sat", tout << "choose: " << l << " " << trail << "\n";);
    lh.push(l, lh.c_fixed_truth);
    lbool r = cube2(branch_id, decisions, lh);
    if (r == l_false) {
        lh.pop();
        lh.flip_prefix();
        lh.push(~l, lh.c_fixed_truth);
        decisions.back().m_last = ~l;
        r = cube2(branch_id, decisions, lh);
        if (r == l_false) {
            lh.pop();
            decisions.pop_back();
        }
    }
    return r;
}

bool ccc::contains_branch(svector<decision> const& decisions, unsigned branch_id) const {
    for (unsigned i = 0; i < decisions.size(); ++i) {
        if (branch_id == decisions[i].m_id) return true;
    }
    return false;
}


lbool ccc::cube() {
    unsigned branch_id = 0;
    unsigned_vector id_trail;

    lookahead lh(m_s);
    lh.init_search();
    lh.m_model.reset();

    lookahead::scoped_level _sl(lh, lh.c_fixed_truth);
    literal_vector trail;
    svector<decision> decisions;
    lh.m_search_mode = lookahead_mode::searching;
    lh.m_blocked_literal = null_literal;
    while (!m_cancel) {

        m_s.checkpoint();

        SASSERT(trail.size() <= decisions.size());
        while (trail.size() < decisions.size()) {
            //check_non_model("lh inconsistent ", decisions);
            decisions.pop_back();
            id_trail.pop_back();
        }
        SASSERT(id_trail.size() == trail.size());
        SASSERT(id_trail.size() == decisions.size());

        TRACE("sat", lh.display(tout););

        if (lh.inconsistent()) {
            if (!lh.backtrack(trail)) return l_false;
            continue;
        }

        lh.inc_istamp();

        // check if CDCL solver got ahead.
        bool repeat = false;
        #pragma omp critical (ccc_solved)
        {
            if (!m_solved.empty()) {
                unsigned solved_id = m_solved.top();
                if (id_trail.contains(solved_id)) {
                    IF_VERBOSE(1, verbose_stream() << "cconquer " << decisions.size() << "\n";);
                    lh.set_conflict();
                }
                else {
                    m_solved.pop();
                }
                repeat = true;
            }
        }
        if (repeat) continue;

        literal l = lh.choose();
        if (lh.inconsistent()) {
            if (!lh.backtrack(trail)) return l_false;
            continue;
        }
        if (l == null_literal) {
            m_model = lh.get_model();
            return l_true;
        }

        // update trail and set of ids

        ++branch_id;
        ++lh.m_stats.m_decisions;
        unsigned parent_id = id_trail.empty() ? 0 : id_trail.back();
        decision d(branch_id, trail.size() + 1, l, lh.m_blocked_literal, parent_id);
        id_trail.push_back(branch_id);
        trail.push_back(l);
        decisions.push_back(d);
        SASSERT(id_trail.size() == trail.size());
        lh.m_blocked_literal = null_literal;
        
        #pragma omp critical (ccc_log)                                  
        {                                                       
            IF_VERBOSE(1, verbose_stream() << "select " << pp_prefix(lh.m_prefix, lh.m_trail_lim.size()) << ": " << l << " " << lh.m_trail.size() << "\n";);
            IF_VERBOSE(2, verbose_stream() << " " << trail << "\n"; pp(verbose_stream(), decisions) << "\n"; );
        }
        #pragma omp critical (ccc_decisions)
        {
            m_decisions.push(d);
        }
        TRACE("sat", tout << "choose: " << l << " " << trail << "\n";);
        lh.push(l, lh.c_fixed_truth);
        SASSERT(lh.inconsistent() || !lh.is_unsat());
    }
    return l_undef;
}

lbool ccc::conquer(solver& s) {
    try {
        if (s.inconsistent()) return l_false;
        s.init_search();
        s.propagate(false);
        if (s.inconsistent()) return l_false;
        s.cleanup();
        s.simplify_problem();
        if (s.inconsistent()) return l_false;

        svector<decision> decisions;
        
        while (true) {
            SASSERT(!s.inconsistent());
            
            lbool r = bounded_search(s, decisions);
            if (r != l_undef)
                return r;
                        
            s.restart();            
            s.simplify_problem();
            if (s.check_inconsistent()) return l_false;
            s.gc();     
        }
    }
    catch (solver::abort_solver) {
        return l_undef;
    }
}

void ccc::replay_decisions(solver& s, svector<decision>& decisions) {
    s.propagate(true);
    for (unsigned i = s.scope_lvl(); !s.inconsistent() && i < decisions.size(); ++i) {
        decision d = decisions[i];
        literal lit = d.m_last;
        lbool val = s.value(lit);
        #pragma omp critical (ccc_log)                                  
        {                                                       
            IF_VERBOSE(2, verbose_stream() << "replay " << lit << " " << val << "\n";);
        }
        if (!push_decision(s, d)) {
            // negation of decision is implied.
            // check_non_model("replay", decisions);
            decisions.resize(i);
            return;
        }
    }
}

bool ccc::push_decision(solver& s, decision const& d) {
    literal lit = d.m_last;
    switch (s.value(lit)) {
    case l_false:
        #pragma omp critical (ccc_solved)
        {
            m_solved.push(d.m_id);
        }
        //TBD:
        s.m_restart_threshold = s.m_config.m_restart_initial;
        //s.m_conflicts_since_last_restart = 0;
        return false;
    case l_true:
        s.push();
        break;
    case l_undef:
        s.push();
        s.assign(lit, justification());
        s.propagate(true);
        break;
    }
    literal blocked = d.m_blocked;
    if (false && blocked != null_literal) {
        switch (s.value(blocked)) {
        case l_false:
            #pragma omp critical (ccc_solved)
            {
                m_solved.push(d.m_id);
            }
            return false;
        case l_true:
            break;
        case l_undef:
            //s.assign(blocked, justification());
            //s.propagate(true);
            break;
        }
    }    
    return true;
}

bool ccc::cube_decision(solver& s, svector<decision>& decisions) {
    decision d;
    bool use_cube_decision = false;
    SASSERT(s.m_qhead == s.m_trail.size());
 get_cube:
    #pragma omp critical (ccc_decisions)
    {
        if (!m_decisions.empty()) {
            d = m_decisions.pop();
            use_cube_decision = true;
        }
    }

    if (!use_cube_decision) {
        return false;
    }
    
    if (!decisions.empty() && decisions.back().m_depth + 1 < d.m_depth) {
        goto get_cube;
    }

    while (!decisions.empty() && decisions.back().m_depth >= d.m_depth) {
        // check_non_model("cube decision", decisions);
        decisions.pop_back();
    }
    SASSERT(decisions.empty() || decisions.back().m_depth + 1 == d.m_depth);
    SASSERT(decisions.empty() || decisions.back().m_id == d.m_parent);
    s.pop_reinit(s.scope_lvl() - decisions.size());
    SASSERT(s.m_qhead == s.m_trail.size());
    SASSERT(s.scope_lvl() == decisions.size());
    #pragma omp critical (ccc_log)                                  
    {                                                       
        literal lit = d.m_last;
        IF_VERBOSE(1, verbose_stream() << "cube " << decisions.size() << "\n";);
        IF_VERBOSE(2, pp(verbose_stream() << "push ", decisions) << " @ " << s.scope_lvl() << " " << s.value(lit) << "\n";
                   if (s.value(lit) == l_false) verbose_stream() << "level: " << s.lvl(lit) << "\n";);
    }
    if (push_decision(s, d)) {
        decisions.push_back(d);
    }    

    return true;
}

lbool ccc::bounded_search(solver& s, svector<decision>& decisions) {    
    while (true) {
        s.checkpoint();
        bool done = false;
        while (!done) {
            replay_decisions(s, decisions);
            lbool is_sat = s.propagate_and_backjump_step(done); 
            if (is_sat != l_true) return is_sat;
        }

        s.gc();
        
        if (!cube_decision(s, decisions) && !s.decide()) {
            lbool is_sat = s.final_check();
            if (is_sat != l_undef) {
                return is_sat;
            }
        }
    }
}


void ccc::push_model(unsigned v, bool sign) {
    if (m_values.size() <= v) {
        m_values.resize(v + 1);
    }
    m_values[v] = sign;
}

void ccc::check_non_model(char const* fn, svector<decision> const& decisions) {
    for (unsigned i = 0; i < decisions.size(); ++i) {
        decision d = decisions[i];
        literal lit = d.m_last;
        if (m_values[lit.var()] != lit.sign()) return;
    }

    #pragma omp critical (ccc_log)                                  
    {                                                       
        pp(verbose_stream() << "backtracking from model " << fn << " ", decisions) << "\n";
    }
}

lbool ccc::search() {
    enum par_exception_kind {
        DEFAULT_EX,
        ERROR_EX
    };

    // set_model();

    m_cancel = false;

    scoped_limits      scoped_rlimit(m_s.rlimit());
    vector<reslimit>   limits;
    ptr_vector<solver> solvers;
    int finished_id = -1;
    std::string        ex_msg;
    par_exception_kind ex_kind;
    unsigned error_code = 0;
    lbool result = l_undef;

    int num_threads = 2; // for ccc-infinity only two threads. s.m_config.m_num_threads + 1;

    for (int i = 1; i < num_threads; ++i) {
        limits.push_back(reslimit());
        m_s.m_params.set_uint("random_seed", m_s.m_rand());
        solver* s1 = alloc(sat::solver, m_s.m_params, limits.back());
        solvers.push_back(s1);
        s1->copy(m_s);
        scoped_rlimit.push_child(&s1->rlimit());            
    }

    #pragma omp parallel for
    for (int i = 0; i < num_threads; ++i) {
        try {                
            lbool r = l_undef;
            if (i == 0) {
                r = cube2();
            }
            else {
                r = conquer(*solvers[i-1]);
            }
            bool first = false;
            #pragma omp critical (par_solver)
            {
                if (finished_id == -1) {
                    finished_id = i;
                    first = true;
                    result = r;
                }
            }
            if (first) {
                for (unsigned j = 0; j < solvers.size(); ++j) {
                    solvers[j]->rlimit().cancel();
                }
                // cancel lookahead solver:
                m_cancel = true;
            }
        }
        catch (z3_error & err) {
            error_code = err.error_code();
            ex_kind = ERROR_EX;                
        }
        catch (z3_exception & ex) {
            ex_msg = ex.msg();
            ex_kind = DEFAULT_EX;    
        }
    }

    if (finished_id > 0 && result == l_true) {
        // set model from auxiliary solver
        m_model = solvers[finished_id - 1]->get_model();
    }

    for (unsigned i = 0; i < solvers.size(); ++i) {            
        dealloc(solvers[i]);
    }
    
    if (finished_id == -1) {
        switch (ex_kind) {
        case ERROR_EX: throw z3_error(error_code);
        default: throw default_exception(ex_msg.c_str());
        }
    }

#if 0
    if (result == l_true) {
        for (unsigned i = 1; i < m_model.size(); ++i) {
            std::cout << "push_model(" << i << ", " << (m_model[i] > 0 ? "false" : "true") << ");\n";
        }
    }
#endif

    return result;
}

