/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_ccc.cpp

Abstract:
   
    A variant of Concurrent Cube and Conquer

Author:

    Nikolaj Bjorner (nbjorner) 2017-4-17

Notes:

    The cube process spawns conquer threads to search parts of the
    state space. 
    The conquer threads have two modes: 
    - emulation mode  - where they try to outpace the cuber on the same search tree
    - complement mode - where they solve a sub-branch not yet explored by the cuber.
    When the conquer thread returns a solved cube it is processed in the following ways:
    - ignore            if solved_id \not\in decisions
    - mark d as closed  if d \in decisions, such that d is marked by solved id
    - backjump          otherwise, conquer thread has solved a branch attempted by the cuber

--*/

#include "sat_solver.h"
#include "sat_lookahead.h"
#include "sat_ccc.h"

using namespace sat;

std::ostream& ccc::decision::pp(std::ostream& out) const {
    out << "(" 
        << "id:" << m_id 
        << " l:" << m_literal 
        << " d:" << m_depth;
    if (m_spawn_id != 0) {
        out << " s:" << m_spawn_id;
    }
    out << ") ";
    return out;
}

std::ostream& ccc::pp(std::ostream& out, svector<decision> const& v) {
    for (unsigned i = 0; i < v.size(); ++i) {
        v[i].pp(out);
    }
    return out;
}

lbool ccc::cube() {
    m_branch_id = 0;
    m_last_closure_level = UINT_MAX;

    lookahead lh(m_s);
    lh.init_search();
    lh.m_model.reset();

    lookahead::scoped_level _sl(lh, lh.c_fixed_truth);
    literal_vector trail;
    svector<decision> decisions;
    lh.m_search_mode = lookahead_mode::searching;
    lbool r = cube(decisions, lh);
    if (r == l_true) {
        m_model = lh.get_model();
    }
    lh.collect_statistics(m_stats);
    return r;
}

lbool ccc::cube(svector<decision>& decisions, lookahead& lh) {
    m_s.checkpoint();
    
    if (lh.inconsistent()) {
        return l_false;
    }

    if (get_solved(decisions)) {
        return l_false;
    }

    lh.inc_istamp(); 
    literal l = lh.choose();
    if (lh.inconsistent()) {
        return l_false;
    }

    if (l == null_literal) {
        return l_true;
    }

    if (!decisions.empty()) {
        put_decision(decisions.back());
    }

    // update trail and decisions
    
    ++lh.m_stats.m_decisions;
    unsigned parent_id = decisions.empty() ? 0 : decisions.back().m_id;
    unsigned spawn_id = spawn_conquer(decisions);
    unsigned branch_id = ++m_branch_id;
    decision d(branch_id, decisions.size() + 1, l, parent_id, spawn_id);
    decisions.push_back(d);
    
    IF_VERBOSE(1, verbose_stream() << "select " << pp_prefix(lh.m_prefix, lh.m_trail_lim.size()) << ": " << l << " " << lh.m_trail.size() << "\n";);
    IF_VERBOSE(2, pp(verbose_stream(), decisions) << "\n"; );
    
    TRACE("sat", tout << "choose: " << l << "\n";);
    lh.push(l, lh.c_fixed_truth);
    lbool r = cube(decisions, lh);
    if (r == l_false) {
        lh.pop();
        if (decisions.back().is_closed()) {
            // branch was solved by a spawned conquer process
            IF_VERBOSE(1, verbose_stream() << "closed " << decisions.back().m_id << "\n";);
            
            r = l_false;
        }
        else {
            lh.flip_prefix();
            lh.push(~l, lh.c_fixed_truth);
            decisions.back().negate();
            r = cube(decisions, lh);
        }
        if (r == l_false) {
            lh.pop();
            decisions.pop_back();
        }
    }
    return r;
}

unsigned ccc::spawn_conquer(svector<decision> const& decisions) {
    unsigned result = 0;
    //
    // decisions must have been solved at a higher level by a conquer thread
    // 
    if (!m_free_threads.empty() && m_last_closure_level <= 1 + decisions.size() + m_free_threads.size()) {
        result = m_free_threads.back();
        m_free_threads.pop_back();
        IF_VERBOSE(1, verbose_stream() << "spawn " << result << "\n";);       
    }
    return result;
}

void ccc::free_conquer(unsigned thread_id) {
    m_free_threads.push_back(thread_id);
}


lbool ccc::conquer(solver& s, unsigned thread_id) {
    SASSERT(thread_id > 0);
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
            
            lbool r = bounded_search(s, decisions, thread_id);
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

void ccc::replay_decisions(solver& s, svector<decision>& decisions, unsigned thread_id) {
    s.propagate(true);
    for (unsigned i = s.scope_lvl(); !s.inconsistent() && i < decisions.size(); ++i) {
        decision const& d = decisions[i];
        IF_VERBOSE(2, verbose_stream() << thread_id << ": replay " << d.get_literal(thread_id) << " " << s.value(d.get_literal(thread_id)) << "\n";);
        
        if (!push_decision(s, decisions, d, thread_id)) {
            // negation of decision is implied.
            // check_non_model("replay", decisions);
            decisions.resize(i);
            return;
        }
    }
}

bool ccc::get_solved(svector<decision>& decisions) {
    // check if CDCL solver got ahead.
    bool found = false;
    #pragma omp critical (ccc_solved)
    {
        while (!m_solved.empty()) {
            solution const& sol = m_solved.top();
            unsigned branch_id = sol.m_branch_id;
            unsigned thread_id = sol.m_thread_id;
            SASSERT(thread_id > 0);
            for (unsigned i = decisions.size(); i > 0; ) {
                --i;
                decision& d = decisions[i];
                if (branch_id == d.m_id) {
                    if (d.m_spawn_id == thread_id) {
                        SASSERT(d.m_spawn_id > 0);
                        free_conquer(thread_id);
                        IF_VERBOSE(1, verbose_stream() << "close " << i << "\n";);
                        d.close();
                    }
                    else {
                        // IF_VERBOSE(1, verbose_stream() << "conquer " << branch_id << " " << i << " " << d.get_literal(thread_id) << "\n";);
                        found = true;
                    }
                    m_last_closure_level = d.m_depth;
                    break;
                }
            }
            if (found) {
                break;
            }
            // IF_VERBOSE(1, verbose_stream() << "not found: " << branch_id << " " << decisions.size() << "\n";);
            m_solved.pop();            
        }
    }
    return found;
}

void ccc::put_decision(decision const& d) {
    #pragma omp critical (ccc_decisions)
    {
        for (unsigned i = 0; i < m_num_conquer; ++i) {
            m_decisions[i].push(d);
        }
    }
}

bool ccc::get_decision(unsigned thread_id, decision& d) {
    SASSERT(0 < thread_id && thread_id <= m_decisions.size());
    bool result = false;
    #pragma omp critical (ccc_decisions)
    {
        if (!m_decisions[thread_id - 1].empty()) {
            d = m_decisions[thread_id - 1].pop();
            result = true;
        }
    }
    return result;
}

bool ccc::push_decision(solver& s, svector<decision> const& decisions, decision const& d, unsigned thread_id) {
    literal lit = d.get_literal(thread_id);
    switch (s.value(lit)) {
    case l_false:
        // TBD: we leak conquer threads if they backjump below spawn point.
        if (decisions.empty() && decisions.back().m_spawn_id == thread_id && decisions.back().m_id != d.m_id) {
            IF_VERBOSE(0, verbose_stream() << "LEAK avoided\n";);
            #pragma omp critical (ccc_solved)
            {
                m_solved.push(solution(thread_id, decisions.back().m_id));
            }            
        }
        #pragma omp critical (ccc_solved)
        {
            m_solved.push(solution(thread_id, d.m_id));
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
    return true;
}

bool ccc::cube_decision(solver& s, svector<decision>& decisions, unsigned thread_id) {
    decision d;
    bool use_cube_decision = false;
    SASSERT(s.m_qhead == s.m_trail.size());

 get_cube:
    if (!get_decision(thread_id, d)) {
        return false;
    }
    
    if (!decisions.empty() && decisions.back().m_depth + 1 < d.m_depth) {
        goto get_cube;
    }

    if (!decisions.empty() && decisions.back().m_spawn_id == thread_id && decisions.back().m_depth < d.m_depth) {
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
    literal lit = d.get_literal(thread_id);
    IF_VERBOSE(1, verbose_stream() << thread_id << ": cube " << decisions.size() << " " << d.get_literal(thread_id) << "\n";);
    IF_VERBOSE(2, pp(verbose_stream() << thread_id << ": push ", decisions) << " @ " << s.scope_lvl() << " " << s.value(lit) << "\n";
               if (s.value(lit) == l_false) verbose_stream() << "level: " << s.lvl(lit) << "\n";);
    
    if (push_decision(s, decisions, d, thread_id)) {
        decisions.push_back(d);
    }    

    return true;
}

lbool ccc::bounded_search(solver& s, svector<decision>& decisions, unsigned thread_id) {    
    while (true) {
        s.checkpoint();
        bool done = false;
        while (!done) {
            replay_decisions(s, decisions, thread_id);
            lbool is_sat = s.propagate_and_backjump_step(done); 
            if (is_sat != l_true) return is_sat;
        }

        s.gc();
        
        if (!cube_decision(s, decisions, thread_id) && !s.decide()) {
            lbool is_sat = s.final_check();
            if (is_sat != l_undef) {
                return is_sat;
            }
        }
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
    m_decisions.reset();

    m_num_conquer = m_s.m_config.m_num_threads;
    int num_threads = 1 + m_num_conquer; // for ccc-infinity only two threads.

    for (int i = 1; i < num_threads; ++i) {
        limits.push_back(reslimit());
        m_s.m_params.set_uint("random_seed", m_s.m_rand());
        solver* s1 = alloc(sat::solver, m_s.m_params, limits.back());
        solvers.push_back(s1);
        s1->copy(m_s);
        scoped_rlimit.push_child(&s1->rlimit());            
        m_decisions.push_back(queue<decision>());
    }    
    for (unsigned i = 1; i < m_num_conquer; ++i) {
        m_free_threads.push_back(i);
    }

    #pragma omp parallel for
    for (int i = 0; i < num_threads; ++i) {
        try {                
            lbool r = l_undef;
            if (i == 0) {
                r = cube();
            }
            else {
                r = conquer(*solvers[i-1], i);
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
        solvers[i]->collect_statistics(m_stats);
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


#if 0
void ccc::push_model(unsigned v, bool sign) {
    if (m_values.size() <= v) {
        m_values.resize(v + 1);
    }
    m_values[v] = sign;
}

void ccc::check_non_model(char const* fn, svector<decision> const& decisions) {
    for (unsigned i = 0; i < decisions.size(); ++i) {
        decision d = decisions[i];
        literal lit = d.m_literal;
        if (m_values[lit.var()] != lit.sign()) return;
    }

    IF_VERBOSE(1, pp(verbose_stream() << "backtracking from model " << fn << " ", decisions) << "\n";);
}
#endif
