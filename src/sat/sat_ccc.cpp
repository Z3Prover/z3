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

// ------------
// cuber

ccc::cuber::cuber(ccc& c): m_ccc(c), lh(c.m_s), m_branch_id(0) {}

lbool ccc::cuber::search() {
    m_branch_id = 0;
    m_last_closure_level = 1000;

    lh.init_search();
    lh.m_model.reset();

    lookahead::scoped_level _sl(lh, lh.c_fixed_truth);
    lh.m_search_mode = lookahead_mode::searching;
    lbool r = research();
    if (r == l_true) {
        m_ccc.m_model = lh.get_model();
    }
    lh.collect_statistics(m_ccc.m_lh_stats);
    return r;
}

lbool ccc::cuber::research() {
    m_ccc.m_s.checkpoint();
    
    if (lh.inconsistent()) {
        return l_false;
    }

    if (get_solved()) {
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
        m_ccc.put_decision(decisions.back());
    }

    // update trail and decisions
    
    ++lh.m_stats.m_decisions;
    unsigned parent_id = decisions.empty() ? 0 : decisions.back().m_id;
    unsigned spawn_id = spawn_conquer();
    unsigned branch1 = m_branch_id++;
    unsigned branch2 = m_branch_id++;
    decision d(branch1, decisions.size() + 1, l, parent_id, spawn_id);
    decisions.push_back(d);
    
    IF_VERBOSE(1, d.pp(verbose_stream() << "select " << m_last_closure_level << " ") << "\n";);
    IF_VERBOSE(1, verbose_stream() << "select " << pp_prefix(lh.m_prefix, lh.m_trail_lim.size()) << ": " << l << " " << lh.m_trail.size() << "\n";);
    IF_VERBOSE(2, pp(verbose_stream(), decisions) << "\n"; );
    
    TRACE("sat", tout << "choose: " << l << "\n";);
    lh.push(l, lh.c_fixed_truth);
    lbool r = research();
    if (r == l_false) {
        lh.pop();
        if (decisions.back().is_closed()) {
            // branch was solved by a spawned conquer process
            IF_VERBOSE(1, decisions.back().pp(verbose_stream() << "closed ") << "\n";);            
            r = l_false;
            decisions.pop_back();
        }
        else {
            if (spawn_id > 0) {
                free_conquer(spawn_id);
                m_last_closure_level *= 3;
                m_last_closure_level /= 4;
            }
            lh.inc_istamp(); 
            lh.flip_prefix();
            lh.push(~l, lh.c_fixed_truth);
            decisions.back().negate();
            decisions.back().m_id = branch2;
            decisions.back().m_spawn_id = 0;
            r = research();
            if (r == l_false) {
                lh.pop();
                decisions.pop_back();
            }
        }
    }
    return r;
}

void ccc::cuber::update_closure_level(decision const& d, int offset) {
    m_last_closure_level = (d.m_depth + 3*m_last_closure_level) / 4;
    if (m_last_closure_level >= static_cast<unsigned>(abs(offset))) {
        m_last_closure_level += offset;
    }                        
}

unsigned ccc::cuber::spawn_conquer() {
    unsigned result = 0;
    //
    // decisions must have been solved at a higher level by a conquer thread
    // 
    if (!m_free_threads.empty()) {
        if (m_last_closure_level <= decisions.size()) {
            result = m_free_threads.back();
            ++m_ccc.m_ccc_stats.m_spawn_opened;
            m_free_threads.pop_back();
        }
        else {
            IF_VERBOSE(1, verbose_stream() << m_last_closure_level << " " << decisions.size() << "\n";);
        }
    }
    return result;
}


void ccc::cuber::free_conquer(unsigned id) {
    if (id != 0) {
        m_free_threads.push_back(id);
    }
}


bool ccc::cuber::get_solved() {
    // check if CDCL solver got ahead.
    bool do_pop = false;
    solution sol;
    while (true) {
        bool is_empty = true;
        #pragma omp critical (ccc_solved)
        {
            if (do_pop) m_ccc.m_solved.pop_front();
            if (!m_ccc.m_solved.empty()) {
                sol = m_ccc.m_solved.top();
                is_empty = false;
            }
        } 
        if (is_empty) {
            return false;
        }
        do_pop = true;
        unsigned branch_id = sol.m_branch_id;
        unsigned thread_id = sol.m_thread_id;
        bool found = false;
        for (unsigned i = decisions.size(); i > 0; ) {
            --i;
            decision& d = decisions[i];
            if (branch_id == d.m_id) {
                if (d.m_spawn_id == thread_id && thread_id != 0) {
                    SASSERT(d.m_spawn_id > 0);
                    IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << ": spawn close ") << "\n";);
                    ++m_ccc.m_ccc_stats.m_spawn_closed;
                    d.close();
                    free_conquer(thread_id);
                    update_closure_level(d, -1);
                    break;
                }
                else {
                    IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << ": conquer ") << "\n";);
                    ++m_ccc.m_ccc_stats.m_cdcl_closed;
                    update_closure_level(d, 1);
                    return true;
                }               
            }
            // branch is even, d has moved to the next branch
            if (branch_id == (d.m_id & ~0x1) && d.m_spawn_id == thread_id && thread_id != 0) {
                IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << ": spawn conquer ") << "\n";);
                ++m_ccc.m_ccc_stats.m_cdcl_closed;
                update_closure_level(d, 1);
                return true;
            }
        }        
    }
}

// ---------------------
// conquer state machine

lbool ccc::conquer::search() {
    try {
        if (s.inconsistent()) return l_false;
        s.init_search();
        s.propagate(false);
        if (s.inconsistent()) return l_false;
        s.cleanup();
        s.simplify_problem();
        if (s.inconsistent()) return l_false;
        
        while (true) {
            SASSERT(!s.inconsistent());
            
            lbool r = bounded_search();
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

void ccc::conquer::replay_decisions() {
    s.propagate(true);
    for (unsigned i = s.scope_lvl(); !s.inconsistent() && i < decisions.size(); ++i) {
        decision const& d = decisions[i];
        IF_VERBOSE(2, verbose_stream() << thread_id << ": replay " << d.get_literal(thread_id) << " " << s.value(d.get_literal(thread_id)) << "\n";);
        
        if (!push_decision(d)) {
            // negation of decision is implied.
            IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << ": backjump to level " << i << " ") << "\n";);
            while (decisions.size() > i) {
                pop_decision(decisions.back());
                decisions.pop_back();
            }
            break;
        }

        if (d.m_spawn_id == thread_id && d.is_left()) {
            // we pushed the right branch on this thread.
            IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << ": skip left branch on level " << i + 1 << " ") << "\n";);
            break;
        }
    }
}

void ccc::conquer::pop_decision(decision const& d) {
    unsigned tid = 0;
    if (d.is_spawned(thread_id)) {
        tid = thread_id;
        m_spawned = false;
        IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << ": retire spawn ") << "\n";);
    }
    #pragma omp critical (ccc_solved)
    {
        m_ccc.m_solved.push(solution(tid, d.m_id));
    }
}

bool ccc::conquer::push_decision(decision const& d) {
    literal lit = d.get_literal(thread_id);
    switch (s.value(lit)) {
    case l_false:
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
    m_spawned |= d.is_spawned(thread_id);
    return true;
}

bool ccc::conquer::cube_decision() {
    decision d;
    bool use_cube_decision = false;
    SASSERT(s.m_qhead == s.m_trail.size());

    while (true) {
        if (!m_ccc.get_decision(thread_id, d)) {
            return false;
        }

        if (d.is_spawned(thread_id)) IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << " ") << "\n";);
    
        if (!decisions.empty() && decisions.back().m_depth + 1 < d.m_depth) {
            if (d.is_spawned(thread_id)) {
                pop_decision(d);
            }           
        }
        else {
            break;
        }
    }    
    SASSERT(decisions.empty() || decisions.back().m_depth + 1 >= d.m_depth);

    if (!decisions.empty() && decisions.back().is_spawned(thread_id) && decisions.back().m_depth == d.m_depth) {
        SASSERT(d.m_spawn_id == 0);
        SASSERT(decisions.back().is_left());
        SASSERT(!d.is_left());
        IF_VERBOSE(1, verbose_stream() << thread_id << " inherit spawn\n";);
        decisions.back().m_spawn_id = 0;
        m_spawned = false;
    }
    SASSERT(decisions.empty() || decisions.back().m_depth + 1 >= d.m_depth);

    while (!decisions.empty() && decisions.back().m_depth >= d.m_depth) {
        // check_non_model("cube decision", decisions);
        if (decisions.back().is_spawned(thread_id)) {
            pop_decision(decisions.back());
        }
        decisions.pop_back();
    }

    SASSERT(decisions.empty() || decisions.back().m_depth + 1 == d.m_depth);
    SASSERT(decisions.empty() || decisions.back().m_id == d.m_parent);
    if (m_spawned) {
        decisions.push_back(d);
        return true;
    }

    s.pop_reinit(s.scope_lvl() - decisions.size());
    SASSERT(s.m_qhead == s.m_trail.size());
    SASSERT(s.scope_lvl() == decisions.size());
    literal lit = d.get_literal(thread_id);
    IF_VERBOSE(1, d.pp(verbose_stream() << thread_id << ": cube ") << "\n";);
    IF_VERBOSE(2, pp(verbose_stream() << thread_id << ": push ", decisions) << " @ " << s.scope_lvl() << " " << s.value(lit) << "\n";
               if (s.value(lit) == l_false) verbose_stream() << "level: " << s.lvl(lit) << "\n";);
    
    if (push_decision(d)) {
        decisions.push_back(d);
    }    
    else {
        pop_decision(d);
    }

    return true;
}

lbool ccc::conquer::bounded_search() {    
    while (true) {
        s.checkpoint();
        bool done = false;
        while (!done) {
            replay_decisions();
            lbool is_sat = s.propagate_and_backjump_step(done); 
            if (is_sat != l_true) return is_sat;
        }

        s.gc();
        
        if (!cube_decision() && !s.decide()) {
            lbool is_sat = s.final_check();
            if (is_sat != l_undef) {
                return is_sat;
            }
        }
    }
}

// --------------
// shared state

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

bool ccc::get_decision(unsigned thread_id, decision& d) {
    SASSERT(0 < thread_id && thread_id <= m_decisions.size());
    bool result = false;
    #pragma omp critical (ccc_decisions)
    {
        if (!m_decisions[thread_id - 1].empty()) {
            d = m_decisions[thread_id - 1].pop_front();
            result = true;
        }
    }
    return result;
}

void ccc::put_decision(decision const& d) {
    for (unsigned i = 0; i < m_num_conquer; ++i) {
        #pragma omp critical (ccc_decisions)
        {
            while (false && !m_decisions[i].empty()) { // introduces contention.
                decision d = m_decisions[i].back();
                if (d.m_depth < d.m_depth || d.m_spawn_id != 0) {
                    break;
                }
                m_decisions[i].pop_back();
            }
            m_decisions[i].push(d);
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
    ptr_vector<conquer> solvers;
    int finished_id = -1;
    std::string        ex_msg;
    par_exception_kind ex_kind;
    unsigned error_code = 0;
    lbool result = l_undef;
    m_decisions.reset();

    cuber cuber(*this);

    m_num_conquer = m_s.m_config.m_num_threads;
    int num_threads = 1 + m_num_conquer; // for ccc-infinity only two threads.

    for (int i = 1; i < num_threads; ++i) {
        m_s.m_params.set_uint("random_seed", m_s.m_rand());
        conquer* s1 = alloc(conquer, *this, m_s.m_params, i);
        solvers.push_back(s1);
        s1->s.copy(m_s);
        scoped_rlimit.push_child(&(s1->m_limit));
        m_decisions.push_back(queue<decision>());
    }    
    for (unsigned i = 1; i < m_num_conquer; ++i) {
        cuber.m_free_threads.push_back(i);
    }

    #pragma omp parallel for
    for (int i = 0; i < num_threads; ++i) {
        try {                
            lbool r = l_undef;
            if (i == 0) {
                r = cuber.search();
            }
            else {
                r = solvers[i-1]->search();
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
                    solvers[j]->m_limit.cancel();
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
        m_model = solvers[finished_id - 1]->s.get_model();
    }

    for (unsigned i = 0; i < solvers.size(); ++i) {            
        solvers[i]->s.collect_statistics(m_lh_stats);
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
