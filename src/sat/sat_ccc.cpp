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

lbool ccc::cube() {
    unsigned branch_id = 0;
    unsigned_vector id_trail;

    lookahead lh(s);
    lh.init_search();
    lh.m_model.reset();

    lookahead::scoped_level _sl(lh, lh.c_fixed_truth);
    literal_vector trail;
    lh.m_search_mode = lookahead_mode::searching;
    while (!m_cancel) {
        // remove old branch ids from id_trail.
        while (id_trail.size() > trail.size()) {
            id_trail.pop_back();
        }
        TRACE("sat", lh.display(tout););
        lh.inc_istamp();
        s.checkpoint();
        if (lh.inconsistent()) {
            if (!lh.backtrack(trail)) return l_false;
            continue;
        }

        // check if CDCL solver got ahead.
        bool repeat = false;
        #pragma omp critical (ccc_solved)
        {
            if (!m_solved.empty()) {
                unsigned solved_id = m_solved.top();
                if (id_trail.contains(solved_id)) {
                    lh.set_conflict();
                }
                else {
                    m_solved.pop();
                }
                repeat = true;
            }
        }
        if (repeat) continue;

        ++branch_id;
        if (!trail.empty()) {
            #pragma omp critical (ccc_decisions)
            {
                m_decisions.push(decision(branch_id, trail.size()-1, trail.back()));
            }
        }

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
        id_trail.push_back(branch_id);
        trail.push_back(l);
        SASSERT(id_trail.size() == trail.size());

        TRACE("sat", tout << "choose: " << l << " " << trail << "\n";);
        ++lh.m_stats.m_decisions;
        IF_VERBOSE(1, verbose_stream() << "select " << pp_prefix(lh.m_prefix, lh.m_trail_lim.size()) << ": " << l << " " << lh.m_trail.size() << "\n";);
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
        s.init_assumptions(0, 0);
        s.propagate(false);
        if (s.check_inconsistent()) return l_false;
        s.cleanup();
        s.simplify_problem();
        if (s.check_inconsistent()) return l_false;

        unsigned_vector ids;
        
        while (true) {
            SASSERT(!s.inconsistent());
            
            lbool r = bounded_search(s, ids);
            if (r != l_undef)
                return r;
            
            if (s.m_conflicts > s.m_config.m_max_conflicts) {
                IF_VERBOSE(SAT_VB_LVL, verbose_stream() << "(sat \"abort: max-conflicts = " << s.m_conflicts << "\")\n";);
                return l_undef;
            }
            
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

lbool ccc::bounded_search(solver& s, unsigned_vector& ids) {
    decision d;

    while (true) {
        s.checkpoint();
        bool done = false;
        while (!done) {
            lbool is_sat = s.propagate_and_backjump_step(done); 
            if (is_sat != l_true) return is_sat;
        }

        if (s.m_scope_lvl < ids.size()) {
            while (ids.size() > s.m_scope_lvl + 1) ids.pop_back();
            unsigned id = ids.back();
            ids.pop_back();
            #pragma omp critical (ccc_solved)
            {
                m_solved.push(id);
            }
        }

        s.gc();

        bool cube_decision = false;
        #pragma omp critical (ccc_decisions)
        {
            if (!m_decisions.empty()) {
                d = m_decisions.pop();
                cube_decision = true;
            }
        }
        if (cube_decision) {
            if (d.m_depth > ids.size()) continue;
            ids.push_back(d.m_id);
            s.pop_reinit(s.m_scope_lvl - d.m_depth); // TBD: check alignment of scopes
            s.push();
            s.assign(d.m_last, justification());
        }
        else if (!s.decide()) {
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

    m_cancel = false;

    scoped_limits      scoped_rlimit(s.rlimit());
    vector<reslimit>   limits;
    ptr_vector<solver> solvers;
    int finished_id = -1;
    std::string        ex_msg;
    par_exception_kind ex_kind;
    unsigned error_code = 0;
    lbool result = l_undef;
    bool canceled = false;

    int num_threads = s.m_config.m_num_threads + 1;
    for (int i = 1; i < num_threads; ++i) {
        limits.push_back(reslimit());
    }

    for (int i = 1; i < num_threads; ++i) {
        s.m_params.set_uint("random_seed", s.m_rand());
        solvers[i] = alloc(sat::solver, s.m_params, limits[i]);
        solvers[i]->copy(s);
        scoped_rlimit.push_child(&solvers[i]->rlimit());            
    }

    #pragma omp parallel for
    for (int i = 0; i < num_threads; ++i) {
        try {                
            lbool r = l_undef;
            if (i == 0) {
                r = cube();
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


    return result;
}

