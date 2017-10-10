/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    parallel_tactic.cpp

Abstract:

    Parallel tactic in the style of Treengeling.

    It assumes a solver that supports good lookaheads.
    

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-9

Notes:
   
--*/

#include "util/scoped_ptr_vector.h"
#include "solver/solver.h"
#include "tactic/tactic.h"

class parallel_tactic : public tactic {

    // parameters
    unsigned m_conflicts_lower_bound;
    unsigned m_conflicts_upper_bound;
    unsigned m_conflicts_growth_rate;
    unsigned m_conflicts_decay_rate;
    unsigned m_num_threads;    

    unsigned m_max_conflicts;

    sref_vector<solver> m_solvers;
    scoped_ptr_vector<ast_manager> m_managers;

    void init() {
        m_conflicts_lower_bound = 1000;
        m_conflicts_upper_bound = 10000;
        m_conflicts_growth_rate = 150;
        m_conflicts_decay_rate = 75;
        m_max_conflicts = m_conflicts_lower_bound;
        m_num_threads = omp_get_num_threads();
    }

    unsigned get_max_conflicts() { 
        return m_max_conflicts;
    }

    void set_max_conflicts(unsigned c) {
        m_max_conflicts = c;
    }

    bool should_increase_conflicts() {
        NOT_IMPLEMENTED_YET();
        return false;
    }

    int pick_solvers() {
        NOT_IMPLEMENTED_YET();
        return 1;
    }

    void update_max_conflicts() {
        if (should_increase_conflicts()) {
            set_max_conflicts(std::min(m_conflicts_upper_bound, m_conflicts_growth_rate * get_max_conflicts() / 100));
        }
        else {
            set_max_conflicts(std::max(m_conflicts_lower_bound, m_conflicts_decay_rate * get_max_conflicts() / 100));
        }
    }

    lbool simplify(solver& s) {
        params_ref p;
        p.set_uint("sat.max_conflicts", 10);
        p.set_bool("sat.lookahead_simplify", true);
        s.updt_params(p);
        lbool is_sat = s.check_sat(0,0);
        p.set_uint("sat.max_conflicts", get_max_conflicts());
        p.set_bool("sat.lookahead_simplify", false);
        s.updt_params(p);
        return is_sat;
    }

    lbool lookahead(solver& s) {
        ast_manager& m = s.get_manager();
        params_ref p;
        p.set_uint("sat.lookahead.cube.cutoff", 1);
        expr_ref_vector cubes(m);
        while (true) {
            expr_ref c = s.cube();
            if (m.is_false(c)) {
                break;
            }
            cubes.push_back(c);            
        }
        if (cubes.empty()) {
            return l_false;
        }
        for (unsigned i = 1; i < cubes.size(); ++i) {
            ast_manager * new_m = alloc(ast_manager, m, !m.proof_mode());
            solver* s1 = s.translate(*new_m, params_ref());
            ast_translation translate(m, *new_m);
            expr_ref cube(translate(cubes[i].get()), *new_m);
            s1->assert_expr(cube);

            #pragma omp critical (_solvers)
            {
                m_managers.push_back(new_m);            
                m_solvers.push_back(s1);
            }
        }
        s.assert_expr(cubes[0].get());
        return l_true;
    }

    lbool solve(solver& s) {
        params_ref p;
        p.set_uint("sat.max_conflicts", get_max_conflicts());
        s.updt_params(p);
        lbool is_sat = s.check_sat(0, 0);
        return is_sat;
    }

    void remove_unsat(svector<int>& unsat) {
        std::sort(unsat.begin(), unsat.end());
        unsat.reverse();
        DEBUG_CODE(for (unsigned i = 0; i + 1 < unsat.size(); ++i) SASSERT(unsat[i] > unsat[i+1]););
        for (int i : unsat) {
            m_solvers.erase(i);
        }
        unsat.reset();
    }

    lbool solve() {        
        while (true) {
            int sz = pick_solvers();

            if (sz == 0) {
                return l_false;
            }
            svector<int> unsat;
            int sat_index = -1;

            // Simplify phase.
            #pragma omp parallel for
            for (int i = 0; i < sz; ++i) {
                lbool is_sat = simplify(*m_solvers[i]);
                switch (is_sat) {
                case l_false: unsat.push_back(i); break;
                case l_true: sat_index = i; break;
                case l_undef: break; 
                }
            }
            if (sat_index != -1) return l_true; // TBD: extact model
            sz -= unsat.size();
            remove_unsat(unsat);
            if (sz == 0) continue;
            
            // Solve phase.
            #pragma omp parallel for
            for (int i = 0; i < sz; ++i) {
                lbool is_sat = solve(*m_solvers[i]);
                switch (is_sat) {
                case l_false: unsat.push_back(i); break;
                case l_true: sat_index = i; break;
                case l_undef: break; 
                }
            }
            if (sat_index != -1) return l_true; // TBD: extact model
            sz -= unsat.size();
            remove_unsat(unsat);
            if (sz == 0) continue;

            // Split phase.            
            #pragma omp parallel for
            for (int i = 0; i < sz; ++i) {
                lbool is_sat = lookahead(*m_solvers[i]);
                switch (is_sat) {
                case l_false: unsat.push_back(i); break;
                case l_true: break;
                case l_undef: break; 
                }
            }
            remove_unsat(unsat);

            update_max_conflicts();
        }
        return l_undef;
    }

public:
    parallel_tactic(solver* s) {
        m_solvers.push_back(s); // clone it?
    }

    void operator ()(const goal_ref & g,goal_ref_buffer & result,model_converter_ref & mc,proof_converter_ref & pc,expr_dependency_ref & dep) {
        NOT_IMPLEMENTED_YET();
    }

    void cleanup() {
        NOT_IMPLEMENTED_YET();
    }

    tactic* translate(ast_manager& m) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }
};

tactic * mk_parallel_tactic(solver* s) {
    return alloc(parallel_tactic, s);
}

