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
#include "ast/ast_util.h"
#include "solver/solver.h"
#include "solver/solver2tactic.h"
#include "tactic/tactic.h"
#include "tactic/portfolio/fd_solver.h"

class parallel_tactic : public tactic {

    class solver_state {
        ref<solver>     m_solver;
        expr_ref_vector m_cube;
        unsigned        m_units;
    public:
        solver_state(solver* s): m_solver(s), m_cube(s->get_manager()), m_units(0) {}

        solver_state& operator=(solver_state& other) {
            m_solver = other.m_solver;
            m_cube.reset();
            m_cube.append(other.m_cube);
            m_units = other.m_units;
            return *this;
        }

        void update_units() {
            m_units = 0;
            statistics st;
            m_solver->collect_statistics(st);
            std::string units("units");
            for (unsigned i = st.size(); i-- > 0; ) {
                if (st.get_key(i) == units) {
                    m_units = st.get_uint_value(i);
                    break;
                }
            }
        }        

        expr_ref cube() { return mk_and(m_cube); }

        void add_cube(expr* c) { m_cube.push_back(c); }

        unsigned num_units() const { return m_units; }

        solver& get_solver() { return *m_solver; }

        solver const& get_solver() const { return *m_solver; }
    };

public:
    bool operator()(solver_state* s1, solver_state* s2) const {
        return s1->num_units() > s2->num_units();
    }
private:

    ast_manager* m_manager;

    // parameters
    unsigned m_conflicts_lower_bound;
    unsigned m_conflicts_upper_bound;
    unsigned m_conflicts_growth_rate;
    unsigned m_conflicts_decay_rate;
    unsigned m_num_threads;
    
    double     m_progress;
    unsigned   m_max_conflicts;
    statistics m_stats;

    vector<solver_state*> m_solvers;
    scoped_ptr_vector<ast_manager> m_managers;

    void init() {
        m_conflicts_lower_bound = 1000;
        m_conflicts_upper_bound = 10000;
        m_conflicts_growth_rate = 150;
        m_conflicts_decay_rate = 75;
        m_max_conflicts = m_conflicts_lower_bound;
        m_progress = 0;
        m_num_threads = omp_get_num_threads();  // TBD adjust by possible threads used inside each solver.
    }

    unsigned get_max_conflicts() { 
        return m_max_conflicts;
    }

    void set_max_conflicts(unsigned c) {
        m_max_conflicts = c;
    }

    bool should_increase_conflicts() {
        return m_progress < 0;
    }

    void update_progress(bool b) {
        m_progress = 0.9 * m_progress + (b ? 1 : -1);
    }

    int pick_solvers() {
        // order solvers by number of units in descending order
        for (solver_state* s : m_solvers) s->update_units();
        std::sort(m_solvers.c_ptr(), m_solvers.c_ptr() + m_solvers.size(), *this);
        TRACE("parallel_tactic", display(tout););
        return std::min(m_num_threads, m_solvers.size());
    }

    int max_num_splits() {
        if (m_solvers.empty()) {
            return m_num_threads;
        }
        uint64 max_mem = memory::get_max_memory_size();
        uint64 cur_mem = memory::get_allocation_size();
        uint64 sol_sz = cur_mem / m_solvers.size();

        TRACE("parallel_tactic", tout << "max mem: " << max_mem << " cur mem: " << cur_mem << " num solvers: " << m_solvers.size() << "\n";);
        if (max_mem <= cur_mem) {
            return 0;
        }
        if (cur_mem == 0) {
            return m_num_threads;
        }
        uint64 extra_solvers = (max_mem - cur_mem) / (2 * sol_sz);
        if (extra_solvers > m_num_threads) {
            return m_num_threads;
        }
        return static_cast<int>(extra_solvers);
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

    void cube(solver& s, expr_ref_vector& cubes) {
        ast_manager& m = s.get_manager();
        params_ref p;
        p.set_uint("sat.lookahead.cube.cutoff", 1);
        s.updt_params(p);
        while (true) {
            expr_ref c = s.cube();
            if (m.is_false(c)) {
                break;
            }
            cubes.push_back(c);            
        }
    }

    lbool solve(solver& s) {
        params_ref p;
        p.set_uint("sat.max_conflicts", get_max_conflicts());
        s.updt_params(p);
        return s.check_sat(0, 0);
    }

    void remove_unsat(svector<int>& unsat) {
        std::sort(unsat.begin(), unsat.end());
        unsat.reverse();
        DEBUG_CODE(for (unsigned i = 0; i + 1 < unsat.size(); ++i) SASSERT(unsat[i] > unsat[i+1]););
        for (int i : unsat) {
            m_solvers[i]->get_solver().collect_statistics(m_stats);
            dealloc(m_solvers[i]);
            for (unsigned j = i + 1; j < m_solvers.size(); ++j) {
                m_solvers[j - 1] = m_solvers[j];
            }
            m_solvers.shrink(m_solvers.size() - 1);
        }
        unsat.reset();
    }

    void get_model(model_ref& mdl, int sat_index) {
        SASSERT(sat_index != -1);
        m_solvers[sat_index]->get_solver().get_model(mdl);
        ast_translation translate(m_solvers[sat_index]->get_solver().get_manager(), *m_manager);
        mdl = mdl->translate(translate);
    }

    lbool solve(model_ref& mdl) {        
        while (true) {
            int sz = pick_solvers();

            if (sz == 0) {
                return l_false;
            }
            svector<int> unsat;
            int sat_index = -1;

            // Simplify phase.
            IF_VERBOSE(1, verbose_stream() << "(solver.parallel :simplify " << sz << ")\n";);
            #pragma omp parallel for
            for (int i = 0; i < sz; ++i) {
                lbool is_sat = simplify(m_solvers[i]->get_solver());
                switch (is_sat) {
                case l_false: unsat.push_back(i); break;
                case l_true: sat_index = i; break;
                case l_undef: break; 
                }
            }
            if (sat_index != -1) {
                get_model(mdl, sat_index);
                return l_true; 
            }
            sz -= unsat.size();
            remove_unsat(unsat);
            if (sz == 0) continue;
            
            // Solve phase.
            IF_VERBOSE(1, verbose_stream() << "(solver.parallel :solve " << sz << ")\n";);
            #pragma omp parallel for
            for (int i = 0; i < sz; ++i) {
                lbool is_sat = solve(m_solvers[i]->get_solver());
                switch (is_sat) {
                case l_false: update_progress(true); unsat.push_back(i); break;
                case l_true: sat_index = i; break;
                case l_undef: update_progress(false); break; 
                }
            }
            if (sat_index != -1) {
                get_model(mdl, sat_index);
                return l_true; 
            }
            sz -= unsat.size();
            remove_unsat(unsat);

            sz = std::min(max_num_splits(), sz);
            if (sz == 0) continue;
            
            vector<expr_ref_vector> cubes;
            for (int i = 0; i < sz; ++i) {
                cubes.push_back(expr_ref_vector(m_solvers[i]->get_solver().get_manager()));
            }

            // Split phase.            
            IF_VERBOSE(1, verbose_stream() << "(solver.parallel :split " << sz << ")\n";);
            #pragma omp parallel for
            for (int i = 0; i < sz; ++i) {                
                cube(m_solvers[i]->get_solver(), cubes[i]);
            }

            for (int i = 0; i < sz; ++i) {
                if (cubes[i].empty()) {
                    unsat.push_back(i);
                    continue;
                }
                solver& s = m_solvers[i]->get_solver();
                ast_manager& m = s.get_manager();
                for (unsigned j = 1; j < cubes[i].size(); ++j) {
                    ast_manager * new_m = alloc(ast_manager, m, !m.proof_mode());
                    solver* s1 = s.translate(*new_m, params_ref());
                    ast_translation translate(m, *new_m);
                    expr_ref cube(translate(cubes[i][j].get()), *new_m);
                    s1->assert_expr(cube);                    
                    m_managers.push_back(new_m);  
                    solver_state* st = alloc(solver_state, s1);
                    st->add_cube(cube);
                    m_solvers.push_back(st);
                }
                expr* cube0 = cubes[i][0].get();
                m_solvers[i]->add_cube(cube0);
                s.assert_expr(cube0);
            }
            remove_unsat(unsat);
            update_max_conflicts();
        }
        return l_undef;
    }

    std::ostream& display(std::ostream& out) {
        for (solver_state* s : m_solvers) {
            out << "solver units" << s->num_units() << "\n";
            out << "cube " << s->cube() << "\n";
        }
        return out;
    }


public:
    parallel_tactic() :
        m_manager(0) {
        init();
    }

    void operator ()(const goal_ref & g,goal_ref_buffer & result,model_converter_ref & mc,proof_converter_ref & pc,expr_dependency_ref & dep) {
        ast_manager& m = g->m();
        m_manager = &m;
        params_ref p;
        solver* s = mk_fd_solver(m, p);
        m_solvers.push_back(alloc(solver_state, s));
        expr_ref_vector clauses(m);
        ptr_vector<expr> assumptions;
        obj_map<expr, expr*> bool2dep;
        ref<filter_model_converter> fmc;
        extract_clauses_and_dependencies(g, clauses, assumptions, bool2dep, fmc);
        for (expr * clause : clauses) {
            s->assert_expr(clause);
        }
        SASSERT(assumptions.empty());
        model_ref mdl;
        lbool is_sat = solve(mdl);
        switch (is_sat) {
        case l_true:
            if (g->models_enabled()) {
                mc = model2model_converter(mdl.get());
                mc = concat(fmc.get(), mc.get());
            }
            g->reset();
            result.push_back(g.get());
            break;
        case l_false:
            SASSERT(!g->proofs_enabled());
            SASSERT(!g->unsat_core_enabled());
            g->assert_expr(m.mk_false(), nullptr, nullptr);
            break;
        case l_undef:
            if (m.canceled()) {
                throw tactic_exception(Z3_CANCELED_MSG);
            }
            result.push_back(g.get());
            break;
        }
    }

    void cleanup() {
        for (solver_state * s : m_solvers) dealloc(s);
        m_solvers.reset();
        init();
        m_manager = nullptr;
    }

    tactic* translate(ast_manager& m) {
        return alloc(parallel_tactic);
    }

    virtual void updt_params(params_ref const & p) {
        // TBD
    }
    virtual void collect_param_descrs(param_descrs & r) {
        // TBD
    }

    virtual void collect_statistics(statistics & st) const {
        for (solver_state const * s : m_solvers) {
            s->get_solver().collect_statistics(st);
        }
        st.copy(m_stats);
    }
    virtual void reset_statistics() {
        m_stats.reset();
    }

};

tactic * mk_parallel_tactic() {
    return alloc(parallel_tactic);
}

