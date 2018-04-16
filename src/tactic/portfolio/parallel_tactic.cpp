/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    parallel_tactic.cpp

Abstract:

    Parallel tactic based on cubing.
    

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-9
    Miguel Neves 

Notes:
 
 A task comprises of a non-empty sequence of cubes, a type and parameters

 It invokes the following procedure:
  1. Clone the state with the remaining cubes if there is more than one cube. Re-enqueue the remaining cubes.
  2. Apply simplifications and pre-processing according to configuration.
  3. Cube using the parameter settings prescribed in m_params.
  4. Optionally pass the cubes as assumptions and solve each sub-cube with a prescribed resource bound.
  5. Assemble cubes that could not be solved and create a cube state.
 
--*/

#include <thread>
#include <mutex>
#include <condition_variable>
#include "util/scoped_ptr_vector.h"
#include "ast/ast_util.h"
#include "ast/ast_translation.h"
#include "solver/solver.h"
#include "solver/solver2tactic.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/portfolio/fd_solver.h"
#include "tactic/smtlogics/parallel_params.hpp"
#include "smt/tactic/smt_tactic.h"
#include "smt/smt_solver.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "sat/tactic/sat_tactic.h"

class parallel_tactic : public tactic {


    class solver_state; 

    class task_queue {
        std::mutex                   m_mutex;
        std::condition_variable      m_cond;
        ptr_vector<solver_state>     m_tasks;
        ptr_vector<solver_state>     m_active;
        unsigned                     m_num_waiters;
        volatile bool                m_shutdown;

        void inc_wait() {
            std::lock_guard<std::mutex> lock(m_mutex);
            ++m_num_waiters;
        }

        void dec_wait() {
            std::lock_guard<std::mutex> lock(m_mutex);
            --m_num_waiters;
        }

        solver_state* try_get_task() {
            solver_state* st = nullptr;
            std::lock_guard<std::mutex> lock(m_mutex);
            if (!m_tasks.empty()) {
                st = m_tasks.back();
                m_tasks.pop_back();
                m_active.push_back(st);
            }
            return st;
        }

    public:

        task_queue(): 
            m_num_waiters(0), 
            m_shutdown(false) {}             

        ~task_queue() { reset(); }

        void shutdown() {
            if (!m_shutdown) {
                m_shutdown = true;
                m_cond.notify_all();
                std::lock_guard<std::mutex> lock(m_mutex);
                for (solver_state* st : m_active) {
                    st->m().limit().cancel();
                }
            }
        }

        void add_task(solver_state* task) {
            std::lock_guard<std::mutex> lock(m_mutex);
            m_tasks.push_back(task);
            if (m_num_waiters > 0) {
                m_cond.notify_one();
            }            
        } 

        bool is_idle() {
            std::lock_guard<std::mutex> lock(m_mutex);
            return m_tasks.empty() && m_num_waiters > 0;
        }

        solver_state* get_task() { 
            while (!m_shutdown) {
                inc_wait();
                solver_state* st = try_get_task();
                if (st) {
                    dec_wait();
                    return st;
                }
                {
                    std::unique_lock<std::mutex> lock(m_mutex);
                    m_cond.wait(lock);
                }
                dec_wait();
            }
            return nullptr;
        }

        void task_done(solver_state* st) {
            std::lock_guard<std::mutex> lock(m_mutex);
            m_active.erase(st);
            if (m_tasks.empty() && m_active.empty()) {
                m_shutdown = true;
                m_cond.notify_all();
            }
        }

        void reset() {
            for (auto* t : m_tasks) dealloc(t);
            for (auto* t : m_active) dealloc(t);
            m_tasks.reset();
            m_active.reset();
        }

        std::ostream& display(std::ostream& out) {
            std::lock_guard<std::mutex> lock(m_mutex);
            out << "num_tasks " << m_tasks.size() << " active: " << m_active.size() << "\n";
            for (solver_state* st : m_tasks) {
                st->display(out);
            }
            return out;
        }

    };

    class cube_var {
        expr_ref_vector m_vars;
        expr_ref_vector m_cube;
    public:
        cube_var(expr_ref_vector& c, expr_ref_vector& vs):
            m_vars(vs), m_cube(c) {}

        cube_var operator()(ast_translation& tr) {
            return cube_var(tr(m_cube), tr(m_vars));
        }

        expr_ref_vector const& cube() const { return m_cube; }
        expr_ref_vector const& vars() const { return m_vars; }
    };

    class solver_state {
        scoped_ptr<ast_manager> m_manager;        // ownership handle to ast_manager
        vector<cube_var> m_cubes;                 // set of cubes to process by task
        expr_ref_vector m_asserted_cubes;         // set of cubes asserted on the current solver
        params_ref      m_params;                 // configuration parameters
        ref<solver>     m_solver;                 // solver state
        unsigned        m_depth;                  // number of nested calls to cubing
        double          m_width;                  // estimate of fraction of problem handled by state

    public:
        solver_state(ast_manager* m, solver* s, params_ref const& p): 
            m_manager(m),
            m_asserted_cubes(s->get_manager()),
            m_params(p),
            m_solver(s),
            m_depth(0),
            m_width(1.0)
        {
        }

        ast_manager& m() { return m_solver->get_manager(); }

        solver& get_solver() { return *m_solver; }

        solver* copy_solver() { return m_solver->translate(m_solver->get_manager(), m_params); }

        solver const& get_solver() const { return *m_solver; }

        solver_state* clone() {
            SASSERT(!m_cubes.empty());
            ast_manager& m = m_solver->get_manager();
            ast_manager* new_m = alloc(ast_manager, m, m.proof_mode());
            ast_translation tr(m, *new_m);
            solver* s = m_solver.get()->translate(*new_m, m_params);
            solver_state* st = alloc(solver_state, new_m, s, m_params);
            for (auto & c : m_cubes) st->m_cubes.push_back(c(tr));
            for (expr* c : m_asserted_cubes) st->m_asserted_cubes.push_back(tr(c));
            st->m_depth = m_depth;
            st->m_width = m_width;
            return st;
        }

        vector<cube_var> const& cubes() const { return m_cubes; }

        // remove up to n cubes from list of cubes.
        vector<cube_var> split_cubes(unsigned n) {
            vector<cube_var> result;
            while (n-- > 0 && !m_cubes.empty()) {
                result.push_back(m_cubes.back());
                m_cubes.pop_back();
            }
            return result;
        }

        void set_cubes(vector<cube_var>& c) {
            m_cubes.reset();
            m_cubes.append(c);
        }

        void inc_depth(unsigned inc) { m_depth += inc; }

        void inc_width(unsigned w) { m_width *= w; }
        
        double get_width() const { return m_width; }

        unsigned get_depth() const { return m_depth; }

        lbool simplify() {
            lbool r = l_undef;
            IF_VERBOSE(2, verbose_stream() << "(parallel.tactic simplify-1)\n";);
            set_simplify_params(true);         // retain blocked
            r = get_solver().check_sat(0,0);
            if (r != l_undef) return r;
            IF_VERBOSE(2, verbose_stream() << "(parallel.tactic simplify-2)\n";);
            set_simplify_params(false);        // remove blocked
            r = get_solver().check_sat(0,0);
            return r;            
        }

        void assert_cube(expr_ref_vector const& cube) {
            get_solver().assert_expr(cube);
            m_asserted_cubes.append(cube);
        }

        void set_cube_params() { 
        }
        
        void set_conquer_params() {            
            set_conquer_params(get_solver());
        }

        void set_conquer_params(solver& s) {
            parallel_params pp(m_params);
            params_ref p;
            p.copy(m_params);
            p.set_bool("gc.burst", true);             // apply eager gc
            p.set_uint("simplify.delay", 1000);       // delay simplification by 1000 conflicts
            p.set_bool("lookahead_simplify", false);
            p.set_uint("restart.max", pp.conquer_restart_max());
            p.set_uint("inprocess.max", UINT_MAX);    // base bounds on restart.max
            s.updt_params(p);
        }

        void set_simplify_params(bool retain_blocked) {
            parallel_params pp(m_params);
            params_ref p;
            p.copy(m_params);
            double exp = pp.simplify_exp();
            exp = std::max(exp, 1.0);
            unsigned mult = static_cast<unsigned>(pow(exp, m_depth - 1));
            p.set_uint("inprocess.max", pp.simplify_inprocess_max() * mult);
            p.set_uint("restart.max", pp.simplify_restart_max() * mult);
            p.set_bool("lookahead_simplify", true);
            p.set_bool("retain_blocked_clauses", retain_blocked);
            get_solver().updt_params(p);
        }

        bool canceled() { 
            return m().canceled();
        }

        std::ostream& display(std::ostream& out) {
            out << ":depth " << m_depth << " :width " << m_width << "\n";
            out << ":asserted " << m_asserted_cubes.size() << "\n";
            return out;
        }
    };    

private:

    solver_ref    m_solver;
    ast_manager&  m_manager;
    params_ref    m_params;
    sref_vector<model> m_models;
    unsigned      m_num_threads;    
    statistics    m_stats;
    task_queue    m_queue;
    std::mutex    m_mutex;
    double        m_progress;
    unsigned      m_branches;
    unsigned      m_backtrack_frequency;
    unsigned      m_conquer_delay;
    volatile bool m_has_undef;
    bool          m_allsat;
    unsigned      m_num_unsat;
    int           m_exn_code;
    std::string   m_exn_msg;

    void init() {
        parallel_params pp(m_params);
        m_num_threads = std::min((unsigned)omp_get_num_procs(), pp.threads_max());
        m_progress = 0;
        m_has_undef = false;
        m_allsat = false;
        m_branches = 0;    
        m_num_unsat = 0;    
        m_backtrack_frequency = pp.conquer_backtrack_frequency();
        m_conquer_delay = pp.conquer_delay();
        m_exn_code = 0;
        m_params.set_bool("override_incremental", true);
    }

    void log_branches(lbool status) {
        IF_VERBOSE(0, verbose_stream() << "(tactic.parallel :progress " << m_progress << "% ";
                   if (status == l_true)  verbose_stream() << ":status sat ";
                   if (status == l_undef) verbose_stream() << ":status unknown ";
                   verbose_stream() << ":closed " << m_num_unsat << " :open " << m_branches << ")\n";);
    }

    void add_branches(unsigned b) {
        if (b == 0) return;
        {
            std::lock_guard<std::mutex> lock(m_mutex);
            m_branches += b;
        }
        log_branches(l_false);
    }

    void dec_branch() {
        std::lock_guard<std::mutex> lock(m_mutex);
        --m_branches;
    }

    void close_branch(solver_state& s, lbool status) {
        double f = 100.0 / s.get_width();
        {
            std::lock_guard<std::mutex> lock(m_mutex);
            m_progress += f;
            --m_branches;
        }
        log_branches(status);
    }

    void report_sat(solver_state& s) {
        close_branch(s, l_true);
        model_ref mdl;
        s.get_solver().get_model(mdl);
        if (mdl) {
            std::lock_guard<std::mutex> lock(m_mutex);
            if (&s.m() != &m_manager) {
                ast_translation tr(s.m(), m_manager);
                mdl = mdl->translate(tr);
            }
            m_models.push_back(mdl.get());
        }
        if (!m_allsat) {
            m_queue.shutdown();
        }
    }

    void inc_unsat() {
        std::lock_guard<std::mutex> lock(m_mutex);
        ++m_num_unsat;
    }

    void report_unsat(solver_state& s) {        
        inc_unsat();
        close_branch(s, l_false);
    }
        
    void report_undef(solver_state& s) {
        m_has_undef = true;
        close_branch(s, l_undef);
    }

    void cube_and_conquer(solver_state& s) {
        ast_manager& m = s.m();
        vector<cube_var> cube, hard_cubes, cubes;
        expr_ref_vector vars(m);

    cube_again:
        // extract up to one cube and add it.
        cube.reset();
        cube.append(s.split_cubes(1));
        SASSERT(cube.size() <= 1);
        IF_VERBOSE(2, verbose_stream() << "(tactic.parallel :split-cube " << cube.size() << ")\n";);
        if (!s.cubes().empty()) m_queue.add_task(s.clone());
        if (!cube.empty()) {
            s.assert_cube(cube.get(0).cube());
            vars.reset();
            vars.append(cube.get(0).vars());
        }

    simplify_again:
        s.inc_depth(1);
        // simplify
        if (canceled(s)) return;
        switch (s.simplify()) {
        case l_undef: break;
        case l_true:  report_sat(s); return;
        case l_false: report_unsat(s); return;                
        }
        if (canceled(s)) return;
        
        if (memory_pressure()) {
            goto simplify_again;
        }
        // extract cubes.
        cubes.reset();
        s.set_cube_params();
        solver_ref conquer;
        
        unsigned cutoff = UINT_MAX;
        bool first = true;
        unsigned num_backtracks = 0, width = 0;
        while (cutoff > 0 && !canceled(s)) {
            expr_ref_vector c = s.get_solver().cube(vars, cutoff);
            if (c.empty()) {
                goto simplify_again;
            }
            if (m.is_false(c.back())) {                
                break;
            }
            lbool is_sat = l_undef;
            if (width >= m_conquer_delay && !conquer) {
                conquer = s.copy_solver();
                s.set_conquer_params(*conquer.get());
            }
            if (conquer) {
                is_sat = conquer->check_sat(c);
            }
            switch (is_sat) {
            case l_false: 
                cutoff = c.size();
                backtrack(*conquer.get(), c, (num_backtracks++) % m_backtrack_frequency == 0);
                if (cutoff != c.size()) {
                    IF_VERBOSE(0, verbose_stream() << "(tactic.parallel :backtrack " << cutoff << " -> " << c.size() << ")\n");
                    cutoff = c.size();
                }
                inc_unsat();
                log_branches(l_false);
                break;

            case l_true:
                report_sat(s);
                if (conquer) {
                    collect_statistics(*conquer.get());
                }
                return;

            case l_undef:
                ++width;
                IF_VERBOSE(2, verbose_stream() << "(tactic.parallel :cube " << c.size() << " :vars " << vars.size() << ")\n"); 
                cubes.push_back(cube_var(c, vars));
                cutoff = UINT_MAX;
                break;

            }
            if (cubes.size() >= conquer_batch_size() || (!cubes.empty() && m_queue.is_idle())) {
                spawn_cubes(s, std::max(2u, width), cubes);
                first = false;
                cubes.reset();
            }
        }

        if (conquer) {
            collect_statistics(*conquer.get());
        }

        if (cubes.empty() && first) {
            report_unsat(s);
        }
        else if (cubes.empty()) {
            dec_branch();
        }
        else {
            s.inc_width(width);
            add_branches(cubes.size()-1);
            s.set_cubes(cubes);
            goto cube_again;
        }                
    }

    void spawn_cubes(solver_state& s, unsigned width, vector<cube_var>& cubes) {
        if (cubes.empty()) return;
        add_branches(cubes.size());
        s.set_cubes(cubes);
        solver_state* s1 = s.clone();
        s1->inc_width(width);
        m_queue.add_task(s1);
    }

    /*
     * \brief backtrack from unsatisfiable core
     */
    void backtrack(solver& s, expr_ref_vector& asms, bool full) {
        ast_manager& m = s.get_manager();
        expr_ref_vector core(m);
        obj_hashtable<expr> hcore;
        s.get_unsat_core(core);
        while (!asms.empty() && !core.contains(asms.back())) asms.pop_back();
        if (!full) return;

        //s.assert_expr(m.mk_not(mk_and(core)));
        if (!asms.empty()) {
            expr* last = asms.back();
            expr_ref not_last(mk_not(m, last), m);
            asms.pop_back();
            asms.push_back(not_last);
            lbool r = s.check_sat(asms);
            asms.pop_back();
            if (r != l_false) {
                asms.push_back(last);
                return;
            }
            core.reset();
            s.get_unsat_core(core);
            if (core.contains(not_last)) {
                //s.assert_expr(m.mk_not(mk_and(core)));
                r = s.check_sat(asms);
            }
            if (r == l_false) {
                backtrack(s, asms, full);
            }            
        }        
    }

    bool canceled(solver_state& s) {
        if (s.canceled()) {
            m_has_undef = true;
            return true;
        }
        else {
            return false;
        }        
    }

    bool memory_pressure() { 
        return memory::above_high_watermark();
    }

    void run_solver() {
        try {
            while (solver_state* st = m_queue.get_task()) {
                cube_and_conquer(*st);
                collect_statistics(*st);
                m_queue.task_done(st);
                if (st->m().canceled()) m_queue.shutdown();
                IF_VERBOSE(1, display(verbose_stream()););
                dealloc(st);
            }
        }
        catch (z3_exception& ex) {            
            IF_VERBOSE(1, verbose_stream() << ex.msg() << "\n";);
            m_queue.shutdown();
            std::lock_guard<std::mutex> lock(m_mutex);
            if (ex.has_error_code()) {
                m_exn_code = ex.error_code();
            }
            else {
                m_exn_msg = ex.msg();
                m_exn_code = -1;
            }
        }
    }

    void collect_statistics(solver_state& s) {
        collect_statistics(s.get_solver());
    }

    void collect_statistics(solver& s) {
        std::lock_guard<std::mutex> lock(m_mutex);
        s.collect_statistics(m_stats);
    }

    lbool solve(model_ref& mdl) {        
        add_branches(1);
        vector<std::thread> threads;
        for (unsigned i = 0; i < m_num_threads; ++i) 
            threads.push_back(std::thread([this]() { run_solver(); }));
        for (std::thread& t : threads) 
            t.join();
        m_manager.limit().reset_cancel();
        if (m_exn_code == -1) 
            throw default_exception(m_exn_msg);
        if (m_exn_code != 0) 
            throw z3_error(m_exn_code);            
        if (!m_models.empty()) {
            mdl = m_models.back();            
            return l_true;
        }
        if (m_has_undef) 
            return l_undef;
        return l_false;
    }

    std::ostream& display(std::ostream& out) {
        unsigned n_models, n_unsat;
        double n_progress;
        {
            std::lock_guard<std::mutex> lock(m_mutex);
            n_models   = m_models.size();
            n_unsat    = m_num_unsat;
            n_progress = m_progress;
        }
        m_stats.display(out);
        m_queue.display(out);
        out << "(tactic.parallel :unsat " << n_unsat << " :progress " << n_progress << "% :models " << n_models << ")\n";
        return out;
    }

public:

    parallel_tactic(solver* s, params_ref const& p) :
        m_solver(s),
        m_manager(s->get_manager()),        
        m_params(p) {
        init();
    }

    void operator ()(const goal_ref & g,goal_ref_buffer & result) {
        ast_manager& m = g->m();
        solver* s = m_solver->translate(m, m_params);
        solver_state* st = alloc(solver_state, 0, s, m_params);
        m_queue.add_task(st);
        expr_ref_vector clauses(m);
        ptr_vector<expr> assumptions;
        obj_map<expr, expr*> bool2dep;
        ref<generic_model_converter> fmc;
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
                g->add(concat(fmc.get(), model2model_converter(mdl.get())));
            }
            g->reset();
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
            break;
        }
        result.push_back(g.get());
    }

    unsigned conquer_batch_size() const {
        parallel_params pp(m_params);
        return pp.conquer_batch_size();
    }

    void cleanup() {
        m_queue.reset();
    }

    tactic* translate(ast_manager& m) {
        solver* s = m_solver->translate(m, m_params);
        return alloc(parallel_tactic, s, m_params);
    }

    virtual void updt_params(params_ref const & p) {
        m_params.copy(p);
        parallel_params pp(p);
        m_conquer_delay = pp.conquer_delay();
    }

    virtual void collect_statistics(statistics & st) const {
        st.copy(m_stats);
        st.update("par unsat", m_num_unsat);
        st.update("par models", m_models.size());
        st.update("par progress", m_progress);
    }

    virtual void reset_statistics() {
        m_stats.reset();
    }
};



tactic * mk_parallel_qffd_tactic(ast_manager& m, params_ref const& p) {
    solver* s = mk_fd_solver(m, p);
    return alloc(parallel_tactic, s, p);
}

tactic * mk_parallel_tactic(solver* s, params_ref const& p) {
    return alloc(parallel_tactic, s, p);
}


tactic * mk_psat_tactic(ast_manager& m, params_ref const& p) {
    parallel_params pp(p);
    bool use_parallel = pp.enable();
    return pp.enable() ? mk_parallel_tactic(mk_inc_sat_solver(m, p), p) : mk_sat_tactic(m);
}

tactic * mk_psmt_tactic(ast_manager& m, params_ref const& p, symbol const& logic) {
    parallel_params pp(p);
    bool use_parallel = pp.enable();
    return pp.enable() ? mk_parallel_tactic(mk_smt_solver(m, p, logic), p) : mk_smt_tactic(p);
}

tactic * mk_psmt_tactic_using(ast_manager& m, bool auto_config, params_ref const& _p, symbol const& logic) {
    parallel_params pp(_p);
    bool use_parallel = pp.enable();
    params_ref p = _p;
    p.set_bool("auto_config", auto_config);
    return using_params(pp.enable() ? mk_parallel_tactic(mk_smt_solver(m, p, logic), p) : mk_smt_tactic(p), p);
}

tactic * mk_parallel_smt_tactic(ast_manager& m, params_ref const& p) {
    return mk_parallel_tactic(mk_smt_solver(m, p, symbol::null), p);
}
