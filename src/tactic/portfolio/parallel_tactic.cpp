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
 
 If in the cube state, the solver performs the following:
  1. Clone the state with the remaining cubes if there is more than one cube. Re-enqueue the remaining cubes.
  2. Apply simplifications and pre-processing according to configuration.
  3. Cube using the parameter settings prescribed in m_params.
  4. Create a conquer state with the produced cubes.
 If in the conquer state, the solver performs the following
  1. Pass the cubes as assumptions and solve each sub-cube with a prescribed resource bound.
  2. Assemble cubes that could not be solved and create a cube state.
 

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
#include "tactic/portfolio/fd_solver.h"
#include "tactic/smtlogics/parallel_params.hpp"

class parallel_tactic : public tactic {


    enum task_type { cube_task, conquer_task };

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
        expr_ref        m_cube;
    public:
        cube_var(expr* c, expr_ref_vector& vs):
            m_vars(vs), m_cube(c, vs.get_manager()) {}

        cube_var operator()(ast_translation& tr) {
            expr_ref_vector vars(tr.to());
            for (expr* v : m_vars) vars.push_back(tr(v));
            return cube_var(tr(m_cube.get()), vars);
        }

        expr* cube() const { return m_cube; }
        expr_ref_vector const& vars() { return m_vars; }
    };

    class solver_state {
        task_type       m_type;                   // current work role of the task
        scoped_ptr<ast_manager> m_manager;        // ownership handle to ast_manager
        vector<cube_var> m_cubes;                // set of cubes to process by task
        expr_ref_vector m_asserted_cubes;         // set of cubes asserted on the current solver
        params_ref      m_params;                 // configuration parameters
        ref<solver>     m_solver;                 // solver state
        unsigned        m_depth;                  // number of nested calls to cubing
        double          m_width;                  // estimate of fraction of problem handled by state
        unsigned        m_restart_max;            // saved configuration value

        expr_ref_vector cube_literals(expr* cube) {
            expr_ref_vector literals(m());
            if (m().is_and(cube)) {
                literals.append(to_app(cube)->get_num_args(), to_app(cube)->get_args());
            }
            else {
                literals.push_back(cube);
            }
            return literals;
        }

    public:
        solver_state(ast_manager* m, solver* s, params_ref const& p, task_type t): 
            m_type(t),
            m_manager(m),
            m_asserted_cubes(s->get_manager()),
            m_params(p),
            m_solver(s),
            m_depth(0),
            m_width(1.0)
        {
            parallel_params pp(p);
            m_restart_max = pp.restart_max();
        }

        ast_manager& m() { return m_solver->get_manager(); }

        solver& get_solver() { return *m_solver; }

        solver const& get_solver() const { return *m_solver; }

        solver_state* clone() {
            SASSERT(!m_cubes.empty());
            ast_manager& m = m_solver->get_manager();
            ast_manager* new_m = alloc(ast_manager, m, !m.proof_mode());
            ast_translation tr(m, *new_m);
            solver* s = m_solver->translate(*new_m, m_params);
            solver_state* st = alloc(solver_state, new_m, s, m_params, m_type);
            for (auto & c : m_cubes) st->m_cubes.push_back(c(tr));
            for (expr* c : m_asserted_cubes) st->m_asserted_cubes.push_back(tr(c));
            st->m_depth = m_depth;
            st->m_width = m_width;
            return st;
        }

        task_type type() const { return m_type; }

        void set_type(task_type t) { m_type = t; }

        vector<cube_var> const& cubes() const { SASSERT(m_type == conquer_task); return m_cubes; }

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

        void inc_width(unsigned w) { 
            m_width *= w;  
        }
        
        double get_width() const { return m_width; }

        unsigned get_depth() const { return m_depth; }

        lbool simplify() {
            lbool r = l_undef;
            if (m_depth == 1) {
                IF_VERBOSE(2, verbose_stream() << "(parallel.tactic simplify-1)\n";);
                set_simplify_params(true, true);         // retain PB, retain blocked
                r = get_solver().check_sat(0,0);
                if (r != l_undef) return r;
                
                // copy over the resulting clauses with a configuration that blasts PB constraints
                set_simplify_params(false, true);
                expr_ref_vector fmls(m());
                get_solver().get_assertions(fmls);
                model_converter_ref mc = get_solver().get_model_converter();
                m_solver = mk_fd_solver(m(), m_params);
                m_solver->set_model_converter(mc.get());
                m_solver->assert_expr(fmls);
            }
            IF_VERBOSE(2, verbose_stream() << "(parallel.tactic simplify-2)\n";);
            set_simplify_params(false, true);         // remove PB, retain blocked
            r = get_solver().check_sat(0,0);
            if (r != l_undef) return r;
            IF_VERBOSE(2, verbose_stream() << "(parallel.tactic simplify-3)\n";);
            set_simplify_params(false, false);        // remove any PB, remove blocked
            r = get_solver().check_sat(0,0);
            return r;            
        }

        void assert_cube(expr* cube) {
            get_solver().assert_expr(cube);
            m_asserted_cubes.append(cube_literals(cube));            
        }

        lbool solve(expr* cube) {
            set_conquer_params();
            expr_ref_vector literals = cube_literals(cube);
            return get_solver().check_sat(literals);
        }        

        void set_cube_params() {
            // get_solver().updt_params(m_params);
        }
        
        void set_conquer_params() {            
            m_params.set_bool("gc.initial", true);
            m_params.set_bool("lookahead_simplify", false);
            m_params.set_uint("restart.max", m_restart_max);
            get_solver().updt_params(m_params);
        }

        void set_simplify_params(bool pb_simp, bool retain_blocked) {
            parallel_params pp(m_params);
            m_params.set_bool("cardinality.solver", pb_simp);
            m_params.set_sym ("pb.solver", pb_simp ? symbol("solver") : symbol("circuit"));
            if (m_params.get_uint("inprocess.max", UINT_MAX) == UINT_MAX) 
                m_params.set_uint("inprocess.max", pp.inprocess_max());
            m_params.set_bool("lookahead_simplify", true);
            m_params.set_uint("restart.max", UINT_MAX);
            m_params.set_bool("retain_blocked_clauses", retain_blocked);
            get_solver().updt_params(m_params);
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

    ast_manager& m_manager;
    params_ref   m_params;
    sref_vector<model> m_models;
    unsigned     m_num_threads;    
    statistics   m_stats;
    task_queue   m_queue;
    std::mutex   m_mutex;
    double       m_progress;
    unsigned     m_branches;
    bool         m_has_undef;
    bool         m_allsat;
    unsigned     m_num_unsat;
    int          m_exn_code;
    std::string  m_exn_msg;

    void init() {
        m_num_threads = omp_get_num_procs();  // TBD adjust by possible threads used inside each solver.
        m_progress = 0;
        m_has_undef = false;
        m_allsat = false;
        m_num_unsat = 0;
        m_branches = 0;
        m_exn_code = 0;
        m_params.set_bool("override_incremental", true);
    }

    void add_branches(unsigned b) {
        std::lock_guard<std::mutex> lock(m_mutex);
        m_branches += b;
    }

    void close_branch(solver_state& s, lbool status) {
        double f = 100.0 / s.get_width();
        {
            std::lock_guard<std::mutex> lock(m_mutex);
            m_progress += f;
            --m_branches;
        }
        IF_VERBOSE(0, verbose_stream() << "(tactic.parallel :progress " << m_progress << "% ";
                   if (status == l_true)  verbose_stream() << ":status sat ";
                   if (status == l_undef) verbose_stream() << ":status unknown ";
                   verbose_stream() << ":unsat " << m_num_unsat << " :open-branches " << m_branches << ")\n";);
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

    void report_unsat(solver_state& s) {        
        {
            std::lock_guard<std::mutex> lock(m_mutex);
            ++m_num_unsat;
        }
        close_branch(s, l_false);
    }
        
    void report_undef(solver_state& s) {
        m_has_undef = true;
        close_branch(s, l_undef);
    }

    void cube_and_conquer(solver_state& s) {
        ast_manager& m = s.m();
        // expr_ref_vector cube(m), hard_cubes(m);
        vector<cube_var> cube, hard_cubes, cubes;
        expr_ref_vector vars(m);

        add_branches(1);

        switch (s.type()) {
        case cube_task: goto cube;
        case conquer_task: goto conquer;
        }

    cube:
        SASSERT(s.type() == cube_task);

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
        s.inc_depth(1);

        // simplify
        switch (s.simplify()) {
        case l_undef: break;
        case l_true:  report_sat(s); return;
        case l_false: report_unsat(s); return;                
        }
        if (canceled(s)) return;
        
        // extract cubes.
        cubes.reset();
        s.set_cube_params();
        while (true) {
            expr_ref_vector c = s.get_solver().cube(vars, UINT_MAX); // TBD tune this
            if (c.empty()) {
                report_undef(s);
                return;
            }
            if (m.is_false(c.back())) {                
                break;
            }
            cubes.push_back(cube_var(mk_and(c), vars));
            IF_VERBOSE(2, verbose_stream() << "(tactic.parallel :cube " << cubes.size() << " :vars " << vars.size() << ")\n"); 
        }

        IF_VERBOSE(1, verbose_stream() << "(tactic.parallel :cubes " << cubes.size() << ")\n";);

        if (cubes.empty()) {
            report_unsat(s);
            return;
        }
        else {
            s.inc_width(cubes.size());
            add_branches(cubes.size() - 1);
            s.set_cubes(cubes);
            s.set_type(conquer_task);            
            goto conquer;
        }

    conquer:        
        SASSERT(s.type() == conquer_task);

        // extract a batch of cubes
        cubes.reset();
        cubes.append(s.split_cubes(conquer_batch_size()));
        if (!s.cubes().empty()) m_queue.add_task(s.clone());

        s.set_conquer_params();
        hard_cubes.reset();
        for (cube_var& cv : cubes) {
            switch (s.solve(cv.cube())) {
            case l_undef: hard_cubes.push_back(cv); break;
            case l_true:  report_sat(s); break;
            case l_false: report_unsat(s); break;                
            }
            if (canceled(s)) return;
        }
        IF_VERBOSE(1, verbose_stream() << "(tactic.parallel :cubes " << cubes.size() << " :hard-cubes " << hard_cubes.size() << ")\n";);
        if (hard_cubes.empty()) return;

        s.set_cubes(hard_cubes);
        s.set_type(cube_task);
        goto cube;        
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
        std::lock_guard<std::mutex> lock(m_mutex);
        s.get_solver().collect_statistics(m_stats);
    }

    lbool solve(model_ref& mdl) {        
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
        m_stats.display(out);
        m_queue.display(out);
        std::lock_guard<std::mutex> lock(m_mutex);
        out << "(tactic.parallel :unsat " << m_num_unsat << " :progress " << m_progress << "% :models " << m_models.size() << ")\n";
        return out;
    }

public:

    parallel_tactic(ast_manager& m, params_ref const& p) :
        m_manager(m),
        m_params(p) {
        init();        
    }

    void operator ()(const goal_ref & g,goal_ref_buffer & result) {
        ast_manager& m = g->m();
        solver* s = mk_fd_solver(m, m_params);
        solver_state* st = alloc(solver_state, 0, s, m_params, cube_task);
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

    virtual void collect_param_descrs(param_descrs & r) {
        r.insert("conquer_batch_size", CPK_UINT, "(default: 1000) batch size of cubes to conquer");
    }

    unsigned conquer_batch_size() const {
        parallel_params pp(m_params);
        return pp.conquer_batch_size();
    }

    void cleanup() {
        m_queue.reset();
        init();
    }

    tactic* translate(ast_manager& m) {
        return alloc(parallel_tactic, m, m_params);
    }

    virtual void updt_params(params_ref const & p) {
        m_params.copy(p);
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



tactic * mk_parallel_tactic(ast_manager& m, params_ref const& p) {
    return alloc(parallel_tactic, m, p);
}

