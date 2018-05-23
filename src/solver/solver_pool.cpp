/**
Copyright (c) 2017 Microsoft Corporation

Module Name:

    solver_pool.cpp

Abstract:

   Maintain a pool of solvers

Author:

    Nikolaj Bjorner

Notes:

--*/

#include "solver/solver_pool.h"
#include "solver/solver_na2as.h"
#include "ast/proofs/proof_utils.h"
#include "ast/ast_util.h"

class pool_solver : public solver_na2as {
    solver_pool&       m_pool;
    app_ref            m_pred;
    proof_ref          m_proof;
    ref<solver>        m_base;
    expr_ref_vector    m_assertions;
    unsigned           m_head;
    expr_ref_vector    m_flat;
    bool               m_pushed;
    bool               m_in_delayed_scope;
    unsigned           m_dump_counter;

    bool is_virtual() const { return !m.is_true(m_pred); }
public:
    pool_solver(solver* b, solver_pool& pool, app_ref& pred):
        solver_na2as(pred.get_manager()),
        m_pool(pool),
        m_pred(pred),
        m_proof(m),
        m_base(b),
        m_assertions(m),
        m_head(0),
        m_flat(m),
        m_pushed(false),
        m_in_delayed_scope(false),
        m_dump_counter(0) {
        if (is_virtual()) {
            solver_na2as::assert_expr_core2(m.mk_true(), pred);
        }
    }

    ~pool_solver() override {
        if (m_pushed) pop(get_scope_level());
        if (is_virtual()) {
            m_pred = m.mk_not(m_pred);
            m_base->assert_expr(m_pred);
        }
    }

    solver* base_solver() { return m_base.get(); }

    solver* translate(ast_manager& m, params_ref const& p) override { UNREACHABLE(); return nullptr; }
    void updt_params(params_ref const& p) override { solver::updt_params(p); m_base->updt_params(p); }
    void collect_param_descrs(param_descrs & r) override { m_base->collect_param_descrs(r); }
    void collect_statistics(statistics & st) const override { m_base->collect_statistics(st); }

    void get_unsat_core(ptr_vector<expr> & r) override {
        m_base->get_unsat_core(r);
        unsigned j = 0;
        for (unsigned i = 0; i < r.size(); ++i) 
            if (m_pred != r[i]) 
                r[j++] = r[i];
        r.shrink(j);
    }

    unsigned get_num_assumptions() const override {
        unsigned sz = solver_na2as::get_num_assumptions();
        return is_virtual() ? sz - 1 : sz;
    }

    proof * get_proof() override {
        scoped_watch _t_(m_pool.m_proof_watch);
        if (!m_proof.get()) {
            elim_aux_assertions pc(m_pred);
            m_proof = m_base->get_proof();
            pc(m, m_proof, m_proof);
        }
        return m_proof;
    }

    void internalize_assertions() {
        SASSERT(!m_pushed || m_head == m_assertions.size());
        for (unsigned sz = m_assertions.size(); m_head < sz; ++m_head) {
            expr_ref f(m);
            f = m.mk_implies(m_pred, (m_assertions.get(m_head)));
            m_base->assert_expr(f);
        }
    }

    lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) override {
        SASSERT(!m_pushed || get_scope_level() > 0);
        m_proof.reset();
        scoped_watch _t_(m_pool.m_check_watch);
        m_pool.m_stats.m_num_checks++;

        stopwatch sw;
        sw.start();
        internalize_assertions();
        lbool res = m_base->check_sat(num_assumptions, assumptions);
        sw.stop();
        switch (res) {
        case l_true:
            m_pool.m_check_sat_watch.add(sw);
            m_pool.m_stats.m_num_sat_checks++;
            break;
        case l_undef:
            m_pool.m_check_undef_watch.add(sw);
            m_pool.m_stats.m_num_undef_checks++;
            break;
        default:
            break;
        }
        set_status(res);
        
        if (false /*m_dump_benchmarks && sw.get_seconds() >= m_pool.fparams().m_dump_min_time*/) {
            std::stringstream file_name;
            file_name << "virt_solver";
            if (is_virtual()) { file_name << "_" << m_pred->get_decl()->get_name(); }
            file_name << "_" << (m_dump_counter++) << ".smt2";
            
            std::ofstream out(file_name.str().c_str());
            if (!out) { verbose_stream() << "could not open file " << file_name.str() << " for output\n"; }
            
            out << "(set-info :status ";
            switch (res) {
            case l_true: out << "sat"; break;
            case l_false: out << "unsat"; break;
            case l_undef: out << "unknown"; break;
            }
            out << ")\n";            
            m_base->display(out, num_assumptions, assumptions);
            out << "(check-sat";
            for (unsigned i = 0; i < num_assumptions; ++i) {
                out << " " << mk_pp(assumptions[i], m);
            }
            out << ")";            
            out << "(exit)\n";
            ::statistics st;
            m_base->collect_statistics(st);
            st.update("time", sw.get_seconds());
            st.display_smt2(out);            
            out.close();
        }
        return res;
    }

    void push_core() override {
        SASSERT(!m_pushed || get_scope_level() > 0);
        if (m_in_delayed_scope) {
            // second push
            internalize_assertions();
            m_base->push();
            m_pushed = true;
            m_in_delayed_scope = false;
        }
        
        if (!m_pushed) { 
            m_in_delayed_scope = true; 
        }
        else {
            SASSERT(m_pushed);
            SASSERT(!m_in_delayed_scope);
            m_base->push();
        }
    }

    void pop_core(unsigned n) override {
        SASSERT(!m_pushed || get_scope_level() > 0);
        if (m_pushed) {
            SASSERT(!m_in_delayed_scope);
            m_base->pop(n);
            m_pushed = get_scope_level() - n > 0;
        } 
        else { 
            m_in_delayed_scope = get_scope_level() - n > 0; 
        }
    }
    
    void assert_expr_core(expr * e) override {
        SASSERT(!m_pushed || get_scope_level() > 0);
        if (m.is_true(e)) return; 
        if (m_in_delayed_scope) {
            internalize_assertions();
            m_base->push();
            m_pushed = true;
            m_in_delayed_scope = false;
        }
        
        if (m_pushed) {
            m_base->assert_expr(e); 
        }
        else {
            m_flat.push_back(e);
            flatten_and(m_flat);
            m_assertions.append(m_flat);
            m_flat.reset();
        }
    }   

    void get_model_core(model_ref & _m) override { m_base->get_model_core(_m); }

    expr * get_assumption(unsigned idx) const override {
        return solver_na2as::get_assumption(idx + is_virtual());
    }

    std::string reason_unknown() const override { return m_base->reason_unknown(); }
    void set_reason_unknown(char const* msg) override { return m_base->set_reason_unknown(msg); }
    void get_labels(svector<symbol> & r) override { return m_base->get_labels(r); }
    void set_progress_callback(progress_callback * callback) override { m_base->set_progress_callback(callback); }

    expr_ref_vector cube(expr_ref_vector& vars, unsigned ) override { return expr_ref_vector(m); }
    
    ast_manager& get_manager() const override { return m_base->get_manager(); }

    void refresh(solver* new_base) {
        SASSERT(!m_pushed);
        m_head = 0;
        m_base = new_base;
    }

    void reset() {
        SASSERT(!m_pushed);
        m_head = 0;
        m_assertions.reset();
        m_pool.refresh(m_base.get());
    }
};

solver_pool::solver_pool(solver* base_solver, unsigned num_solvers_per_pool):
    m_base_solver(base_solver),
    m_num_solvers_per_pool(num_solvers_per_pool),
    m_num_solvers_in_last_pool(0)
{}


ptr_vector<solver> solver_pool::get_base_solvers() const {
    ptr_vector<solver> solvers;
    for (solver* s0 : m_solvers) {
        pool_solver* s = dynamic_cast<pool_solver*>(s0);
        if (!solvers.contains(s->base_solver())) {
            solvers.push_back(s->base_solver());
        }
    }
    return solvers;
}

void solver_pool::collect_statistics(statistics &st) const {
    ptr_vector<solver> solvers = get_base_solvers();
    for (solver* s : solvers) s->collect_statistics(st);        
    st.update("time.pool_solver.smt.total", m_check_watch.get_seconds());
    st.update("time.pool_solver.smt.total.sat", m_check_sat_watch.get_seconds());
    st.update("time.pool_solver.smt.total.undef", m_check_undef_watch.get_seconds());
    st.update("time.pool_solver.proof", m_proof_watch.get_seconds());
    st.update("pool_solver.checks", m_stats.m_num_checks);
    st.update("pool_solver.checks.sat", m_stats.m_num_sat_checks);
    st.update("pool_solver.checks.undef", m_stats.m_num_undef_checks);
}

void solver_pool::reset_statistics() {
#if 0
    ptr_vector<solver> solvers = get_base_solvers();
    for (solver* s : solvers) {
        s->reset_statistics();    
    }
#endif
    m_stats.reset();
    m_check_sat_watch.reset();
    m_check_undef_watch.reset();
    m_check_watch.reset();
    m_proof_watch.reset();
}

solver* solver_pool::mk_solver() {
    ref<solver> base_solver;
    ast_manager& m = m_base_solver->get_manager();
    if (m_solvers.empty() || m_num_solvers_in_last_pool == m_num_solvers_per_pool) {
        base_solver = m_base_solver->translate(m, m_base_solver->get_params());
        m_num_solvers_in_last_pool = 0;
    }
    else {
        base_solver = dynamic_cast<pool_solver*>(m_solvers.back())->base_solver();
    }
    m_num_solvers_in_last_pool++;
    std::stringstream name;
    name << "vsolver#" << m_solvers.size();
    app_ref pred(m.mk_const(symbol(name.str().c_str()), m.mk_bool_sort()), m);
    pool_solver* solver = alloc(pool_solver, base_solver.get(), *this, pred);
    m_solvers.push_back(solver);
    return solver;
}

void solver_pool::reset_solver(solver* s) {
    pool_solver* ps = dynamic_cast<pool_solver*>(s);
    SASSERT(ps);
    if (ps) ps->reset();    
}

void solver_pool::refresh(solver* base_solver) {
    ast_manager& m = m_base_solver->get_manager();
    ref<solver> new_base = m_base_solver->translate(m, m_base_solver->get_params());
    for (solver* s0 : m_solvers) {
        pool_solver* s = dynamic_cast<pool_solver*>(s0);
        if (base_solver == s->base_solver()) {
            s->refresh(new_base.get());
        }
    }
}
