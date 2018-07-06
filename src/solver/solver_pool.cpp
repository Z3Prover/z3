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
    bool               m_dump_benchmarks;
    double             m_dump_threshold;
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
        m_dump_benchmarks(false),
        m_dump_threshold(5.0),
        m_dump_counter(0) {
        if (is_virtual()) {
            solver_na2as::assert_expr_core2(m.mk_true(), pred);
        }
        updt_params(m_base->get_params());
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
    void updt_params(params_ref const& p) override {
        solver::updt_params(p); m_base->updt_params(p);
        m_dump_benchmarks = solver::get_params().get_bool("dump_benchmarks", false);
        m_dump_threshold = solver::get_params().get_double("dump_threshold", 5.0);
    }
    void push_params() override {m_base->push_params();}
    void pop_params() override {m_base->pop_params();}

    void collect_param_descrs(param_descrs & r) override { m_base->collect_param_descrs(r); }
    void collect_statistics(statistics & st) const override { m_base->collect_statistics(st); }
    unsigned get_num_assertions() const override { return m_base->get_num_assertions(); }
    expr * get_assertion(unsigned idx) const override { return m_base->get_assertion(idx); }

    void get_unsat_core(expr_ref_vector& r) override {
        m_base->get_unsat_core(r);
        unsigned j = 0;
        for (unsigned i = 0; i < r.size(); ++i)
            if (m_pred != r.get(i))
                r[j++] = r.get(i);
        r.shrink(j);
    }

    unsigned get_num_assumptions() const override {
        unsigned sz = solver_na2as::get_num_assumptions();
        return is_virtual() ? sz - 1 : sz;
    }


    proof * get_proof() override {
        scoped_watch _t_(m_pool.m_proof_watch);
        if (!m_proof.get()) {
            m_proof = m_base->get_proof();
            if (m_proof) {
                elim_aux_assertions pc(m_pred);
                pc(m, m_proof, m_proof);
            }
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

        if (m_dump_benchmarks && sw.get_seconds() >= m_dump_threshold) {
            expr_ref_vector cube(m, num_assumptions, assumptions);
            vector<expr_ref_vector> clauses;
            dump_benchmark(cube, clauses, res, sw.get_seconds());
        }
        return res;
    }

    lbool check_sat_cc_core(expr_ref_vector const & cube,
                            vector<expr_ref_vector> const & clauses) override {
        SASSERT(!m_pushed || get_scope_level() > 0);
        m_proof.reset();
        scoped_watch _t_(m_pool.m_check_watch);
        m_pool.m_stats.m_num_checks++;

        stopwatch sw;
        sw.start();
        internalize_assertions();
        lbool res = m_base->check_sat_cc(cube, clauses);
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

        if (m_dump_benchmarks && sw.get_seconds() >= m_dump_threshold) {
            dump_benchmark(cube, clauses, res, sw.get_seconds());
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
            SASSERT(!m_in_delayed_scope);
            m_base->push();
        }
    }

    void pop_core(unsigned n) override {
        unsigned lvl = get_scope_level();
        SASSERT(!m_pushed || lvl > 0);
        if (m_pushed) {
            SASSERT(!m_in_delayed_scope);
            m_base->pop(n);
            m_pushed = lvl - n > 0;
        }
        else {
            m_in_delayed_scope = lvl - n > 0;
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

private:

    void dump_benchmark(const expr_ref_vector &cube, vector<expr_ref_vector> const & clauses,
                        lbool last_status, double last_time) {
        std::string file_name = mk_file_name();
        std::ofstream out(file_name);
        if (!out) {
            IF_VERBOSE(0, verbose_stream() << "could not open file " << file_name << " for output\n");
            return;
        }

        out << "(set-info :status " << lbool2status(last_status) << ")\n";
        m_base->display(out, cube.size(), cube.c_ptr());
        for (auto const& clause : clauses) {
            out << ";; extra clause\n";
            out << "(assert (or ";
            for (auto *lit : clause) out << mk_pp(lit, m) << " ";
            out << "))\n";
        }

        out << "(check-sat";
        for (auto * lit : cube) out << " " << mk_pp(lit, m);
        out << ")\n";

        out << "(exit)\n";
        ::statistics st;
        m_base->collect_statistics(st);
        st.update("time", last_time);
        st.display_smt2(out);
        out.close();
    }

    char const* lbool2status(lbool r) const {
        switch (r) {
        case l_true:  return "sat";
        case l_false: return "unsat";
        case l_undef: return "unknown";
        }
        return "?";
    }

    std::string mk_file_name() {
        std::stringstream file_name;
        file_name << "pool_solver";
        if (is_virtual()) file_name << "_" << m_pred->get_decl()->get_name();
        file_name << "_" << (m_dump_counter++) << ".smt2";
        return file_name.str();
    }

};

solver_pool::solver_pool(solver* base_solver, unsigned num_pools):
    m_base_solver(base_solver),
    m_num_pools(num_pools),
    m_current_pool(0)
{
    SASSERT(num_pools > 0);
}


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

void solver_pool::updt_params(const params_ref &p) {
    m_base_solver->updt_params(p);
    for (solver *s : m_solvers) s->updt_params(p);
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

/**
   \brief Create a fresh solver instance.
   The first num_pools solvers are independent and
   use a fresh instance of the base solver.
   Subsequent solvers reuse the first num_polls base solvers, rotating
   among the first num_pools.
*/
solver* solver_pool::mk_solver() {
    ref<solver> base_solver;
    ast_manager& m = m_base_solver->get_manager();
    if (m_solvers.size() < m_num_pools) {
        base_solver = m_base_solver->translate(m, m_base_solver->get_params());
    }
    else {
        solver* s = m_solvers[(m_current_pool++) % m_num_pools];
        base_solver = dynamic_cast<pool_solver*>(s)->base_solver();
    }
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
