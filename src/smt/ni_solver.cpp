/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ni_solver.cpp

Abstract:
    Wrappers for smt::kernel that are non-incremental & (quasi-incremental).

Author:

    Leonardo (leonardo) 2011-03-30

Notes:

--*/
#include"ni_solver.h"
#include"smt_kernel.h"
#include"cmd_context.h"

class ni_smt_solver : public solver {
protected:
    cmd_context &       m_cmd_ctx;
    smt::kernel *       m_context;
    progress_callback * m_callback;
public:
    ni_smt_solver(cmd_context & ctx):m_cmd_ctx(ctx), m_context(0), m_callback(0) {}

    virtual ~ni_smt_solver() {
        if (m_context != 0)
            dealloc(m_context);
    }

    virtual void init(ast_manager & m, symbol const & logic) {
        // do nothing
    }

    virtual void collect_statistics(statistics & st) const {
        if (m_context == 0) {
            return;
        }
        else {
            m_context->collect_statistics(st);
        }
    }

    virtual void reset() {
        if (m_context != 0) {
            #pragma omp critical (ni_solver) 
            {
                dealloc(m_context);
                m_context = 0;
            }
        }
    }

    virtual void assert_expr(expr * t) {
        // do nothing
    }

    virtual void push() {
        // do nothing
    }

    virtual void pop(unsigned n) {
        // do nothing
    }

    virtual unsigned get_scope_level() const {
        return m_cmd_ctx.num_scopes();
    }

    void assert_exprs() {
        ptr_vector<expr>::const_iterator it  = m_cmd_ctx.begin_assertions();
        ptr_vector<expr>::const_iterator end = m_cmd_ctx.end_assertions();
        for (; it != end; ++it) {
            m_context->assert_expr(*it);
        }
    }

    void init_solver() {
        reset();
        #pragma omp critical (ni_solver)
        {
            m_context = alloc(smt::kernel, m_cmd_ctx.m(), m_cmd_ctx.params());
        }
        if (m_cmd_ctx.has_logic())
            m_context->set_logic(m_cmd_ctx.get_logic());
        if (m_callback)
            m_context->set_progress_callback(m_callback);
        assert_exprs();
    }

    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        // erase current solver, and create a new one.
        init_solver();

        if (num_assumptions == 0) {
            return m_context->setup_and_check();
        }
        else {
            return m_context->check(num_assumptions, assumptions); 
        }
    }

    virtual void get_unsat_core(ptr_vector<expr> & r) {
        SASSERT(m_context);
        unsigned sz = m_context->get_unsat_core_size();
        for (unsigned i = 0; i < sz; i++)
            r.push_back(m_context->get_unsat_core_expr(i));
    }

    virtual void get_model(model_ref & m) {
        SASSERT(m_context);
        m_context->get_model(m);
    }

    virtual proof * get_proof() {
        SASSERT(m_context);
        return m_context->get_proof();
    }

    virtual std::string reason_unknown() const {
        SASSERT(m_context);
        return m_context->last_failure_as_string();
    }

    virtual void get_labels(svector<symbol> & r) {
        SASSERT(m_context);
        buffer<symbol> tmp;
        m_context->get_relevant_labels(0, tmp);
        r.append(tmp.size(), tmp.c_ptr());
    }

    virtual void set_cancel(bool f) {
        #pragma omp critical (ni_solver)
        {
            if (m_context)
                m_context->set_cancel(f);
        }
    }

    virtual void set_progress_callback(progress_callback * callback) {
        m_callback = callback;
        if (m_context)
            m_context->set_progress_callback(callback);
    }


    virtual void collect_param_descrs(param_descrs & r) {
        smt::kernel::collect_param_descrs(r);
    }

};

solver * mk_non_incremental_smt_solver(cmd_context & ctx) {
    return alloc(ni_smt_solver, ctx);
}

class qi_smt_solver : public ni_smt_solver {
    bool            m_inc_mode;   
public:
    qi_smt_solver(cmd_context & ctx):ni_smt_solver(ctx), m_inc_mode(false) {}
    
    virtual ~qi_smt_solver() {}

    virtual void init(ast_manager & m, symbol const & logic) {
        if (m_inc_mode) {
            init_solver();
            m_inc_mode = true;
        }
    }

    virtual void reset() {
        ni_smt_solver::reset();
        m_inc_mode = false;
    }

    void switch_to_inc() {
        if (!m_inc_mode) {
            init_solver();
            m_inc_mode = true;
        }
        SASSERT(m_inc_mode);
    }

    virtual void assert_expr(expr * t) {
        if (m_context != 0 && !m_inc_mode) {
            // solver was already created to solve a check_sat query...
            switch_to_inc();
        }
        if (m_inc_mode) {
            SASSERT(m_context);
            m_context->assert_expr(t);
        }
    }

    virtual void push() {
        switch_to_inc();
        SASSERT(m_context);
        m_context->push();
        SASSERT(m_inc_mode);
    }

    virtual void pop(unsigned n) {
        switch_to_inc();
        SASSERT(m_context);
        m_context->pop(n);
        SASSERT(m_inc_mode);
    }

    virtual unsigned get_scope_level() const {
        if (!m_inc_mode)
            return 0;
        else
            return m_context->get_scope_level();
    }


    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        if (!m_inc_mode) {
            lbool r = ni_smt_solver::check_sat(num_assumptions, assumptions);
            SASSERT(!m_inc_mode);
            return r;
        }
        else {
            return m_context->check(num_assumptions, assumptions); 
        }
    }
};


solver * mk_quasi_incremental_smt_solver(cmd_context & ctx) {
    return alloc(qi_smt_solver, ctx);
}
