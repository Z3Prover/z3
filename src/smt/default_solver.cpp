/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    default_solver.cpp

Abstract:

    Wrapps smt::solver as a solver for cmd_context

Author:

    Leonardo (leonardo) 2012-10-21

Notes:

--*/
#include"solver.h"
#include"smt_solver.h"

class default_solver : public solver {
    front_end_params * m_params;
    smt::solver *     m_context;
public:
    default_solver():m_params(0), m_context(0) {}

    virtual ~default_solver() {
        if (m_context != 0)
            dealloc(m_context);
    }

    virtual void set_front_end_params(front_end_params & p) {
        m_params = &p;
    }

    virtual void updt_params(params_ref const & p) {
        if (m_context == 0)
            return;
        m_context->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        if (m_context == 0) {
            ast_manager m;
            m.register_decl_plugins();
            front_end_params p;
            smt::solver s(m, p);
            s.collect_param_descrs(r);
        }
        else {
            m_context->collect_param_descrs(r);
        }
    }

    virtual void init(ast_manager & m, symbol const & logic) {
        SASSERT(m_params);
        reset();
        #pragma omp critical (solver)
        {
            m_context = alloc(smt::solver, m, *m_params);
        }
        if (logic != symbol::null)
            m_context->set_logic(logic);
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
            #pragma omp critical (solver)
            {
                dealloc(m_context);
                m_context = 0;
            }
        }
    }

    virtual void assert_expr(expr * t) {
        SASSERT(m_context);
        m_context->assert_expr(t);
    }

    virtual void push() {
        SASSERT(m_context);
        m_context->push();
    }

    virtual void pop(unsigned n) {
        SASSERT(m_context);
        m_context->pop(n);
    }

    virtual unsigned get_scope_level() const {
        if (m_context)
            return m_context->get_scope_level();
        else
            return 0;
    }

    virtual lbool check_sat(unsigned num_assumptions, expr * const * assumptions) {
        SASSERT(m_context);
        return m_context->check(num_assumptions, assumptions);
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
        #pragma omp critical (solver)
        {
            if (m_context) 
                m_context->set_cancel(f);
        }
    }

    virtual void set_progress_callback(progress_callback * callback) {
        SASSERT(m_context);
        m_context->set_progress_callback(callback);
    }

    virtual unsigned get_num_assertions() const {
        if (m_context)
            return m_context->size();
        else
            return 0;
    }
    
    virtual expr * get_assertion(unsigned idx) const {
        SASSERT(m_context);
        SASSERT(idx < get_num_assertions());
        return m_context->get_formulas()[idx];
    }

    virtual void display(std::ostream & out) const {
        if (m_context)
            m_context->display(out);
        else
            out << "(solver)";
    }
   
};

solver * mk_default_solver() {
    return alloc(default_solver);
}
