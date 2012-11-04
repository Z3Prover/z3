/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver.cpp

Abstract:

    Wraps smt::kernel as a solver for the external API and cmd_context.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:

--*/
#include"solver_na2as.h"
#include"smt_kernel.h"
#include"reg_decl_plugins.h"
#include"front_end_params.h"

namespace smt {

    class solver : public solver_na2as {
        front_end_params *  m_params;
        smt::kernel *       m_context;
        progress_callback * m_callback;
    public:
        solver():m_params(0), m_context(0), m_callback(0) {}

        virtual ~solver() {
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
                reg_decl_plugins(m);
                front_end_params p;
                smt::kernel s(m, p);
                s.collect_param_descrs(r);
            }
            else {
                m_context->collect_param_descrs(r);
            }
        }

        virtual void init_core(ast_manager & m, symbol const & logic) {
            SASSERT(m_params);
            reset();
#pragma omp critical (solver)
            {
                m_context = alloc(smt::kernel, m, *m_params);
                if (m_callback)
                    m_context->set_progress_callback(m_callback);
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

        virtual void reset_core() {
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

        virtual void push_core() {
            SASSERT(m_context);
            m_context->push();
        }

        virtual void pop_core(unsigned n) {
            SASSERT(m_context);
            m_context->pop(n);
        }

        virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
            SASSERT(m_context);
            TRACE("solver_na2as", tout << "smt_solver::check_sat_core: " << num_assumptions << "\n";);
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
            m_callback = callback;
            if (m_context)
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

};

solver * mk_smt_solver() {
    return alloc(smt::solver);
}
