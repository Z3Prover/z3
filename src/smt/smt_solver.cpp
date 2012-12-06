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
#include"smt_params.h"

namespace smt {

    class solver : public solver_na2as {
        smt_params          m_params;
        smt::kernel *       m_context;
        progress_callback * m_callback;
    public:
        solver():m_context(0), m_callback(0) {}

        virtual ~solver() {
            if (m_context != 0)
                dealloc(m_context);
        }

        virtual void updt_params(params_ref const & p) {
            m_params.updt_params(p);
            if (m_context == 0)
                return;
            m_context->updt_params(p);
        }

        virtual void collect_param_descrs(param_descrs & r) {
            if (m_context == 0) {
                ast_manager m;
                reg_decl_plugins(m);
                smt::kernel s(m, m_params);
                s.collect_param_descrs(r);
            }
            else {
                m_context->collect_param_descrs(r);
            }
        }

        virtual void init_core(ast_manager & m, symbol const & logic) {
            reset();
            // We can throw exceptions when creating a smt::kernel object
            // So, we should create the smt::kernel outside of the criticial section
            // block. OMP does not allow exceptions to cross critical section boundaries.
            smt::kernel * new_kernel = alloc(smt::kernel, m, m_params);
            #pragma omp critical (solver)
            {
                m_context = new_kernel;
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
        
        // An exception may be thrown when creating a smt::kernel.
        // So, there is no guarantee that m_context != 0 when
        // using smt_solver from the SMT 2.0 command line frontend.
        void check_context() const {
            if (m_context == 0)
                throw default_exception("Z3 failed to create solver, check previous error messages");
        }

        virtual void assert_expr(expr * t) {
            check_context();
            m_context->assert_expr(t);
        }

        virtual void push_core() {
            check_context();
            m_context->push();
        }

        virtual void pop_core(unsigned n) {
            check_context();
            m_context->pop(n);
        }

        virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
            check_context();
            TRACE("solver_na2as", tout << "smt_solver::check_sat_core: " << num_assumptions << "\n";);
            return m_context->check(num_assumptions, assumptions);
        }

        virtual void get_unsat_core(ptr_vector<expr> & r) {
            check_context();
            unsigned sz = m_context->get_unsat_core_size();
            for (unsigned i = 0; i < sz; i++)
                r.push_back(m_context->get_unsat_core_expr(i));
        }

        virtual void get_model(model_ref & m) {
            check_context();
            m_context->get_model(m);
        }

        virtual proof * get_proof() {
            check_context();
            return m_context->get_proof();
        }

        virtual std::string reason_unknown() const {
            check_context();
            return m_context->last_failure_as_string();
        }

        virtual void get_labels(svector<symbol> & r) {
            check_context();
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
