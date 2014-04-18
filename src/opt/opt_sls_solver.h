/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    opt_sls_solver.h

Abstract:

    Wraps a solver with SLS for improving a solution using an objective function.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-18

Notes:

   
--*/
#ifndef _OPT_SLS_SOLVER_H_
#define _OPT_SLS_SOLVER_H_

#include "solver_na2as.h"

namespace opt {
    
    class sls_solver : public solver_na2as {
        ast_manager&     m;
        ref<solver>      m_solver;
        bvsls_opt_engine m_sls;
        model_ref        m_model;
        expr_ref         m_objective;
    public:
        sls_solver(ast_manager & m, solver* s, expr* to_maximize, params_ref const& p):
            solver_na2as(m),
            m(m),
            m_solver(s),
            m_sls(m, p),
            m_objective(to_maximize,m)
        {            
        }
        virtual ~sls_solver() {}

        virtual void updt_params(params_ref & p) {
            m_solver->updt_params(p);
        }
        virtual void collect_param_descrs(param_descrs & r) {
            m_solver->collect_param_descrs(r);
        }
        virtual void collect_statistics(statistics & st) const {
            m_solver->collect_statistics(st);
            // TBD: m_sls.get_stats();
        }
        virtual void assert_expr(expr * t) {
            m_solver->assert_expr(t);
            m_sls.assert_expr(t);
        }
        virtual void get_unsat_core(ptr_vector<expr> & r) {
            m_solver->get_unsat_core(r);
        }
        virtual void get_model(model_ref & m) {
            m = m_model;
        }
        virtual proof * get_proof() {
            return m_solver->get_proof();
        }
        virtual std::string reason_unknown() const {
            return m_solver->reason_unknown();
        }
        virtual void get_labels(svector<symbol> & r) {
            m_solver->get_labels(r);
        }
        virtual void set_cancel(bool f) {
            m_solver->set_cancel(f);
            m_sls.set_cancel(f);
        }
        virtual void set_progress_callback(progress_callback * callback) {
            m_solver->set_progress_callback(callback);
        }
        virtual unsigned get_num_assertions() const {
            return m_solver->get_num_assertions();
        }
        virtual expr * get_assertion(unsigned idx) const {
            return m_solver->get_assertion(idx);
        }
        virtual void display(std::ostream & out) const {
            m_solver->display(out);
            // m_sls.display(out);
        }

    protected:
        virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
            lbool r = m_solver->check_sat(num_assumptions, assumptions);
            if (r == l_true) {
                m_solver->get_model(m_model);
                bvsls_opt_engine::optimization_result or(m);
                or = m_sls.optimize(m_objective, m_model, true);
                SASSERT(or.is_sat == l_true);
                m_sls.get_model(m_model);
                or.optimum;
            }
            return r;
        }
        virtual void push_core() {
            m_solver->push();
        }
        virtual void pop_core(unsigned n) {
            m_solver->pop(n);
        }

    };
}

#endif
