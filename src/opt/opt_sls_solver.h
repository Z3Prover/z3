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
#include "card2bv_tactic.h"
#include "pb_sls.h"

namespace opt {
    
    class sls_solver : public solver_na2as {
        ast_manager&     m;
        ref<solver>      m_solver;
        scoped_ptr<bvsls_opt_engine> m_bvsls;
        scoped_ptr<smt::pb_sls>      m_pbsls;
        pb::card_pb_rewriter m_pb2bv;
        model_ref        m_model;
        expr_ref         m_objective;        
        params_ref       m_params;
        symbol           m_engine; 
    public:
        sls_solver(ast_manager & m, solver* s, expr* to_maximize, params_ref const& p):
            solver_na2as(m),
            m(m),
            m_solver(s),
            m_bvsls(0),
            m_pbsls(0),
            m_pb2bv(m),
            m_objective(to_maximize, m)
        {            
        }
        virtual ~sls_solver() {}

        virtual void updt_params(params_ref & p) {
            m_solver->updt_params(p);
            m_params.copy(p);
            opt_params _p(p);
            m_engine = _p.sls_engine();
        }
        virtual void collect_param_descrs(param_descrs & r) {
            m_solver->collect_param_descrs(r);
        }
        virtual void collect_statistics(statistics & st) const {
            m_solver->collect_statistics(st);
            if (m_bvsls) m_bvsls->collect_statistics(st);
            if (m_pbsls) m_pbsls->collect_statistics(st);
        }
        virtual void assert_expr(expr * t) {
            m_solver->assert_expr(t);
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
            m_pb2bv.set_cancel(f);
            #pragma omp critical (this)
            {
                if (m_bvsls) {
                    m_bvsls->set_cancel(f);
                }
                if (m_pbsls) {
                    m_pbsls->set_cancel(f);
                }
            }
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
            // if (m_bvsls) m_bvsls->display(out);
        }

    protected:
        typedef bvsls_opt_engine::optimization_result opt_result;

        virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions) {            
            lbool r = m_solver->check_sat(num_assumptions, assumptions);
            if (r == l_true) {
                m_solver->get_model(m_model);
                if (m_engine == symbol("pb")) {

                }
                else {
                    bvsls_opt();
                }
            }
            return r;
        }
        virtual void push_core() {
            m_solver->push();
        }
        virtual void pop_core(unsigned n) {
            m_solver->pop(n);
        }

    private:
        void assertions2sls() {
            expr_ref tmp(m);
            goal_ref g(alloc(goal, m, true, false));
            for (unsigned i = 0; i < m_solver->get_num_assertions(); ++i) {
                m_pb2bv(m_solver->get_assertion(i), tmp);
                g->assert_expr(tmp);
            }
            tactic_ref simplify = mk_nnf_tactic(m);
            proof_converter_ref pc;
            expr_dependency_ref core(m);
            goal_ref_buffer result;
            model_converter_ref model_converter;
            (*simplify)(g, result, model_converter, pc, core);
            SASSERT(result.size() == 1);
            goal* r = result[0];
            for (unsigned i = 0; i < r->size(); ++i) {
                m_bvsls->assert_expr(r->form(i));
            }
        }

        void pbsls_opt() {
            #pragma omp critical (this)
            {
                m_pbsls = alloc(smt::pb_sls, m);
            }
            m_pbsls->set_model(m_model);
            m_pbsls->updt_params(m_params);
            for (unsigned i = 0; i < m_solver->get_num_assertions(); ++i) {
                m_pbsls->add(m_solver->get_assertion(i));
            }
#if 0
        TBD:
            for (unsigned i = 0; i < m_num_soft; ++i) {
                m_pbsls->add(m_soft[i].get(), m_weights[i].get());
            }
#endif

            lbool is_sat = (*m_pbsls.get())();
            if (is_sat == l_true) {
                m_bvsls->get_model(m_model);
            }
        }

        void bvsls_opt() {
            #pragma omp critical (this)
            {
                m_bvsls = alloc(bvsls_opt_engine, m, m_params);
            }
            assertions2sls();
            opt_result or = m_bvsls->optimize(m_objective, m_model, true);
            SASSERT(or.is_sat == l_true || or.is_sat == l_undef);
            if (or.is_sat == l_true) {
                m_bvsls->get_model(m_model);
            }
        }

    };
}

#endif
