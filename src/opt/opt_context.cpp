/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_context.cpp

Abstract:
    Facility for running optimization problem.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    TODO:

    - there are race conditions for cancelation.
    - it would also be a good idea to maintain a volatile bool to track
      cancelation and then bail out of loops inside optimize() and derived
      functions.

--*/

#include "opt_context.h"
#include "fu_malik.h"
#include "weighted_maxsat.h"
#include "optimize_objectives.h"
#include "ast_pp.h"
#include "opt_solver.h"
#include "arith_decl_plugin.h"
#include "th_rewriter.h"


namespace opt {

    void context::optimize() {

        expr_ref_vector const& fmls = m_soft_constraints;

        if (!m_solver) {
            symbol logic;
            params_ref p;
            p.set_bool("model", true);
            p.set_bool("unsat_core", true);        
            set_solver(alloc(opt_solver, m, p, logic));
        }
        solver* s = m_solver.get();

        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s->assert_expr(m_hard_constraints[i].get());
        }

        expr_ref_vector fmls_copy(fmls);
        lbool is_sat;
        if (!fmls.empty()) {
            if (is_maxsat_problem()) {
                is_sat = opt::fu_malik_maxsat(*s, fmls_copy);
            }
            else {
                is_sat = weighted_maxsat(*s, fmls_copy, m_weights);
            }
            std::cout << "is-sat: " << is_sat << "\n";
            if (is_sat != l_true) {
                return;
            }
            for (unsigned i = 0; i < fmls_copy.size(); ++i) {
                std::cout << "Satisfying soft constraint: " << mk_pp(fmls_copy[i].get(), m) << "\n";
            }            
        }

        if (!m_objectives.empty()) {
            vector<inf_eps_rational<inf_rational> > values;
            for (unsigned i = 0; i < fmls_copy.size(); ++i) {
                s->assert_expr(fmls_copy[i].get());
            }
            // SASSERT(instanceof(*s, opt_solver));
            // if (!instsanceof ...) { throw ... invalid usage ..} 
            is_sat = optimize_objectives(dynamic_cast<opt_solver&>(*s), m_objectives, values);
            std::cout << "is-sat: " << is_sat << "\n";

            if (is_sat != l_true) {
                return;
            }

            for (unsigned i = 0; i < values.size(); ++i) {
                if (!m_is_max[i]) {
                    values[i].neg();
                }
                std::cout << "objective function: " << mk_pp(m_objectives[i].get(), m) << " -> " << values[i].to_string() << "\n";                
            }
        }     

        if (m_objectives.empty() && m_soft_constraints.empty()) {
            is_sat = s->check_sat(0,0);
            std::cout << "nothing to optimize: is-sat " << is_sat << "\n";
        }

    }
        
    bool context::is_maxsat_problem() const {
        vector<rational> const& ws  = m_weights;
        for (unsigned i = 0; i < ws.size(); ++i) {
            if (!ws[i].is_one()) {
                return false;
            }
        }
        return true;
    }

    void context::cancel() {
        if (m_solver) {
            m_solver->cancel();
        }
    }

    void context::reset_cancel() {
        if (m_solver) {
            m_solver->reset_cancel();
        }
    }

    void context::add_objective(app* t, bool is_max) {
        expr_ref t1(t, m), t2(m);
        th_rewriter rw(m);
        if (!is_max) {
            arith_util a(m);
            t1 = a.mk_uminus(t);
        }
        rw(t1, t2);
        SASSERT(is_app(t2));
        m_objectives.push_back(to_app(t2));
        m_is_max.push_back(is_max);
    }


}
