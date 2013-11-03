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

--*/

#include "opt_context.h"
#include "fu_malik.h"
#include "weighted_maxsat.h"
#include "ast_pp.h"
#include "opt_solver.h"
#include "arith_decl_plugin.h"
#include "th_rewriter.h"
#include "opt_params.hpp"


namespace opt {

    context::context(ast_manager& m):
        m(m),
        m_hard_constraints(m),
        m_soft_constraints(m),
        m_objectives(m),
        m_opt_objectives(m)
    {
        m_params.set_bool("model", true);
        m_params.set_bool("unsat_core", true);
    }

    void context::optimize() {

        expr_ref_vector const& fmls = m_soft_constraints;

        if (!m_solver) {
            symbol logic;
            set_solver(alloc(opt_solver, m, m_params, logic));
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
                is_sat = weighted_maxsat(get_opt_solver(*s), fmls_copy, m_weights);
            }
            std::cout << "is-sat: " << is_sat << "\n";
            if (is_sat != l_true) {
                return;
            }
            std::cout << "Satisfying soft constraints\n";
            for (unsigned i = 0; i < fmls_copy.size(); ++i) {
                std::cout << mk_pp(fmls_copy[i].get(), m) << "\n";
            }            
        }

        if (!m_objectives.empty()) {
            vector<inf_eps_rational<inf_rational> > values;
            for (unsigned i = 0; i < fmls_copy.size(); ++i) {
                s->assert_expr(fmls_copy[i].get());
            }
            is_sat = m_opt_objectives(get_opt_solver(*s), m_objectives, values);
            std::cout << "is-sat: " << is_sat << std::endl;

            if (is_sat != l_true) {
                return;
            }

            for (unsigned i = 0; i < values.size(); ++i) {
                if (!m_is_max[i]) {
                    values[i].neg();
                }
                std::cout << "objective value: " << mk_pp(m_objectives[i].get(), m) << " -> " << values[i].to_string() << std::endl;                
            }
        }     

        if (m_objectives.empty() && m_soft_constraints.empty()) {
            is_sat = s->check_sat(0,0);
            std::cout << "nothing to optimize: is-sat " << is_sat << std::endl;
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

    opt_solver& context::get_opt_solver(solver& s) {
        if (typeid(opt_solver) != typeid(s)) {
            throw default_exception("BUG: optimization context has not been initialized correctly");
        }
        return dynamic_cast<opt_solver&>(s);
    }

    void context::cancel() {
        if (m_solver) {
            m_solver->cancel();
        }
        m_opt_objectives.set_cancel(true);
    }

    void context::reset_cancel() {
        if (m_solver) {
            m_solver->reset_cancel();
        }
        m_opt_objectives.set_cancel(false);
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

    void context::collect_statistics(statistics& stats) {
        if (m_solver) {
            m_solver->collect_statistics(stats);
        }
    }

    void context::collect_param_descrs(param_descrs & r) {
        opt_params::collect_param_descrs(r);
    }
    
    void context::updt_params(params_ref& p) {
        m_params.append(p);
        if (m_solver) {
            m_solver->updt_params(m_params);
        }
        opt_params _p(m_params);
        m_opt_objectives.set_engine(_p.engine());        
    }


}
