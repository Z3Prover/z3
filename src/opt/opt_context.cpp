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
        m_opt_objectives(m),
        m_maxsmt(m)
    {
        m_params.set_bool("model", true);
        m_params.set_bool("unsat_core", true);
    }

    void context::optimize() {

        if (!m_solver) {
            symbol logic;
            set_solver(alloc(opt_solver, m, m_params, logic));
        }

        // really just works for opt_solver now.
        solver* s = m_solver.get(); 
        opt_solver::scoped_push _sp(get_opt_solver(*s));

        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s->assert_expr(m_hard_constraints[i].get());
        }
        
        lbool is_sat;

        is_sat = m_maxsmt(get_opt_solver(*s), m_soft_constraints, m_weights);

        for (unsigned i = 0; i < m_soft_constraints.size(); ++i) {
            s->assert_expr(m_soft_constraints[i].get());
        }

        if (is_sat == l_true) {           
            is_sat = m_opt_objectives(get_opt_solver(*s), m_objectives);        
        }

        if (m_objectives.empty() && m_soft_constraints.empty()) {
            is_sat = s->check_sat(0,0);
            std::cout << "nothing to optimize: is-sat " << is_sat << std::endl;
        }
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
        m_maxsmt.set_cancel(true);
    }

    void context::reset_cancel() {
        if (m_solver) {
            m_solver->reset_cancel();
        }
        m_opt_objectives.set_cancel(false);
        m_maxsmt.set_cancel(false);
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
