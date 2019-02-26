/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    opt_pareto.cpp

Abstract:

    Pareto front utilities

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-24

Notes:

   
--*/

#include "opt/opt_pareto.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "model/model_smt2_pp.h"

namespace opt {

    // ---------------------
    // GIA pareto algorithm
   
    lbool gia_pareto::operator()() {
        expr_ref fml(m);
        lbool is_sat = m_solver->check_sat(0, nullptr);
        if (is_sat == l_true) {
            {
                solver::scoped_push _s(*m_solver.get());
                while (is_sat == l_true) {
                    if (m.canceled()) {
                        return l_undef;
                    }
                    m_solver->get_model(m_model);
                    m_solver->get_labels(m_labels);
                    m_model->set_model_completion(true);
                    IF_VERBOSE(1,
                               model_ref mdl(m_model);
                               cb.fix_model(mdl); 
                               model_smt2_pp(verbose_stream() << "new model:\n", m, *mdl, 0););
                    // TBD: we can also use local search to tune solution coordinate-wise.
                    mk_dominates();
                    is_sat = m_solver->check_sat(0, nullptr);
                }
            }
            if (is_sat == l_undef) {
                return l_undef;
            }
            SASSERT(is_sat == l_false);
            is_sat = l_true;
            mk_not_dominated_by();
        }
        return is_sat;
    }

    void pareto_base::mk_dominates() {
        unsigned sz = cb.num_objectives();
        expr_ref fml(m);
        expr_ref_vector gt(m), fmls(m);
        for (unsigned i = 0; i < sz; ++i) {
            fmls.push_back(cb.mk_ge(i, m_model));
            gt.push_back(cb.mk_gt(i, m_model));
        }
        fmls.push_back(mk_or(gt));
        fml = mk_and(fmls);
        IF_VERBOSE(10, verbose_stream() << "dominates: " << fml << "\n";);
        TRACE("opt", model_smt2_pp(tout << fml << "\n", m, *m_model, 0););
        m_solver->assert_expr(fml);        
    }

    void pareto_base::mk_not_dominated_by() {
        unsigned sz = cb.num_objectives();
        expr_ref fml(m);
        expr_ref_vector le(m);
        for (unsigned i = 0; i < sz; ++i) {
            le.push_back(cb.mk_le(i, m_model));
        }
        fml = m.mk_not(mk_and(le));
        IF_VERBOSE(10, verbose_stream() << "not dominated by: " << fml << "\n";);
        TRACE("opt", tout << fml << "\n";);
        m_solver->assert_expr(fml);        
    }

    // ---------------------------------
    // OIA algorithm (without filtering)

    lbool oia_pareto::operator()() {
        solver::scoped_push _s(*m_solver.get());
        lbool is_sat = m_solver->check_sat(0, nullptr);
        if (m.canceled()) {
            is_sat = l_undef;
        }
        if (is_sat == l_true) {
            m_solver->get_model(m_model);
            m_solver->get_labels(m_labels);
            m_model->set_model_completion(true);
            mk_not_dominated_by();
        }
        return is_sat;
    }

}

