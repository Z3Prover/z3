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

#include "opt_pareto.h"
#include "ast_pp.h"

namespace opt {

    // ---------------------
    // GIA pareto algorithm
   
    lbool gia_pareto::operator()() {
        model_ref model;
        expr_ref fml(m);
        lbool is_sat = m_solver->check_sat(0, 0);
        while (is_sat == l_true) {
            {
                solver::scoped_push _s(*m_solver.get());
                while (is_sat == l_true) {
                    if (m_cancel) {
                        return l_undef;
                    }
                    m_solver->get_model(model);
                    // TBD: we can also use local search to tune solution coordinate-wise.
                    mk_dominates(model);
                    is_sat = m_solver->check_sat(0, 0);
                }
                if (is_sat == l_undef) {
                    return l_undef;
                }
                is_sat = l_true;
            }
            cb.yield(model);
            mk_not_dominated_by(model);
            is_sat = m_solver->check_sat(0, 0);
        }
        if (is_sat == l_undef) {
            return l_undef;
        }
        return l_true;
    }

    void pareto_base::mk_dominates(model_ref& model) {
        unsigned sz = cb.num_objectives();
        expr_ref fml(m);
        expr_ref_vector gt(m), fmls(m);
        for (unsigned i = 0; i < sz; ++i) {
            fmls.push_back(cb.mk_ge(i, model));
            gt.push_back(cb.mk_gt(i, model));
        }
        fmls.push_back(m.mk_or(gt.size(), gt.c_ptr()));
        fml = m.mk_and(fmls.size(), fmls.c_ptr());
        IF_VERBOSE(10, verbose_stream() << "dominates: " << fml << "\n";);
        m_solver->assert_expr(fml);        
    }

    void pareto_base::mk_not_dominated_by(model_ref& model) {
        unsigned sz = cb.num_objectives();
        expr_ref fml(m);
        expr_ref_vector le(m);
        for (unsigned i = 0; i < sz; ++i) {
            le.push_back(cb.mk_le(i, model));
        }
        fml = m.mk_not(m.mk_and(le.size(), le.c_ptr()));
        IF_VERBOSE(10, verbose_stream() << "not dominated by: " << fml << "\n";);
        m_solver->assert_expr(fml);        
    }

    // ---------------------------------
    // OIA algorithm (without filtering)

    lbool oia_pareto::operator()() {
        model_ref model;
        solver::scoped_push _s(*m_solver.get());
        lbool is_sat = m_solver->check_sat(0, 0);
        if (is_sat != l_true) {
            return is_sat;
        }
        while (is_sat == l_true) {
            if (m_cancel) {
                return l_undef;
            }
            m_solver->get_model(model);
            cb.yield(model);
            mk_not_dominated_by(model);
            is_sat = m_solver->check_sat(0, 0);
        }
        if (m_cancel) {
            return l_undef;
        }
        return l_true;
    }

}

