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

#if 0
        opt_solver& s = get_solver();        
        expr_ref val(m);
        rational r;
        lbool is_sat = l_true;
        vector<bounds_t> bounds;
        for (unsigned i = 0; i < m_objectives.size(); ++i) {
            objective const& obj = m_objectives[i];
            if (obj.m_type == O_MAXSMT) {
                IF_VERBOSE(0, verbose_stream() << "Pareto optimization is not supported for MAXSMT\n";);
                return l_undef;
            }
            solver::scoped_push _sp(s);
            is_sat = m_optsmt.pareto(obj.m_index);
            if (is_sat != l_true) {
                return is_sat;
            }
            if (!m_optsmt.get_upper(obj.m_index).is_finite()) {
                return l_undef;
            }
            bounds_t bound;            
            for (unsigned j = 0; j < m_objectives.size(); ++j) {
                objective const& obj_j = m_objectives[j];
                inf_eps lo = m_optsmt.get_lower(obj_j.m_index);
                inf_eps hi = m_optsmt.get_upper(obj_j.m_index);
                bound.push_back(std::make_pair(lo, hi));
            }            
            bounds.push_back(bound);
        }
        for (unsigned i = 0; i < bounds.size(); ++i) {
            for (unsigned j = 0; j < bounds.size(); ++j) {
                objective const& obj = m_objectives[j];
                bounds[i][j].second = bounds[j][j].second;                
            }
            IF_VERBOSE(0, display_bounds(verbose_stream() << "new bound\n", bounds[i]););
        }

        for (unsigned i = 0; i < bounds.size(); ++i) {
            bounds_t b = bounds[i];
            vector<inf_eps> mids;
            solver::scoped_push _sp(s);
            for (unsigned j = 0; j < b.size(); ++j) {
                objective const& obj = m_objectives[j];
                inf_eps mid = (b[j].second - b[j].first)/rational(2);
                mids.push_back(mid);
                expr_ref ge = s.mk_ge(obj.m_index, mid);            
                s.assert_expr(ge);
            }
            is_sat = execute_box();
            switch(is_sat) {
            case l_undef: 
                return is_sat;
            case l_true: {
                bool at_bound = true; 
                for (unsigned j = 0; j < b.size(); ++j) {
                    objective const& obj = m_objectives[j];
                    if (m_model->eval(obj.m_term, val) && is_numeral(val, r)) {
                        mids[j] = inf_eps(r);
                    }
                    at_bound = at_bound && mids[j] == b[j].second;
                    b[j].second = mids[j];
                }
                IF_VERBOSE(0, display_bounds(verbose_stream() << "new bound\n", b););
                if (!at_bound) {
                    bounds.push_back(b);
                }
                break;
            }
            case l_false: {
                bounds_t b2(b);
                for (unsigned j = 0; j < b.size(); ++j) {
                    b2[j].second = mids[j];
                    if (j > 0) {
                        b2[j-1].second = b[j-1].second;
                    }
                    IF_VERBOSE(0, display_bounds(verbose_stream() << "refined bound\n", b2););
                    bounds.push_back(b2);
                }
                break;
            }
            }
        }
        
        return is_sat;
#endif
