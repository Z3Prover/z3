/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    maxsmt.cpp

Abstract:
   
    MaxSMT optimization context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-7

Notes:

--*/

#include "maxsmt.h"
#include "fu_malik.h"
#include "core_maxsat.h"
#include "weighted_maxsat.h"
#include "ast_pp.h"
#include "opt_params.hpp"

namespace opt {

    lbool maxsmt::operator()(solver& s) {
        lbool is_sat;
        m_answer.reset();
        m_msolver = 0;
        m_s = &s;
        if (m_soft_constraints.empty()) {
            m_msolver = 0;
            is_sat = s.check_sat(0, 0);
            m_answer.reset();
        }
        else if (is_maxsat_problem(m_weights)) {
            if (m_maxsat_engine == symbol("core_maxsat")) {
                m_msolver = alloc(core_maxsat, m, s, m_soft_constraints);
            }
            else {
                m_msolver = alloc(fu_malik, m, s, m_soft_constraints);
            }
        }
        else {
            m_msolver = alloc(wmaxsmt, m, opt_solver::to_opt(s), m_soft_constraints, m_weights);
        }

        if (m_msolver) {
            is_sat = (*m_msolver)();
            m_answer.append(m_msolver->get_assignment());
        }

        // Infrastructure for displaying and storing solution is TBD.
        IF_VERBOSE(1, verbose_stream() << "is-sat: " << is_sat << "\n";
                   if (is_sat == l_true) {
                       verbose_stream() << "Satisfying soft constraints\n";
                       display_answer(verbose_stream());
                   });

        DEBUG_CODE(if (is_sat == l_true) {
                m_s->push();
                commit_assignment();
                VERIFY(l_true == m_s->check_sat(0,0));
                m_s->pop(1);
                // TBD: check that all extensions are unsat too

            });
        return is_sat;
    }

    expr_ref_vector maxsmt::get_assignment() const {
        return m_answer;
    } 

    inf_eps maxsmt::get_value() const {
        if (m_msolver) {
            return inf_eps(m_msolver->get_value());
        }
        return inf_eps(m_upper);
    }

    inf_eps maxsmt::get_lower() const {
        rational r = m_lower;
        if (m_msolver) {
            rational q = m_msolver->get_lower();
            if (r < q) r = q;
        }
        return inf_eps(r);
    }

    inf_eps maxsmt::get_upper() const {
        rational r = m_upper;
        if (m_msolver) {
            rational q = m_msolver->get_upper();
            if (r > q) r = q;
        }
        return inf_eps(r);
    }

    void maxsmt::update_lower(rational const& r) {
        if (m_lower > r)  m_lower = r;
    }

    void maxsmt::commit_assignment() {
        SASSERT(m_s);
        for (unsigned i = 0; i < m_answer.size(); ++i) {
            m_s->assert_expr(m_answer[i].get());
        }
    }

    void maxsmt::display_answer(std::ostream& out) const {
        for (unsigned i = 0; i < m_answer.size(); ++i) {
            out << mk_pp(m_answer[i], m) << "\n";
        } 
    }
    
    void maxsmt::set_cancel(bool f) {
        m_cancel = f;
        if (m_msolver) {
            m_msolver->set_cancel(f);
        }
    }
    
    bool maxsmt::is_maxsat_problem(vector<rational> const& ws) const {
        for (unsigned i = 0; i < ws.size(); ++i) {
            if (!ws[i].is_one()) {
                return false;
            }
        }
        return true;
    }

    void maxsmt::updt_params(params_ref& p) {
        opt_params _p(p);
        m_maxsat_engine = _p.maxsat_engine();        
    }

    void maxsmt::collect_statistics(statistics& st) const {
        if (m_msolver) {
            m_msolver->collect_statistics(st);
        }
    }


};
