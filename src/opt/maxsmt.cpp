/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_maxsmt.cpp

Abstract:
   
    MaxSMT optimization context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-7

Notes:

--*/

#include "maxsmt.h"
#include "fu_malik.h"
#include "weighted_maxsat.h"
#include "ast_pp.h"

namespace opt {

    lbool maxsmt::operator()(solver& s) {
        lbool is_sat;
        m_answer.reset();
        m_msolver = 0;
        if (m_answer.empty()) {
            m_msolver = 0;
            is_sat = s.check_sat(0, 0);
            m_answer.append(m_soft_constraints);
        }
        else if (is_maxsat_problem(m_weights)) {
            m_msolver = alloc(fu_malik, m, s, m_soft_constraints);
        }
        else {
            m_msolver = alloc(wmaxsmt, m, opt_solver::to_opt(s), m_soft_constraints, m_weights);
        }

        if (m_msolver) {
            is_sat = (*m_msolver)();
            m_answer.append(m_msolver->get_assignment());
        }

        // Infrastructure for displaying and storing solution is TBD.
        std::cout << "is-sat: " << is_sat << "\n";
        if (is_sat == l_true) {
            std::cout << "Satisfying soft constraints\n";
            display_answer(std::cout);
        }
        return is_sat;
    }

    expr_ref_vector maxsmt::get_assignment() const {
        return m_answer;
    } 

    inf_eps maxsmt::get_value() const {
        if (m_msolver) {
            return inf_eps(m_msolver->get_value());
        }
        return inf_eps();
    }

    inf_eps maxsmt::get_lower() const {
        if (m_msolver) {
            return inf_eps(m_msolver->get_lower());
        }
        return inf_eps();
    }

    inf_eps maxsmt::get_upper() const {
        if (m_msolver) {
            return inf_eps(m_msolver->get_upper());
        }
        return inf_eps();
    }

    void maxsmt::commit_assignment() {
        for (unsigned i = 0; i < m_answer.size(); ++i) {
            s->assert_expr(m_answer[i].get());
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
    }


};
