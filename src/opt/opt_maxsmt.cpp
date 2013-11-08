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

#include "opt_maxsmt.h"
#include "fu_malik.h"
#include "weighted_maxsat.h"
#include "ast_pp.h"

namespace opt {

    lbool maxsmt::operator()(opt_solver& s) {
        lbool is_sat;
        m_answer.reset();
        m_answer.append(m_soft_constraints);
        if (m_answer.empty()) {
            is_sat = s.check_sat(0, 0);
        }
        else if (is_maxsat_problem(m_weights)) {
            is_sat = opt::fu_malik_maxsat(s, m_answer);
        }
        else {
            is_sat = weighted_maxsat(s, m_answer, m_weights);
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

    void maxsmt::display_answer(std::ostream& out) const {
        for (unsigned i = 0; i < m_answer.size(); ++i) {
            out << mk_pp(m_answer[i], m) << "\n";
        } 
    }
    
    void maxsmt::set_cancel(bool f) {
        m_cancel = f;
    }
    
    bool maxsmt::is_maxsat_problem(vector<rational> const& ws) const {
        for (unsigned i = 0; i < ws.size(); ++i) {
            if (!ws[i].is_one()) {
                return false;
            }
        }
        return true;
    }



};
