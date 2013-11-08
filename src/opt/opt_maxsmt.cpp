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

    lbool maxsmt::operator()(opt_solver& s, expr_ref_vector& fmls, vector<rational> const& ws) {
        lbool is_sat;
        
        if (fmls.empty()) {
            is_sat = s.check_sat(0, 0);
        }
        else if (is_maxsat_problem(ws)) {
            is_sat = opt::fu_malik_maxsat(s, fmls);
        }
        else {
            is_sat = weighted_maxsat(s, fmls, ws);
        }

        // Infrastructure for displaying and storing solution is TBD.
        std::cout << "is-sat: " << is_sat << "\n";
        if (is_sat == l_true) {
            std::cout << "Satisfying soft constraints\n";
            for (unsigned i = 0; i < fmls.size(); ++i) {
                std::cout << mk_pp(fmls[i].get(), m) << "\n";
            }           
        } 
        return is_sat;
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
