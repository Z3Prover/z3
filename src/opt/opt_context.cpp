/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_context.cpp

Abstract:
    Facility for running optimization problem.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/


#include "opt_context.h"
#include "smt_solver.h"
#include "fu_malik.h"
#include "weighted_maxsat.h"
#include "optimize_objectives.h"
#include "ast_pp.h"

namespace opt {

    void context::optimize() {

        expr_ref_vector const& fmls = m_soft_constraints;

        ref<solver> s;
        symbol logic;
        params_ref p;
        p.set_bool("model", true);
        p.set_bool("unsat_core", true);        
        s = mk_smt_solver(m, p, logic);

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
            vector<optional<rational> > values;
            for (unsigned i = 0; i < fmls_copy.size(); ++i) {
                s->assert_expr(fmls_copy[i].get());
            }
            is_sat = optimize_objectives(*s, m_objectives, m_is_max, values);
            std::cout << "is-sat: " << is_sat << "\n";
            if (is_sat != l_true) {
                return;
            }
            for (unsigned i = 0; i < values.size(); ++i) {
                // display
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

}
