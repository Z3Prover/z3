/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    wmax.cpp

Abstract:

    Theory based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/
#include "wmax.h"
#include "uint_set.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"
#include "smt_theory.h"
#include "smt_context.h"
#include "theory_wmaxsat.h"
#include "opt_context.h"

namespace opt {
    // ----------------------------------------------------------
    // weighted max-sat using a custom theory solver for max-sat.
    // NB. it is quite similar to pseudo-Boolean propagation.


    class wmax : public maxsmt_solver_base {
    public:
        wmax(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(c, ws, soft) {}
        virtual ~wmax() {}

        lbool operator()() {
            TRACE("opt", tout << "weighted maxsat\n";);
            scoped_ensure_theory wth(*this);
            lbool is_sat = l_true;
            bool was_sat = false;
            for (unsigned i = 0; i < m_soft.size(); ++i) {
                wth().assert_weighted(m_soft[i], m_weights[i]);
            }
            while (l_true == is_sat) {
                is_sat = s().check_sat(0,0);
                if (m.canceled()) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    if (wth().is_optimal()) {
                        m_upper = wth().get_min_cost();
                        s().get_model(m_model);
                    }
                    expr_ref fml = wth().mk_block();
                    s().assert_expr(fml);
                    was_sat = true;
                }
                trace_bounds("wmax");
            }
            if (was_sat) {
                wth().get_assignment(m_assignment);
            }
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
            }
            m_upper = wth().get_min_cost();
            if (is_sat == l_true) {
                m_lower = m_upper;
            }
            TRACE("opt", tout << "min cost: " << m_upper << "\n";);
            return is_sat;
        }
    };

    maxsmt_solver_base* mk_wmax(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft) {
        return alloc(wmax, c, ws, soft);
    }

}
