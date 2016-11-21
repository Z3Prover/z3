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
            obj_map<expr, rational> soft;            
            lbool is_sat = find_mutexes(soft);
            if (is_sat != l_true) {
                return is_sat;
            }
            rational offset = m_lower;
            m_upper = offset;
            bool was_sat = false;
            expr_ref_vector disj(m);
            obj_map<expr, rational>::iterator it = soft.begin(), end = soft.end();
            for (; it != end; ++it) {
                expr_ref tmp(m);
                bool is_true = m_model->eval(it->m_key, tmp) && m.is_true(tmp);
                expr* c = wth().assert_weighted(it->m_key, it->m_value, is_true);
                if (!is_true) {
                    m_upper += it->m_value;
                    disj.push_back(c);
                }
            }
            s().assert_expr(mk_or(disj));
            trace_bounds("wmax");
            while (l_true == is_sat && m_lower < m_upper) {
                is_sat = s().check_sat(0, 0);
                if (m.canceled()) {
                    is_sat = l_undef;
                }
                if (is_sat == l_true) {
                    if (wth().is_optimal()) {
                        m_upper = offset + wth().get_min_cost();
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
                m_upper = offset + wth().get_min_cost();
            }
            if (is_sat == l_false && was_sat) {
                is_sat = l_true;
            }
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
