/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    maxsls.cpp

Abstract:

    Weighted SLS MAXSAT module

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/

#include "maxsls.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"
#include "opt_context.h"
#include "inc_sat_solver.h"


namespace opt {

    class sls : public maxsmt_solver_base {
    public:
        sls(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(c, ws, soft) {
        }
        virtual ~sls() {}
        lbool operator()() {
            IF_VERBOSE(1, verbose_stream() << "(opt.sls)\n";);
            init();
            enable_sls(true);
            lbool is_sat = check();
            if (is_sat == l_true) {
                s().get_model(m_model);
                m_upper.reset();
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    expr_ref tmp(m);
                    m_model->eval(m_soft[i], tmp, true);
                    m_assignment[i] = m.is_true(tmp);
                    if (!m_assignment[i]) {
                        m_upper += m_weights[i];
                    }
                }
            }
            return is_sat;
        }
        
        lbool check() {
            if (m_c.sat_enabled()) {
                return inc_sat_check_sat(
                    s(), m_soft.size(), m_soft.c_ptr(), m_weights.c_ptr(), m_upper);
            }
            else {
                return s().check_sat(0, 0);
            }
        }

    };

    maxsmt_solver_base* mk_sls(
        maxsat_context& c, weights_t& ws, expr_ref_vector const& soft) {
        return alloc(sls, c, ws, soft);
    }


};
