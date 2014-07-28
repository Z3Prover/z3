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


namespace opt {

    class sls : public maxsmt_solver_base {
    public:
        sls(opt_solver* s, ast_manager& m, params_ref& p, 
            vector<rational> const& ws, expr_ref_vector const& soft): 
            maxsmt_solver_base(s, m, p, ws, soft) {
        }
        virtual ~sls() {}
        lbool operator()() {
            IF_VERBOSE(1, verbose_stream() << "(opt.sls)\n";);
            enable_bvsat();
            enable_sls();
            init();
            lbool is_sat = s().check_sat(0, 0);
            if (is_sat == l_true) {
                s().get_model(m_model);
                m_upper.reset();
                for (unsigned i = 0; i < m_soft.size(); ++i) {
                    expr_ref tmp(m);
                    m_model->eval(m_soft[i].get(), tmp, true);
                    m_assignment[i] = m.is_true(tmp);
                    if (!m_assignment[i]) {
                        m_upper += m_weights[i];
                    }
                }
            }
            return is_sat;
        }

    };

    maxsmt_solver_base* opt::mk_sls(ast_manager& m, opt_solver* s, params_ref& p, 
                                    vector<rational> const& ws, expr_ref_vector const& soft) {
        return alloc(sls, s, m, p, ws, soft);
    }


};
