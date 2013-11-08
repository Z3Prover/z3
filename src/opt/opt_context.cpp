/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_context.cpp

Abstract:
    Facility for running optimization problem.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    TODO:

    - there are race conditions for cancelation.

--*/

#include "opt_context.h"
#include "ast_pp.h"
#include "opt_solver.h"
#include "arith_decl_plugin.h"
#include "th_rewriter.h"
#include "opt_params.hpp"

namespace opt {

    context::context(ast_manager& m):
        m(m),
        m_hard_constraints(m),
        m_optsmt(m),
        m_maxsmt(m)
    {
        m_params.set_bool("model", true);
        m_params.set_bool("unsat_core", true);
        m_solver = alloc(opt_solver, m, m_params, symbol());
    }

    void context::optimize() {

        opt_solver& s = *m_solver.get(); 
        opt_solver::scoped_push _sp(s);

        for (unsigned i = 0; i < m_hard_constraints.size(); ++i) {
            s.assert_expr(m_hard_constraints[i].get());
        }
        
        lbool is_sat = m_maxsmt(s);
        if (is_sat == l_true) {           
            is_sat = m_optsmt(s);
        }
    }
        
    void context::set_cancel(bool f) {
        if (m_solver) {
            m_solver->set_cancel(f);
        }
        m_optsmt.set_cancel(f);
        m_maxsmt.set_cancel(f);
    }

    void context::collect_statistics(statistics& stats) {
        if (m_solver) {
            m_solver->collect_statistics(stats);
        }
    }

    void context::collect_param_descrs(param_descrs & r) {
        opt_params::collect_param_descrs(r);
    }
    
    void context::updt_params(params_ref& p) {
        m_params.append(p);
        if (m_solver) {
            m_solver->updt_params(m_params);
        }
        m_optsmt.updt_params(m_params);
        m_maxsmt.updt_params(m_params);
    }


}
