/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_smt_solver.h

Abstract:

    A Stochastic Local Search (SLS) Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-10
    
--*/

#pragma once
#include "ast/sls/sls_context.h"
#include "ast/sls/sat_ddfw.h"


namespace sls {

    class smt_solver {
        ast_manager& m;
        class solver_ctx;
        sat::ddfw m_ddfw;
        solver_ctx* m_solver_ctx = nullptr;        
        expr_ref_vector m_assertions;
        statistics m_st;
        
    public:
        smt_solver(ast_manager& m, params_ref const& p);
        ~smt_solver();
        void assert_expr(expr* e);
        lbool check();
        model_ref get_model();
        void updt_params(params_ref& p) {}
        void collect_statistics(statistics& st);
        std::ostream& display(std::ostream& out);
        void reset_statistics();
    };
}
