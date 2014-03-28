/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    bvsls_opt_engine.h

Abstract:

    Optimization extensions to bvsls

Author:

    Christoph (cwinter) 2014-03-28

Notes:

--*/
#ifndef _BVSLS_OPT_ENGINE_H_
#define _BVSLS_OPT_ENGINE_H_

#include "sls_engine.h"

class bvsls_opt_engine : public sls_engine {
public:
    bvsls_opt_engine(ast_manager & m, params_ref const & p);
    ~bvsls_opt_engine();

    class optimization_result {
    public:
        lbool is_sat;
        expr_ref optimum;
        optimization_result(ast_manager & m) : is_sat(l_undef), optimum(m) {}
    };

    optimization_result optimize(expr_ref const & objective);

protected:
    expr_ref maximize(expr_ref const & objective);
};

#endif