/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    theory_opt.h

Abstract:

    Interface utilities used by optimization providing 
    theory solvers.

Author:

    Nikolaj Bjorner (nbjorner) 2013-10-18

Notes:

--*/

#include "inf_rational.h"
#include "inf_eps_rational.h"
#include "arith_decl_plugin.h"

#ifndef THEORY_OPT_H_
#define THEORY_OPT_H_

class filter_model_converter;
namespace smt {
    class theory_opt {
    public:
        typedef inf_eps_rational<inf_rational> inf_eps;
        virtual inf_eps value(theory_var) = 0;
        virtual inf_eps maximize(theory_var v, expr_ref& blocker, bool& has_shared) = 0; 
        virtual theory_var add_objective(app* term) = 0;
        bool is_linear(ast_manager& m, expr* term);
        bool is_numeral(arith_util& a, expr* term);
    };
}

#endif
