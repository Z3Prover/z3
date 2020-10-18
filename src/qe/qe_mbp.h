/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_mbp.h

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#pragma once

#include "ast/ast.h"
#include "util/params.h"
#include "model/model.h"
#include "math/simplex/model_based_opt.h"


namespace qe {

    class mbproj {
        class impl;
        impl * m_impl;
    public:
        mbproj(ast_manager& m, params_ref const& p = params_ref());

        ~mbproj();

        void updt_params(params_ref const& p);

        static void get_param_descrs(param_descrs & r);

        /**
           \brief
           Apply model-based qe on constants provided as vector of variables.
           Return the updated formula and updated set of variables that were not eliminated.
        */
        void operator()(bool force_elim, app_ref_vector& vars, model& mdl, expr_ref_vector& fmls);

        /**
           \brief
           Solve as many variables as possible using "cheap" quantifier elimination"
        */
        void solve(model& model, app_ref_vector& vars, expr_ref_vector& lits);

        /**
           \brief
           Maximize objective t under current model for constraints in fmls.
         */
        opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt);

        /**
           \brief
           Apply spacer friendly MBP.
           Use parameters to control behavior.
           - reduce_all_selects (false)
           - dont_sub (false)
        */
        void spacer(app_ref_vector& vars, model& mdl, expr_ref& fml);
    };
}

