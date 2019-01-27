/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_qe_project.h

Abstract:

    Model-based projection

Author:

    Anvesh Komuravelli
    Arie Gurfinkel (arie)

Notes:

--*/
#ifndef SPACER_QE_PROJECT_H_
#define SPACER_QE_PROJECT_H_

#include "model/model.h"
#include "ast/expr_map.h"

namespace spacer_qe {
    /**
       Loos-Weispfenning model-based projection for a basic conjunction.
       Lits is a vector of literals.
       return vector of variables that could not be projected.
     */
    expr_ref arith_project(model& model, app_ref_vector& vars, expr_ref_vector const& lits);

    void arith_project(model& model, app_ref_vector& vars, expr_ref& fml);

    void arith_project(model& model, app_ref_vector& vars, expr_ref& fml, expr_map& map);

    void array_project_eqs (model& model, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars);

    void reduce_array_selects (model& mdl, app_ref_vector const& arr_vars, expr_ref& fml, bool reduce_all_selects = false);

    void reduce_array_selects (model& mdl, expr_ref& fml);

    void array_project_selects (model& model, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars);

    void array_project (model& model, app_ref_vector& arr_vars, expr_ref& fml, app_ref_vector& aux_vars, bool reduce_all_selects = false);
};

#endif
