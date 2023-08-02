/*++

  Module Name:

    qel.h

Abstract:

    Light weight quantifier elimination (QEL) based on term graph.

    The implementation is based on the following paper:

    Isabel Garcia-Contreras, Hari Govind V. K., Sharon Shoham, Arie Gurfinkel:
    Fast Approximations of Quantifier Elimination. Computer-Aided Verification
    (CAV). 2023. URL: https://arxiv.org/abs/2306.10009

Author:

    Hari Govind V K (hgvk94)
    Isabel Garcia (igcontreras)

--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_util.h"
#include "util/params.h"
#include "util/uint_set.h"

class qel {
    class impl;
    impl *m_impl;
    
public:
    qel(ast_manager &m, params_ref const &p);

    ~qel();

    /**
       \brief Applies light-weight elimination of `vars` provided as vector
       of expressions to the cube `fml`. Returns the updated formula and updated
       set of variables that were not eliminated.
    */
    void operator()(app_ref_vector &vars, expr_ref &fml);
};
