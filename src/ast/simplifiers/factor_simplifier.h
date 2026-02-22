/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    factor_simplifier.h

Abstract:

    Polynomial factorization simplifier.

Author:

    Leonardo de Moura (leonardo) 2012-02-03

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "util/params.h"

class factor_simplifier : public dependent_expr_simplifier {
    struct rw_cfg;
    struct rw;
    params_ref        m_params;
    scoped_ptr<rw>    m_rw;

public:
    factor_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s);

    char const* name() const override { return "factor"; }

    void updt_params(params_ref const& p) override;
    void collect_param_descrs(param_descrs& r) override;
    void reduce() override;
};

dependent_expr_simplifier* mk_factor_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s);
