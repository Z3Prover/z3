
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    distribute_forall.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"


class distribute_forall_simplifier : public dependent_expr_simplifier {

    struct rw_cfg;
    struct rw;
    
public:

    distribute_forall_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls) {
    }

    char const* name() const override { return "distribute-forall"; }
      
    bool supports_proofs() const override { return true; }

    void reduce() override;
};

