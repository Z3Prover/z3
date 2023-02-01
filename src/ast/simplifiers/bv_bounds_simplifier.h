/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_bounds_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-27

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"

dependent_expr_simplifier * mk_bv_bounds_simplifier(ast_manager & m, params_ref const & p, dependent_expr_state& fmls);
