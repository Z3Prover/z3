/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    max_bv_sharing.h

Abstract:

    Rewriter for "maximing" the number of shared terms.
    The idea is to rewrite AC terms to maximize sharing.
    This rewriter is particularly useful for reducing
    the number of Adders and Multipliers before "bit-blasting".

Author:

    Leonardo de Moura (leonardo) 2011-12-29.

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"

dependent_expr_simplifier * mk_max_bv_sharing(ast_manager & m, params_ref const & p, dependent_expr_state& fmls);
