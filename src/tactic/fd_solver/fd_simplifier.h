/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    fd_simplifier.h

Abstract:

    Finite-domain preprocessing simplifier.

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"

dependent_expr_simplifier* mk_fd_simplifier(
    ast_manager& m,
    params_ref const& p,
    dependent_expr_state& s);
