/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    reduce_args_simplifier.h

Abstract:

    Reduce the number of arguments in function applications.

--*/
#pragma once

dependent_expr_simplifier* mk_reduce_args_simplifier(ast_manager & m, dependent_expr_state& st, params_ref const & p);

