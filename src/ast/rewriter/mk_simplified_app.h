/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    mk_simplified_app.h

Abstract:

    Functor for creating new simplified applications

Author:

    Leonardo (leonardo) 2011-06-06

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"
#include "ast/rewriter/rewriter_types.h"

class mk_simplified_app {
    struct imp;
    imp * m_imp;
public:
    mk_simplified_app(ast_manager & m, params_ref const & p = params_ref());
    ~mk_simplified_app();

    br_status mk_core(func_decl * decl, unsigned num, expr * const * args, expr_ref & result);
    void operator()(func_decl * decl, unsigned num, expr * const * args, expr_ref & result);
};

