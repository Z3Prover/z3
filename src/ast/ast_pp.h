/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_pp.h

Abstract:

    Pretty printer

Author:

    Leonardo de Moura 2008-01-20.

Revision History:

    2012-11-17 - ast_smt2_pp is the official pretty printer in Z3

--*/
#ifndef AST_PP_H_
#define AST_PP_H_

#include"ast_smt2_pp.h"

struct mk_pp : public mk_ismt2_pp {
    mk_pp(ast * t, ast_manager & m, params_ref const & p, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = 0):
        mk_ismt2_pp(t, m, p, indent, num_vars, var_prefix) {
    }
    mk_pp(ast * t, ast_manager & m, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = 0):
        mk_ismt2_pp(t, m, indent, num_vars, var_prefix) {
    }
};

#endif

