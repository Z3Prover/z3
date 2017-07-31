/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    datatype_rewriter.h

Abstract:

    Basic rewriting rules for Datatypes.

Author:

    Leonardo (leonardo) 2011-04-06

Notes:

--*/
#ifndef DATATYPE_REWRITER_H_
#define DATATYPE_REWRITER_H_

#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"

class datatype_rewriter {
    datatype_util    m_util;
public:    
    datatype_rewriter(ast_manager & m):m_util(m) {}
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    br_status mk_eq_core(expr * lhs, expr * rhs, expr_ref & result);
};

#endif
