/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dl_rewriter.h

Abstract:

    Basic rewriting rules for atalog finite domains.

Author:

    Nikolaj Bjorner (nbjorner) 2012-03-09

Notes:

--*/
#ifndef _DL_REWRITER_H_
#define _DL_REWRITER_H_

#include"dl_decl_plugin.h"
#include"rewriter_types.h"

class dl_rewriter {
    datalog::dl_decl_util    m_util;
public:    
    dl_rewriter(ast_manager & m):m_util(m) {}
    family_id get_fid() const { return m_util.get_family_id(); }
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
};

#endif
