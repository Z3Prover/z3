/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    recfun_rewriter.h

Abstract:

    Rewriter recursive function applications to values

Author:

    Nikolaj Bjorner (nbjorner) 2020-04-26


--*/

#pragma once

#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/rewriter.h"

class recfun_rewriter {
    ast_manager& m;
    recfun::util  m_rec;
public:
    recfun_rewriter(ast_manager& m): m(m), m_rec(m) {}
    
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    family_id get_fid() const { return m_rec.get_family_id(); }

};

