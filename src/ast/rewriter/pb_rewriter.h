/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_rewriter.h

Abstract:

    Basic rewriting rules for PB constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2013-14-12

Notes:

--*/
#ifndef _PB_REWRITER_H_
#define _PB_REWRITER_H_

#include"pb_decl_plugin.h"
#include"rewriter_types.h"
#include"params.h"

/**
   \brief Cheap rewrite rules for PB constraints
*/
class pb_rewriter {
    pb_util       m_util;
public:    
    pb_rewriter(ast_manager & m, params_ref const & p = params_ref()):
        m_util(m) {
    }
    ast_manager & m() const { return m_util.get_manager(); }
    family_id get_fid() const { return m_util.get_family_id(); }

    void updt_params(params_ref const & p) {}
    static void get_param_descrs(param_descrs & r) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

};

#endif
