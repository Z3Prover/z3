/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    elim_term_ite.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-12.

Revision History:

--*/
#include "smt/elim_term_ite.h"
#include "ast/ast_smt2_pp.h"

br_status elim_term_ite_cfg::reduce_app(func_decl* f, unsigned n, expr * const* args, expr_ref& result, proof_ref& result_pr) {
    if (!m.is_term_ite(f)) {
        return BR_FAILED;
    }

    expr_ref   new_def(m);
    proof_ref  new_def_pr(m);
    app_ref   r(m.mk_app(f, n, args), m);
    app_ref    new_r(m);
    if (!m_defined_names.mk_name(r, new_def, new_def_pr, new_r, result_pr)) {
        return BR_FAILED;
    }
    result = new_r;
     
    CTRACE("elim_term_ite_bug", new_def.get() == 0, tout << mk_ismt2_pp(r, m) << "\n";);
    m_new_defs.push_back(justified_expr(m, new_def, new_def_pr));
    return BR_DONE;
}

