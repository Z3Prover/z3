/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    label_rewriter.cpp

Abstract:

    Basic rewriting rules for removing labels.

Author:

    Nikolaj Bjorner (nbjorner) 2015-19-10

Notes:

--*/

#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/label_rewriter.h"


label_rewriter::label_rewriter(ast_manager & m) : 
    m_label_fid(m.get_label_family_id()),
    m_rwr(m, false, *this) {}

label_rewriter::~label_rewriter() {}

br_status label_rewriter::reduce_app(
    func_decl * f, unsigned num, expr * const * args, expr_ref & result, 
    proof_ref & result_pr) {
    if (is_decl_of(f, m_label_fid, OP_LABEL)) {
        SASSERT(num == 1);
        result = args[0];
        return BR_DONE;
    }
    return BR_FAILED;
}

void label_rewriter::remove_labels(expr_ref& fml, proof_ref& pr) {
    ast_manager& m = fml.get_manager();
    expr_ref tmp(m);
    m_rwr(fml, tmp);
    if (pr && fml != tmp) {        
        pr = m.mk_modus_ponens(pr, m.mk_rewrite(fml, tmp));
    }
    fml = tmp;
}


//template class rewriter_tpl<label_rewriter>;
