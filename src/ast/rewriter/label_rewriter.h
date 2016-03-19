/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    label_rewriter.h

Abstract:

    Basic rewriting rules for labels.

Author:

    Nikolaj Bjorner (nbjorner) 2015-19-10

Notes:

--*/
#ifndef LABEL_REWRITER_H_
#define LABEL_REWRITER_H_

#include"ast.h"
#include"rewriter_types.h"


class label_rewriter : public default_rewriter_cfg {
    family_id m_label_fid;
    rewriter_tpl<label_rewriter> m_rwr;
public:    
    label_rewriter(ast_manager & m);
    ~label_rewriter();

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, 
                         proof_ref & result_pr);

    
    void remove_labels(expr_ref& fml, proof_ref& pr);
    
};

#endif
