/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_mev_array.h

Abstract:

    Utilities to evaluate arrays in the model.

Author:
   based on model_evaluator in muz/pdr/pdr_util.h

Revision History:

--*/
#pragma once

#include"ast/ast.h"
#include"ast/rewriter/rewriter_types.h"
#include"util/params.h"
#include"ast/array_decl_plugin.h"

/**
 * based on model_evaluator in muz/pdr/pdr_util.h
 */
class model_evaluator_array_util {
    ast_manager&    m;
    array_util      m_array;

    void eval_exprs(model& mdl, expr_ref_vector& es);

    bool extract_array_func_interp(model& mdl, expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case);

public:

    model_evaluator_array_util (ast_manager& m):
        m (m),
        m_array (m)
    {}

    /**
     * best effort evaluator of extensional array equality.
     */
    void eval_array_eq(model& mdl, app* e, expr* arg1, expr* arg2, expr_ref& res);

    void eval(model& mdl, expr* e, expr_ref& r, bool model_completion = true);
};

