/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    seq_simplifier_plugin.h

Abstract:

    Simplifier for the sequence theory

Author:

    Nikolaj Bjorner (nbjorner) 2016-02-05

--*/
#ifndef SEQ_SIMPLIFIER_PLUGIN_H_
#define SEQ_SIMPLIFIER_PLUGIN_H_

#include"basic_simplifier_plugin.h"
#include"seq_decl_plugin.h"
#include"seq_rewriter.h"

class seq_simplifier_plugin : public simplifier_plugin {
    seq_util     m_util;
    seq_rewriter m_rw;

public:
    seq_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b);
    ~seq_simplifier_plugin();


    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);

};

#endif /* SEQ_SIMPLIFIER_PLUGIN_H_ */
