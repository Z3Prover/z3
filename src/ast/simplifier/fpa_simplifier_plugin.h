/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    fpa_simplifier_plugin.h

Abstract:

    Simplifier for the floating-point theory

Author:

    Christoph (cwinter) 2015-01-14

--*/
#ifndef _FPA_SIMPLIFIER_PLUGIN_H_
#define _FPA_SIMPLIFIER_PLUGIN_H_

#include"basic_simplifier_plugin.h"
#include"fpa_decl_plugin.h"
#include"fpa_rewriter.h"

class fpa_simplifier_plugin : public simplifier_plugin {
    fpa_util     m_util;
    fpa_rewriter m_rw;

public:
    fpa_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b);
    ~fpa_simplifier_plugin();


    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);

};

#endif /* _FPA_SIMPLIFIER_PLUGIN_H_ */
