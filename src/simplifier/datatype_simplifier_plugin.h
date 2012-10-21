/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    datatype_simplifier_plugin.h

Abstract:

    Simplifier for algebraic datatypes.

Author:

    nbjorner 2008-11-6
    
--*/
#ifndef _DATATYPE_SIMPLIFIER_PLUGIN_H_
#define _DATATYPE_SIMPLIFIER_PLUGIN_H_

#include"basic_simplifier_plugin.h"
#include"datatype_decl_plugin.h"

/**
   \brief Simplifier for the arith family.
*/
class datatype_simplifier_plugin : public simplifier_plugin {
    datatype_util             m_util;
    basic_simplifier_plugin & m_bsimp;


public:
    datatype_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b);
    ~datatype_simplifier_plugin();
    

    virtual bool reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    virtual bool reduce_eq(expr * lhs, expr * rhs, expr_ref & result);

};

#endif /* _DATATYPE_SIMPLIFIER_PLUGIN_H_ */
