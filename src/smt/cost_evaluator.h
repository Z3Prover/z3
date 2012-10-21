/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cost_evaluator.h

Abstract:

    Simple evaluator for cost function

Author:

    Leonardo de Moura (leonardo) 2008-06-14.

Revision History:

--*/
#ifndef _COST_EVALUATOR_H_
#define _COST_EVALUATOR_H_

#include"ast.h"
#include"arith_decl_plugin.h"

class cost_evaluator {
    ast_manager &   m_manager;
    arith_util      m_util;
    unsigned        m_num_args;
    float const *   m_args;
    float eval(expr * f) const;
public:
    cost_evaluator(ast_manager & m);
    /**
       I'm using the same standard used in quantifier instantiation.
       (VAR 0) is stored in the last position of the array.
       ...
       (VAR (num_args - 1)) is stored in the first position of the array.
    */
    float operator()(expr * f, unsigned num_args, float const * args);
};

#endif /* _COST_EVALUATOR_H_ */

