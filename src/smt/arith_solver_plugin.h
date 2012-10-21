/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_solver_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-30.

Revision History:

--*/
#ifndef _ARITH_SOLVER_PLUGIN_H_
#define _ARITH_SOLVER_PLUGIN_H_

#include"solver_plugin.h"
#include"arith_simplifier_plugin.h"

class arith_solver_plugin : public solver_plugin {
    arith_simplifier_plugin &  m_simplifier;
public:
    arith_solver_plugin(arith_simplifier_plugin & simp);
    virtual ~arith_solver_plugin() {}
    virtual bool solve(expr * lhs, expr * rhs, expr_mark const & forbidden, app_ref & var, expr_ref & subst);
};

#endif /* _ARITH_SOLVER_PLUGIN_H_ */

