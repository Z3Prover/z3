/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    solver_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-30.

Revision History:

--*/
#ifndef _SOLVER_PLUGIN_H_
#define _SOLVER_PLUGIN_H_

#include"ast.h"

/**
   \brief Abstract solver used during preprocessing step.
*/
class solver_plugin {
protected:
    ast_manager &   m_manager;
    family_id       m_fid;
public:
    solver_plugin(symbol const & fname, ast_manager & m):m_manager(m), m_fid(m.get_family_id(fname)) {}
    
    virtual ~solver_plugin() {}

    /**
       \brief Return true if it is possible to solve lhs = rhs. The
       arg. forbidden contains the set of variables that cannot be
       used. Store the result (var = subst) in var and subst.

       \remark Only simple solvers are supported. That is, the solution set has only one entry.
    */
    virtual bool solve(expr * lhs, expr * rhs, expr_mark const & forbidden, app_ref & var, expr_ref & subst) = 0;
    
    family_id get_family_id() const { return m_fid; }
   
    ast_manager & get_manager() { return m_manager; }
};

#endif /* _SOLVER_PLUGIN_H_ */

