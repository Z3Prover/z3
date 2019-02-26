/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    expr_delta.h

Abstract:

    Delta debugging support for specifications.
    A specification is a list of assumptions.
   
Author:

    Nikolaj Bjorner (nbjorner) 2008-21-06

Revision History:

--*/
#ifndef EXPR_DELTA_H_
#define EXPR_DELTA_H_

#include "ast/ast.h"

class expr_delta {
    ast_manager&    m_manager;
    expr_ref_vector m_exprs;
public:
    expr_delta(ast_manager& m);

    // Assert a constraint.
    void assert_cnstr(expr* e);
    
    //
    // Create the n'th delta in dfs mode.
    // return 'true' if a delta was obtained.
    //
    bool delta_dfs(unsigned n, expr_ref_vector& result);

private:

    // perform delta 
    bool delta_dfs(unsigned& n, expr* e, expr_ref& result);

    bool delta_dfs(unsigned& n, app* a, expr_ref& result);

    bool delta_dfs(unsigned& n, unsigned sz, expr* const* exprs, expr_ref_vector& result);
    
};


#endif
