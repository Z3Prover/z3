/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_abstract.h

Abstract:

    Abstract occurrences of constants to bound variables.

Author:

    Nikolaj Bjorner (nbjorner) 2008-03-08

Notes:

--*/
#ifndef _EXPR_ABSTRACT_H_
#define _EXPR_ABSTRACT_H_

#include"ast.h"

class expr_abstractor {
    ast_manager& m;
    expr_ref_vector m_pinned;
    ptr_vector<expr> m_stack, m_args;
    obj_map<expr, expr*> m_map;
    
public:
    expr_abstractor(ast_manager& m): m(m), m_pinned(m) {}
    void operator()(unsigned base, unsigned num_bound, expr* const* bound, expr* n, expr_ref& result);
};

void expr_abstract(ast_manager& m, unsigned base, unsigned num_bound, expr* const* bound, expr* n, expr_ref&  result);

#endif


