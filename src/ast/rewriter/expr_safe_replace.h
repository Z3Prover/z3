/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    expr_safe_replace.h

Abstract:

    Version of expr_replace/expr_substitution that is safe for quantifiers.
    

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-30

Revision History:


--*/

#ifndef __EXPR_SAFE_REPLACE_H__
#define __EXPR_SAFE_REPLACE_H__

#include "ast.h"

class expr_safe_replace {
    ast_manager& m;
    expr_ref_vector m_src;
    expr_ref_vector m_dst;
    obj_map<expr, expr*> m_subst;

public:
    expr_safe_replace(ast_manager& m): m(m), m_src(m), m_dst(m) {}

    void insert(expr* src, expr* dst);

    void operator()(expr_ref& e) { (*this)(e.get(), e); }

    void operator()(expr* src, expr_ref& e);

    void apply_substitution(expr* s, expr* def, expr_ref& t);

    void reset();
};

#endif /* __EXPR_SAFE_REPLACE_H__ */
