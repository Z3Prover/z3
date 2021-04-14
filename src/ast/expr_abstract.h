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
#pragma once

#include "ast/ast.h"

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
inline expr_ref expr_abstract(ast_manager& m, unsigned base, unsigned num_bound, expr* const* bound, expr* n) { expr_ref r(m); expr_abstract(m, base, num_bound, bound, n, r); return r; }
inline expr_ref expr_abstract(expr_ref_vector const& bound, expr* n) { return expr_abstract(bound.m(), 0, bound.size(), bound.data(), n); }
inline expr_ref expr_abstract(app_ref_vector const& bound, expr* n) { return expr_abstract(bound.m(), 0, bound.size(), (expr*const*)bound.data(), n); }
expr_ref mk_forall(ast_manager& m, unsigned num_bound, app* const* bound, expr* n);
expr_ref mk_exists(ast_manager& m, unsigned num_bound, app* const* bound, expr* n);
inline expr_ref mk_forall(ast_manager& m, app* b, expr* n) { return mk_forall(m, 1, &b, n); }
inline expr_ref mk_forall(ast_manager& m, expr* b, expr* n) { return mk_forall(m, to_app(b), n); }



