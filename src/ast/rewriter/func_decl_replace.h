/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    func_decl_replace.h

Abstract:

    Replace functions in expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-28

Revision History:


--*/

#ifndef FUNC_DECL_REPLACE_H_
#define FUNC_DECL_REPLACE_H_

#include "ast/ast.h"

class func_decl_replace {
    ast_manager& m;
    obj_map<func_decl, func_decl*> m_subst;
    obj_map<expr, expr*> m_cache;
    ptr_vector<expr>     m_todo, m_args;
    expr_ref_vector      m_refs;
    func_decl_ref_vector m_funs;

public:
    func_decl_replace(ast_manager& m): m(m), m_refs(m), m_funs(m) {}

    void insert(func_decl* src, func_decl* dst) { m_subst.insert(src, dst); m_funs.push_back(src), m_funs.push_back(dst); }

    expr_ref operator()(expr* e);

    void reset();

    bool empty() const { return m_subst.empty(); }
};

#endif /* FUNC_DECL_REPLACE_H_ */
