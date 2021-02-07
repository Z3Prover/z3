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

#pragma once

#include "ast/ast.h"
#include <unordered_map>

class expr_safe_replace {
    ast_manager& m;
    expr_ref_vector m_src;
    expr_ref_vector m_dst;
    ptr_vector<expr> m_todo, m_args;
    expr_ref_vector m_refs;
    std::unordered_map<expr*,expr*> m_cache;

public:
    expr_safe_replace(ast_manager& m): m(m), m_src(m), m_dst(m), m_refs(m) {}

    void insert(expr* src, expr* dst);

    void operator()(expr_ref& e) { (*this)(e.get(), e); }

    void operator()(expr* src, expr_ref& e);

    void operator()(expr_ref_vector& es);

    void apply_substitution(expr* s, expr* def, expr_ref& t);

    void reset();

    bool empty() const { return m_src.empty(); }
};

