/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    macro_replacer.h

Abstract:

    Abstract (functor) for applying macro replacement.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "util/obj_hashtable.h"


class macro_replacer {
    ast_manager& m;
    ast_ref_vector m_trail;
    expr_dependency_ref_vector m_deps;
    ptr_vector<expr> m_dep_exprs;
    obj_map<func_decl, std::tuple<app*, expr*, expr_dependency*>> m_map;
    struct macro_replacer_cfg;
    struct macro_replacer_rw;

public:

    macro_replacer(ast_manager& m): m(m), m_trail(m), m_deps(m) {}

    void insert(app* head, expr* def, expr_dependency* dep);
    void operator()(expr* t, expr_dependency* d, expr_ref& result, expr_dependency_ref& dep);
    void operator()(expr* t, expr_ref & result) { expr_dependency_ref dep(m); (*this)(t, nullptr, result, dep); }
    void operator()(expr_ref & t) { expr_ref s(t, m); (*this)(s, t); }

    bool has_macro(func_decl* f, app_ref& head, expr_ref& def, expr_dependency_ref& d);
};

