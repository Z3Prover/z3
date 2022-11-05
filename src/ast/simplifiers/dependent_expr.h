/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    dependent_expr.h

Abstract:

    Container class for dependent expressions.
    They represent how assertions are tracked in goals.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/
#pragma once

#include "ast/ast.h"

class dependent_expr {
    ast_manager& m;
    expr*            m_fml;
    expr_dependency* m_dep;
public:
    dependent_expr(ast_manager& m, expr* fml, expr_dependency* d):
        m(m),
        m_fml(fml),
        m_dep(d) {
        SASSERT(fml);
        m.inc_ref(fml);
        m.inc_ref(d);
    }
    
    dependent_expr& operator=(dependent_expr const& other) {
        SASSERT(&m == &other.m);
        if (this != &other) {
            m.inc_ref(other.m_fml);
            m.inc_ref(other.m_dep);
            m.dec_ref(m_fml);
            m.dec_ref(m_dep);
            m_fml = other.m_fml;
            m_dep = other.m_dep;
        }
        return *this;
    }
    
    dependent_expr(dependent_expr const& other):
        m(other.m),
        m_fml(other.m_fml),
        m_dep(other.m_dep) {
        m.inc_ref(m_fml);
        m.inc_ref(m_dep);
    }

    dependent_expr(dependent_expr && other) noexcept :
        m(other.m),
        m_fml(nullptr),
        m_dep(nullptr) {
        std::swap(m_fml, other.m_fml);
        std::swap(m_dep, other.m_dep);
    }

    ~dependent_expr() {
        m.dec_ref(m_fml);
        m.dec_ref(m_dep);
        m_fml = nullptr;
        m_dep = nullptr;
    }

    ast_manager& get_manager() const { return m; }

    expr* fml() const { return m_fml; }

    expr_dependency* dep() const { return m_dep; }
    
    std::tuple<expr*, expr_dependency*> operator()() const { 
        return { m_fml, m_dep }; 
    }
};
