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
#include "ast/ast_pp.h"
#include "ast/ast_translation.h"

class dependent_expr {
    ast_manager& m;
    expr*            m_fml;
    proof*           m_proof;
    expr_dependency* m_dep;
public:
    dependent_expr(ast_manager& m, expr* fml, proof* p, expr_dependency* d):
        m(m),
        m_fml(fml),
        m_proof(p),
        m_dep(d) {
        SASSERT(fml);
        m.inc_ref(fml);
        m.inc_ref(d);
        m.inc_ref(p);
    }

    dependent_expr(ast_translation& tr, dependent_expr const& src) :
        m(tr.to()) {
        m_fml = tr(src.fml());
        m.inc_ref(m_fml);
        m_proof = tr(src.pr());
        m.inc_ref(m_proof);
        expr_dependency_translation dtr(tr);
        m_dep = dtr(src.dep());
        m.inc_ref(m_dep);
    }
    
    dependent_expr& operator=(dependent_expr const& other) {
        SASSERT(&m == &other.m);
        if (this != &other) {
            m.inc_ref(other.m_fml);
            m.inc_ref(other.m_dep);
            m.inc_ref(other.m_proof);
            m.dec_ref(m_fml);
            m.dec_ref(m_dep);
            m.dec_ref(m_proof);
            m_fml = other.m_fml;
            m_dep = other.m_dep;
            m_proof = other.m_proof;
        }
        return *this;
    }
    
    dependent_expr(dependent_expr const& other):
        m(other.m),
        m_fml(other.m_fml),
        m_proof(other.m_proof),
        m_dep(other.m_dep) {
        m.inc_ref(m_fml);
        m.inc_ref(m_proof);
        m.inc_ref(m_dep);
    }

    dependent_expr(dependent_expr && other) noexcept :
        m(other.m),
        m_fml(nullptr),
        m_proof(nullptr),
        m_dep(nullptr) {
        std::swap(m_fml, other.m_fml);
        std::swap(m_proof, other.m_proof);
        std::swap(m_dep, other.m_dep);
    }

    ~dependent_expr() {
        m.dec_ref(m_fml);
        m.dec_ref(m_dep);
        m.dec_ref(m_proof);
        m_fml = nullptr;
        m_dep = nullptr;
        m_proof = nullptr;
    }

    ast_manager& get_manager() const { return m; }

    expr* fml() const { return m_fml; }

    expr_dependency* dep() const { return m_dep; }

    proof* pr() const { return m_proof; }
    
    std::tuple<expr*, proof*, expr_dependency*> operator()() const { 
        return { m_fml, m_proof, m_dep }; 
    }

    std::ostream& display(std::ostream& out) const {
        return out << mk_pp(m_fml, m);
        if (m_dep) {
            out << "\n <- ";
            ptr_vector<expr> deps;            
            m.linearize(m_dep, deps);
            for (expr* arg : deps)
                out << mk_pp(arg, m) << " ";
        }
        if (m_proof)
            out << "\n:- " << mk_pp(m_proof, m);
        return out;
    }
};

inline std::ostream& operator<<(std::ostream& out, dependent_expr const& d) {
    return d.display(out);
}
