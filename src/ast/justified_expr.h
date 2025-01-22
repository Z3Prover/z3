
#pragma once

#include "ast/ast.h"

class justified_expr {
    ast_manager& m;
    expr*        m_fml;
    proof*       m_proof;
public:
    justified_expr(ast_manager& m, expr* fml, proof* p):
        m(m),
        m_fml(fml),
        m_proof(p) {
        SASSERT(fml);
        m.inc_ref(fml);
        m.inc_ref(p);
    }
    
    justified_expr& operator=(justified_expr const& other) {
        SASSERT(&m == &other.m);
        if (this != &other) {
            m.inc_ref(other.fml());
            m.inc_ref(other.pr());
            m.dec_ref(m_fml);
            m.dec_ref(m_proof);
            m_fml = other.fml();
            m_proof = other.pr();
        }
        return *this;
    }
    
    justified_expr(justified_expr const& other):
        m(other.m),
        m_fml(other.m_fml),
        m_proof(other.m_proof) {
        m.inc_ref(m_fml);
        m.inc_ref(m_proof);
    }

    justified_expr(justified_expr && other) noexcept :
        m(other.m),
        m_fml(nullptr),
        m_proof(nullptr) {
        std::swap(m_fml, other.m_fml);
        std::swap(m_proof, other.m_proof);
    }

    ~justified_expr() {
        m.dec_ref(m_fml);
        m.dec_ref(m_proof);
        m_fml = nullptr;
        m_proof = nullptr;
    }
    
    expr* fml() const { return m_fml; }

    proof* pr() const { return m_proof; }        
};
