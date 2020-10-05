/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cond_macro.h

Abstract:

    Class for maintaining conditional macros

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

Revision History:

--*/
#pragma once
#include "ast/ast_ll_pp.h"

class cond_macro {
protected:
    func_decl *           m_f;
    expr_ref              m_def;
    expr_ref              m_cond;
    bool                  m_ineq;
    bool                  m_satisfy_atom;
    bool                  m_hint;
    unsigned              m_weight;
public:
    cond_macro(ast_manager & m, func_decl * f, expr * def, expr * cond, bool ineq, bool satisfy_atom, bool hint, unsigned weight):
        m_f(f),
        m_def(def,m),
        m_cond(cond, m),
        m_ineq(ineq),
        m_satisfy_atom(satisfy_atom),
        m_hint(hint),
        m_weight(weight) {
        SASSERT(!m_hint || !m_cond);
    }
    
    ~cond_macro() {
    }
    
    func_decl * get_f() const { return m_f; }
    
    expr * get_def() const { return m_def; }
    
    expr * get_cond() const { return m_cond; }
    
    bool is_unconditional() const { return !m_cond || m_cond.m().is_true(m_cond); }
    
    bool satisfy_atom() const { return m_satisfy_atom; }
    
    bool is_hint() const { return m_hint; }
    
    bool is_equal(cond_macro const * other) const {
        return m_f == other->m_f && m_def == other->m_def && m_cond == other->m_cond;
    }
    
    std::ostream& display(std::ostream & out) const {
        out << "[" << m_f->get_name() << " -> " << mk_bounded_pp(m_def, m_def.m(), 6);
        if (m_hint)
            out << " *hint*";
        else
            out << " when " << mk_bounded_pp(m_cond, m_cond.m(), 6);
        return out << "] weight: " << m_weight;
    }
    
    unsigned get_weight() const { return m_weight; }
};
