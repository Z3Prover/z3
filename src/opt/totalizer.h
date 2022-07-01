/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    totalizer.h

Abstract:
   
    Incremental totalizer for at least constraints

Author:

    Nikolaj Bjorner (nbjorner) 2022-06-27

--*/

#pragma once
#include "ast/ast.h"

namespace opt {
    
    class totalizer {
        struct node {
            node* m_left = nullptr;
            node* m_right = nullptr;
            expr_ref_vector m_literals;
            node(expr_ref_vector& l): m_literals(l) {}
            ~node() {
                dealloc(m_left);
                dealloc(m_right);
            }
            unsigned size() const { return m_literals.size(); }
            
        };

        ast_manager&            m;
        expr_ref_vector         m_literals;
        node*                   m_root = nullptr;
        expr_ref_vector         m_clauses;
        vector<std::pair<expr_ref, expr_ref>> m_defs;

        void ensure_bound(node* n, unsigned k);

    public:
        totalizer(expr_ref_vector const& literals);
        ~totalizer();
        expr* at_least(unsigned k);
        expr_ref_vector& clauses() { return m_clauses; }
        vector<std::pair<expr_ref, expr_ref>>& defs() { return m_defs; }
    };   
}
