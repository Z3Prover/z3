/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    func_decl_replace.cpp

Abstract:

    Replace functions in expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-28

Revision History:


--*/


#include "ast/rewriter/func_decl_replace.h"

expr_ref func_decl_replace::operator()(expr* e) {
    m_todo.push_back(e);
    
    while (!m_todo.empty()) {
        expr* a = m_todo.back(), *b;
        if (m_cache.contains(a)) {
            m_todo.pop_back();
        }
        else if (is_var(a)) {
            m_cache.insert(a, a);
            m_todo.pop_back();
        }
        else if (is_app(a)) {
            app* c = to_app(a);
            unsigned n = c->get_num_args();
            m_args.reset();            
            bool arg_differs = false;
            for (unsigned i = 0; i < n; ++i) {
                expr* d = nullptr, *arg = c->get_arg(i);
                if (m_cache.find(arg, d)) {
                    m_args.push_back(d);
                    arg_differs |= arg != d;
                    SASSERT(arg->get_sort() == d->get_sort());
                }
                else {
                    m_todo.push_back(arg);
                }
            }
            if (m_args.size() == n) {
                if (arg_differs) {
                    b = m.mk_app(c->get_decl(), m_args.size(), m_args.data());
                    m_refs.push_back(b);
                    SASSERT(a->get_sort() == b->get_sort());
                } else {
                    b = a;
                }
                func_decl* f = nullptr;
                if (m_subst.find(c->get_decl(), f)) {
                    b = m.mk_app(f, m_args.size(), m_args.data());
                    m_refs.push_back(b);
                }
                m_cache.insert(a, b);
                m_todo.pop_back();
            }
        }
        else {
            quantifier* q = to_quantifier(a);
            SASSERT(is_quantifier(a));
            expr* body = q->get_expr(), *new_body;
            if (m_cache.find(body, new_body)) {
                if (new_body == body) {
                    b = a;
                }
                else {
                    b = m.update_quantifier(q, new_body);
                    m_refs.push_back(b);
                }
                m_cache.insert(a, b);
                m_todo.pop_back();
            }
            else {
                m_todo.push_back(body);
            }
        }        
    }
    return expr_ref(m_cache.find(e), m);
}

void func_decl_replace::reset() {
    m_cache.reset();
    m_subst.reset();
    m_refs.reset();
    m_funs.reset();
}
