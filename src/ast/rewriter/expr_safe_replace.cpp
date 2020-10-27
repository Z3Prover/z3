/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    expr_safe_replace.cpp

Abstract:

    Version of expr_replace/expr_substitution that is safe for quantifiers.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-30

Revision History:


--*/

#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_pp.h"

#define ALIVE_OPT 0


void expr_safe_replace::insert(expr* src, expr* dst) {
    SASSERT(m.get_sort(src) == m.get_sort(dst));
    m_src.push_back(src);
    m_dst.push_back(dst);
#if ALIVE_OPT
    cache_insert(src, dst);
#else
    m_subst.insert(src, dst);
#endif
}

void expr_safe_replace::operator()(expr_ref_vector& es) {
    expr_ref val(m);
    for (unsigned i = 0; i < es.size(); ++i) {
        (*this)(es.get(i), val);
        es[i] = val;
    }
}

void expr_safe_replace::cache_insert(expr* a, expr* b) {
#if ALIVE_OPT
    m_refs.reserve(a->get_id() + 1);
    m_refs[a->get_id()] = b;
#else
    m_cache.insert(a, b);
#endif
}

expr* expr_safe_replace::cache_find(expr* a) {
#if ALIVE_OPT
    return m_refs.get(a->get_id(), nullptr);
#else
    expr* b = nullptr;
    m_cache.find(a, b);
    return b;
#endif
}


void expr_safe_replace::operator()(expr* e, expr_ref& res) {
    m_todo.push_back(e);
    expr* a, *b;
    
    while (!m_todo.empty()) {
        a = m_todo.back();
        if (cache_find(a)) {
            m_todo.pop_back();
        }
#if !ALIVE_OPT
        else if (m_subst.find(a, b)) {
            cache_insert(a, b);
            m_todo.pop_back();            
        }
#endif
        else if (is_var(a)) {
            cache_insert(a, a);
            m_todo.pop_back();
        }
        else if (is_app(a)) {
            app* c = to_app(a);
            unsigned n = c->get_num_args();
            m_args.reset();
            bool arg_differs = false;
            for (expr* arg : *c) {
                expr* d = cache_find(arg);
                if (d) {
                    m_args.push_back(d);
                    arg_differs |= arg != d;
                    SASSERT(m.get_sort(arg) == m.get_sort(d));
                }
                else {
                    m_todo.push_back(arg);
                }
            }
            if (m_args.size() == n) {
                if (arg_differs) {
                    b = m.mk_app(c->get_decl(), m_args);
#if !ALIVE_OPT
                    m_refs.push_back(b);
#endif
                    SASSERT(m.get_sort(a) == m.get_sort(b));
                } else {
                    b = a;
                }
                cache_insert(a, b);
                m_todo.pop_back();
            }
        }
        else {
            SASSERT(is_quantifier(a));
            quantifier* q = to_quantifier(a);
            expr_safe_replace replace(m);
            var_shifter shift(m);
            expr_ref new_body(m), src(m), dst(m), tmp(m);
            expr_ref_vector pats(m), nopats(m);
            unsigned num_decls = q->get_num_decls();
            for (unsigned i = 0; i < m_src.size(); ++i) {
                shift(m_src.get(i), num_decls, src);
                shift(m_dst.get(i), num_decls, dst);
                replace.insert(src, dst);
            }
            unsigned np = q->get_num_patterns();
            for (unsigned i = 0; i < np; ++i) {
                replace(q->get_pattern(i), tmp);
                pats.push_back(tmp);
            }
            np = q->get_num_no_patterns();
            for (unsigned i = 0; i < np; ++i) {
                replace(q->get_no_pattern(i), tmp);
                nopats.push_back(tmp);
            }
            replace(q->get_expr(), new_body);
            b = m.update_quantifier(q, pats.size(), pats.c_ptr(), nopats.size(), nopats.c_ptr(), new_body);
#if !ALIVE_OPT
            m_refs.push_back(b);
#endif
            cache_insert(a, b);
            m_todo.pop_back();
        }        
    }
    res = cache_find(e);
    m_cache.reset();
    m_todo.reset();
    m_args.reset();
#if !ALIVE_OPT
    m_refs.reset();    
#endif
}

void expr_safe_replace::reset() {
    m_src.reset();
    m_dst.reset();
    m_subst.reset();
    m_refs.finalize();
    m_cache.reset();
}

void expr_safe_replace::apply_substitution(expr* s, expr* def, expr_ref& t) {
    reset();
    insert(s, def);
    (*this)(t, t);
    reset();
}
