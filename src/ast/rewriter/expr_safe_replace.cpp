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


void expr_safe_replace::insert(expr* src, expr* dst) {
    SASSERT(src->get_sort() == dst->get_sort());
    m_src.push_back(src);
    m_dst.push_back(dst);
    m_subst.insert(src, dst);
}

void expr_safe_replace::operator()(expr_ref_vector& es) {
    if (empty())
        return;
    expr_ref val(m);
    for (unsigned i = 0; i < es.size(); ++i) {
        (*this)(es.get(i), val);
        es[i] = val;
    }
}

void expr_safe_replace::cache_insert(expr* a, expr* b) {
    m_cache.emplace(a, b);
}

expr* expr_safe_replace::cache_find(expr* a) {
    auto I = m_cache.find(a);
    return I != m_cache.end() ? I->second : nullptr;
}


void expr_safe_replace::operator()(expr* e, expr_ref& res) {
    if (empty()) {
        res = e;
        return;
    }

    for (auto &[src,dst] : m_subst) {
        cache_insert(src, dst);
    }

    m_todo.push_back(e);
    expr* a, *b;
    
    while (!m_todo.empty()) {
        a = m_todo.back();
        if (cache_find(a)) {
            m_todo.pop_back();
        }
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
                    SASSERT(arg->get_sort() == d->get_sort());
                }
                else {
                    m_todo.push_back(arg);
                }
            }
            if (m_args.size() == n) {
                if (arg_differs) {
                    b = m.mk_app(c->get_decl(), m_args);
                    m_refs.push_back(b);
                    SASSERT(a->get_sort() == b->get_sort());
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
            m_refs.push_back(b);
            cache_insert(a, b);
            m_todo.pop_back();
        }        
    }
    res = cache_find(e);
    m_cache.clear();
    m_todo.reset();
    m_args.reset();
    m_refs.reset();    
}

void expr_safe_replace::reset() {
    m_src.reset();
    m_dst.reset();
    m_subst.reset();
    m_refs.finalize();
    m_cache.clear();
}

void expr_safe_replace::apply_substitution(expr* s, expr* def, expr_ref& t) {
    reset();
    insert(s, def);
    (*this)(t, t);
    reset();
}
