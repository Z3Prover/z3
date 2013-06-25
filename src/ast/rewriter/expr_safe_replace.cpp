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

#include "expr_safe_replace.h"
#include "rewriter.h"


void expr_safe_replace::insert(expr* src, expr* dst) {
    m_src.push_back(src);
    m_dst.push_back(dst);
    m_subst.insert(src, dst);
}

void expr_safe_replace::operator()(expr* e, expr_ref& res) {
    obj_map<expr,expr*> cache;
    ptr_vector<expr> todo, args;
    expr_ref_vector refs(m);
    todo.push_back(e);
    expr* a, *b, *d;
    todo.push_back(e);
    
    while (!todo.empty()) {
        a = todo.back();
        if (cache.contains(a)) {
            todo.pop_back();
        }
        else if (m_subst.find(a, b)) {
            cache.insert(a, b);
            todo.pop_back();
        }
        else if (is_var(a)) {
            cache.insert(a, a);
            todo.pop_back();
        }
        else if (is_app(a)) {
            app* c = to_app(a);
            unsigned n = c->get_num_args();
            args.reset();
            for (unsigned i = 0; i < n; ++i) {
                if (cache.find(c->get_arg(i), d)) {
                    args.push_back(d);
                }
                else {
                    todo.push_back(c->get_arg(i));
                }
            }
            if (args.size() == n) {
                b = m.mk_app(c->get_decl(), args.size(), args.c_ptr());
                refs.push_back(b);
                cache.insert(a, b);
                todo.pop_back();
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
                shift(m_src[i].get(), num_decls, src);
                shift(m_dst[i].get(), num_decls, dst);
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
            refs.push_back(b);
            cache.insert(a, b);
            todo.pop_back();
        }        
    }
    res = cache.find(e);
}

void expr_safe_replace::reset() {
    m_src.reset();
    m_dst.reset();
    m_subst.reset();
}

void expr_safe_replace::apply_substitution(expr* s, expr* def, expr_ref& t) {
    reset();
    insert(s, def);
    (*this)(t, t);
    reset();
}
