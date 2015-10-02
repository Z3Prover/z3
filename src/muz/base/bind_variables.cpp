/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    bind_variables.cpp

Abstract:

    Utility to find constants that are declared as variables.

Author:

    Nikolaj Bjorner (nbjorner) 9-24-2014

Notes:
    

--*/

#include "bind_variables.h"

bind_variables::bind_variables(ast_manager & m):
    m(m),
    m_vars(m),
    m_pinned(m)
{}

bind_variables::~bind_variables() {
}
    
expr_ref bind_variables::operator()(expr* fml, bool is_forall) {
    if (m_vars.empty()) {
        return expr_ref(fml, m);
    }
    SASSERT(m_pinned.empty());
    expr_ref result = abstract(fml, m_cache, 0);
    if (!m_names.empty()) {
        m_bound.reverse();
        m_names.reverse();
        result = m.mk_quantifier(is_forall, m_bound.size(), m_bound.c_ptr(), m_names.c_ptr(), result);
    }
    m_pinned.reset();
    m_cache.reset();
    m_names.reset();
    m_bound.reset();
    for (var2bound::iterator it = m_var2bound.begin(); it != m_var2bound.end(); ++it) {
        it->m_value = 0;
    }
    return result;
}


expr_ref bind_variables::abstract(expr* term, cache_t& cache, unsigned scope) {
    unsigned sz = m_todo.size();
    m_todo.push_back(term);
    m_args.reset();
    expr* b, *arg;
    while (m_todo.size() > sz) {
        expr* e = m_todo.back();
        if (cache.contains(e)) {
            m_todo.pop_back();
            continue;
        }
        switch(e->get_kind()) {
        case AST_VAR: {
            SASSERT(to_var(e)->get_idx() < scope); 
            // mixing bound variables and free is possible for the caller, 
            // but not proper use.
            // So we assert here even though we don't check for it.
            cache.insert(e, e);
            m_todo.pop_back();
            break;
        }
        case AST_APP: {
            app* a = to_app(e);
            var2bound::obj_map_entry* w = m_var2bound.find_core(a);
            if (w) {
                var* v = w->get_data().m_value;
                if (!v) {
                    // allocate a bound index.
                    v = m.mk_var(m_names.size(), m.get_sort(a));
                    m_names.push_back(a->get_decl()->get_name());
                    m_bound.push_back(m.get_sort(a));
                    w->get_data().m_value = v;
                    m_pinned.push_back(v);
                }
                if (scope == 0) {
                    cache.insert(e, v);
                }
                else {
                    var* v1 = m.mk_var(scope + v->get_idx(), m.get_sort(v));
                    m_pinned.push_back(v1);
                    cache.insert(e, v1);
                }
                m_todo.pop_back();
                break;
            }
            bool all_visited = true;
            bool some_diff = false;
            m_args.reset();
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                arg = a->get_arg(i);                
                if (!cache.find(arg, b)) {
                    m_todo.push_back(arg);
                    all_visited = false;
                }
                else if (all_visited) {
                    m_args.push_back(b);
                    if (b != arg) {
                        some_diff = true;
                    }
                }
            }
            if (all_visited) {
                if (some_diff) {
                    b = m.mk_app(a->get_decl(), m_args.size(), m_args.c_ptr());
                    m_pinned.push_back(b);
                }
                else {
                    b = a;
                }
                cache.insert(e, b);
                m_todo.pop_back();
            }
            break;
        }
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(e);
            expr_ref_buffer patterns(m);
            expr_ref result1(m);
            unsigned new_scope = scope + q->get_num_decls();
            cache_t new_cache;
            for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
                patterns.push_back(abstract(q->get_pattern(i), new_cache, new_scope));
            }
            result1 = abstract(q->get_expr(), new_cache, new_scope);
            b = m.update_quantifier(q, patterns.size(), patterns.c_ptr(), result1.get());
            m_pinned.push_back(b);            
            cache.insert(e, b);
            m_todo.pop_back();            
            break;
        }
        default:
            UNREACHABLE();
        }
    }
    return expr_ref(cache.find(term), m);
}

void bind_variables::add_var(app* v) {
    m_vars.push_back(v);
    m_var2bound.insert(v, 0);
}
