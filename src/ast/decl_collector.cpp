/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_decl_collector.cpp

Abstract:

    Collect uninterpreted func_delcs and sorts.
    This class was originally in ast_smt_pp.h

Author:

    Leonardo (leonardo) 2011-10-04

Revision History:

--*/
#include"decl_collector.h"

void decl_collector::visit_sort(sort * n) {
    family_id fid = n->get_family_id();
    if (m().is_uninterp(n))
        m_sorts.push_back(n);
    if (fid == m_dt_fid)
        m_sorts.push_back(n);
}

bool decl_collector::is_bool(sort * s) {
    return m().is_bool(s);
}

void decl_collector::visit_func(func_decl * n) {
    family_id fid = n->get_family_id();
    if (fid == null_family_id) {
        if (m_sep_preds && is_bool(n->get_range()))
            m_preds.push_back(n);
        else
            m_decls.push_back(n);
    }        
}

decl_collector::decl_collector(ast_manager & m, bool preds):
    m_manager(m),
    m_sep_preds(preds) {
    m_basic_fid = m_manager.get_basic_family_id();
    m_dt_fid    = m_manager.mk_family_id("datatype");
}

void decl_collector::visit(ast* n) {
    ptr_vector<ast> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        n = todo.back();
        todo.pop_back();
        if (!m_visited.is_marked(n)) {
            m_visited.mark(n, true);                
            switch(n->get_kind()) {
            case AST_APP: {
                app * a = to_app(n);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    todo.push_back(a->get_arg(i));
                }
                todo.push_back(a->get_decl());
                break;
            }                    
            case AST_QUANTIFIER: {
                quantifier * q = to_quantifier(n);
                unsigned num_decls = q->get_num_decls();
                for (unsigned i = 0; i < num_decls; ++i) {
                    todo.push_back(q->get_decl_sort(i));
                }
                todo.push_back(q->get_expr());
                for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
                    todo.push_back(q->get_pattern(i));
                }
                break;
            }
            case AST_SORT: 
                visit_sort(to_sort(n));
                break;
            case AST_FUNC_DECL: {
                func_decl * d = to_func_decl(n);
                for (unsigned i = 0; i < d->get_arity(); ++i) {
                    todo.push_back(d->get_domain(i));
                }
                todo.push_back(d->get_range());
                visit_func(d);
                break;
            }
            case AST_VAR:
                break;
            default:
                UNREACHABLE();
            }
        }
    }
}



