/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_abstract.h

Abstract:

    Abstract occurrences of constants to bound variables.

Author:

    Nikolaj Bjorner (nbjorner) 2008-03-08

Notes:

--*/    

#include "ast/expr_abstract.h"
#include "util/map.h"
#include "ast/ast_pp.h"

void expr_abstractor::operator()(unsigned base, unsigned num_bound, expr* const* bound, expr* n, expr_ref& result) {
    
    if (num_bound == 0) {
        result = n;
        return;
    }
    expr * curr = nullptr, *b = nullptr;
    SASSERT(n->get_ref_count() > 0);

    m_stack.push_back(n);

    for (unsigned i = 0; i < num_bound; ++i) {
        b = bound[i];
        expr* v = m.mk_var(base + num_bound - i - 1, m.get_sort(b));
        m_pinned.push_back(v);
        m_map.insert(b, v);
    }

    while(!m_stack.empty()) {
        curr = m_stack.back();
        if (m_map.contains(curr)) {
            m_stack.pop_back();
            continue;
        }
        switch(curr->get_kind()) {
        case AST_VAR: {
            m_map.insert(curr, curr);
            m_stack.pop_back();
            break;
        }
        case AST_APP: {
            app* a = to_app(curr);
            bool all_visited = true;
            bool changed = false;
            m_args.reset();
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                if (!m_map.find(a->get_arg(i), b)) {
                    m_stack.push_back(a->get_arg(i));
                    all_visited = false;
                }
                else {
                    changed |= b != a->get_arg(i);
                    m_args.push_back(b);
                }
            }
            if (all_visited) {
                if (changed) {
                    b = m.mk_app(a->get_decl(), m_args.size(), m_args.c_ptr());
                    m_pinned.push_back(b);
                } else {
                    b = curr;
                }
                m_map.insert(curr, b);
                m_stack.pop_back();
            }
            break;
        }
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(curr);
            expr_ref_buffer patterns(m);
            expr_ref result1(m);
            unsigned new_base = base + q->get_num_decls();
        
            for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
                expr_abstract(m, new_base, num_bound, bound, q->get_pattern(i), result1);
                patterns.push_back(result1.get());
            }
            expr_abstract(m, new_base, num_bound, bound, q->get_expr(), result1);
            b = m.update_quantifier(q, patterns.size(), patterns.c_ptr(), result1.get());
            m_pinned.push_back(b);            
            m_map.insert(curr, b);
            m_stack.pop_back();            
            break;
        }
        default:
            UNREACHABLE();
        }
    }
    VERIFY (m_map.find(n, b));
    result = b;
    m_pinned.reset();
    m_map.reset();
    m_stack.reset();
    m_args.reset();   
}

void expr_abstract(ast_manager& m, unsigned base, unsigned num_bound, expr* const* bound, expr* n, expr_ref&  result) {
    expr_abstractor abs(m);
    abs(base, num_bound, bound, n, result);
    TRACE("expr_abstract",
          tout << expr_ref(n, m) << "\n";
          tout << result << "\n";);
}

expr_ref mk_quantifier(bool is_forall, ast_manager& m, unsigned num_bound, app* const* bound, expr* n) {
    expr_ref result(m);
    expr_abstract(m, 0, num_bound, (expr* const*)bound, n, result);    
    if (num_bound > 0) {
        ptr_vector<sort> sorts;
        svector<symbol> names;
        for (unsigned i = 0; i < num_bound; ++i) {
            sorts.push_back(m.get_sort(bound[i]));
            names.push_back(bound[i]->get_decl()->get_name());
        }
        result = m.mk_quantifier(is_forall, num_bound, sorts.c_ptr(), names.c_ptr(), result);
    }
    TRACE("expr_abstract",
          tout << expr_ref(n, m) << "\n";
          for (unsigned i = 0; i < num_bound; ++i) tout << expr_ref(bound[i], m) << " ";
          tout << "\n";
          tout << result << "\n";);
    return result;

}

expr_ref mk_forall(ast_manager& m, unsigned num_bound, app* const* bound, expr* n) {
    return mk_quantifier(true, m, num_bound, bound, n);
}

expr_ref mk_exists(ast_manager& m, unsigned num_bound, app* const* bound, expr* n) {
    return mk_quantifier(false, m, num_bound, bound, n);
}
